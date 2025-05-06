use ark_ff::{FftField, Field, PrimeField};
use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial, Polynomial};
use ark_std::Zero;
use rayon::prelude::*;
use std::ops::Mul;

use crate::{psi::subproduct_tree::SubProductTree, ValType};

// coeffs: [c_0, c_1, ..., c_n]
// len(): n+1, degree(): n
pub type Poly<S> = DensePolynomial<S>;

pub fn eval<S: Field>(poly: &Poly<S>, x: S) -> S {
    poly.evaluate(&x)
}

// calculate the differentiation of a polynomial
pub fn derive<S: Field>(poly: &Poly<S>) -> Poly<S> {
    if poly.len() == 1 {
        return Poly::<S>::from_coefficients_vec(vec![]);
    }

    let derive_coeffs: Vec<S> = poly
        .coeffs
        .par_iter()
        .enumerate()
        .skip(1)
        .map(|(i, c)| *c * S::from(i as ValType))
        .collect();

    Poly::<S>::from_coefficients_vec(derive_coeffs)
}

// calculate the differentiation of a polynomial
pub fn derive_single<S: Field>(poly: &Poly<S>) -> Poly<S> {
    if poly.len() == 1 {
        return Poly::<S>::from_coefficients_vec(vec![]);
    }

    let derive_coeffs: Vec<S> = poly
        .coeffs
        .iter()
        .enumerate()
        .skip(1)
        .map(|(i, c)| *c * S::from(i as ValType))
        .collect();

    Poly::<S>::from_coefficients_vec(derive_coeffs)
}

// use FFT to compute polynomial multiplication in O(nlogn) time
pub(crate) fn fft_mul<S: FftField>(lhs: &Poly<S>, rhs: &Poly<S>) -> Poly<S> {
    lhs.mul(rhs)
}

// slow multiplication in O(n^2) time
pub(crate) fn simple_mul<S: FftField>(lhs: &Poly<S>, rhs: &Poly<S>) -> Poly<S> {
    let mut coeffs = vec![S::zero(); lhs.degree() + rhs.degree() + 1];
    for (i, &coeff1) in lhs.coeffs.iter().enumerate() {
        for (j, &coeff2) in rhs.coeffs.iter().enumerate() {
            coeffs[i + j] += coeff1 * coeff2;
        }
    }

    Poly::from_coefficients_vec(coeffs)
}

pub fn long_div<S: PrimeField>(poly: &Poly<S>, divisor: &Poly<S>) -> (Poly<S>, Option<Poly<S>>) {
    if divisor.is_zero() {
        panic!("divisor must not be zero!")
    } else if poly.is_zero() {
        (Poly::from_coefficients_vec(vec![]), None)
    } else if poly.degree() < divisor.degree() {
        (Poly::from_coefficients_vec(vec![]), Some(poly.clone()))
    } else {
        let mut remainder = poly.clone();
        let mut quotient_coeffs = vec![S::zero(); poly.degree() - divisor.degree() + 1];

        // divisor is guaranteed to be non-zero
        let lead_inv = divisor.last().unwrap().inverse().unwrap();

        while !remainder.is_zero() && remainder.degree() >= divisor.degree() {
            let cur_q_coeff = *remainder.last().unwrap() * lead_inv;
            let cur_q_degree = remainder.degree() - divisor.degree();
            quotient_coeffs[cur_q_degree] = cur_q_coeff;

            // simple way
            // for (i, &div_coeff) in divisor.coeffs.iter().enumerate() {
            //     remainder[cur_q_degree + i] -= &(cur_q_coeff * div_coeff);
            // }

            // by parallel iterator
            remainder
                .par_iter_mut()
                .skip(cur_q_degree)
                .zip(divisor.coeffs.par_iter())
                .for_each(|(r_coeff, div_coeff)| *r_coeff -= &(cur_q_coeff * div_coeff));

            while let Some(true) = remainder.coeffs.last().map(|c| c.is_zero()) {
                remainder.coeffs.pop();
            }
        }

        if remainder.is_zero() {
            (Poly::from_coefficients_vec(quotient_coeffs), None)
        } else {
            (
                Poly::from_coefficients_vec(quotient_coeffs),
                Some(remainder),
            )
        }
    }
}

// fast long division
pub fn fft_div<S: PrimeField>(poly: &Poly<S>, divisor: &Poly<S>) -> (Poly<S>, Option<Poly<S>>) {
    let m = poly.degree();
    let n = divisor.degree();

    // assert!(m >= n);
    if m < n {
        return (Poly::from_coefficients_vec(vec![]), Some(poly.clone()));
    }

    let mut a_rev = poly.clone();
    let mut b_rev = divisor.clone();

    a_rev.reverse();
    b_rev.reverse();

    let inv = invert(&b_rev, m - n);
    let q_rev = fft_mul(&a_rev, &inv);
    let mut q = truncate(&q_rev, m - n);
    q.reverse();

    let r = poly - &fft_mul(divisor, &q);
    if r.is_zero() {
        (q, None)
    } else {
        (q, Some(r))
    }
}

fn truncate<S: PrimeField>(poly: &Poly<S>, degree: usize) -> Poly<S> {
    let mut coeffs = poly.coeffs.clone();
    coeffs.truncate(degree + 1);
    Poly::from_coefficients_vec(coeffs)
}

// compute the first degree + 1 terms of the formal series 1/f(x)
fn invert<S: PrimeField>(poly: &Poly<S>, degree: usize) -> Poly<S> {
    assert!(!poly.is_empty());
    if degree == 0 {
        Poly::from_coefficients_vec(vec![poly.first().unwrap().inverse().unwrap()])
    } else {
        let q = invert(poly, degree / 2);

        let res = fft_mul(
            &q,
            &(&Poly::from_coefficients_vec(vec![S::from(2_u64)]) - &fft_mul(&q, poly)),
        );
        truncate(&res, degree)
    }
}

pub fn multi_eval<S: PrimeField>(poly: &Poly<S>, xs: &[S]) -> Vec<S> {
    // assert!(xs.len() > poly.degree());
    let tree = SubProductTree::new_from_points_parallel(xs);
    tree.multi_eval_parallel(xs, poly)
}

pub fn multi_eval_safe<S: PrimeField>(poly: &Poly<S>, xs: &[S]) -> Vec<S> {
    if xs.len() > poly.degree() + 1 {
        println!("=======longer eval found");
        let n = xs.len();
        let sub_xs: Vec<Vec<S>> = xs.chunks(n).map(|chunk| chunk.to_vec()).collect();
        let mut res = vec![];
        for xs in &sub_xs {
            res.extend(multi_eval(poly, xs));
        }
        res
    } else {
        multi_eval(poly, xs)
    }
}

// single thread, slow
pub fn multi_eval_single<S: PrimeField>(poly: &Poly<S>, xs: &[S]) -> Vec<S> {
    let tree = SubProductTree::new_from_points_parallel(xs);
    tree.multi_eval_single(xs, poly)
}

pub fn multi_eval_with_subproduct_tree_single<S: PrimeField>(
    poly: &Poly<S>,
    xs: &[S],
    tree: &SubProductTree<S>,
) -> Vec<S> {
    tree.multi_eval_single(xs, poly)
}

pub fn multi_eval_with_subproduct_tree<S: PrimeField>(
    poly: &Poly<S>,
    xs: &[S],
    tree: &SubProductTree<S>,
) -> Vec<S> {
    tree.multi_eval_parallel(xs, poly)
}

// note: if there exists 0 in ys, err will be thrown
// the correct way to do: for y_i=0, (x-x_i) must be the factor of the target poly, we firstly remove x_i and y_i from xs and ys, then do interpolation for degree -= 1 to compute poly. Finally we compute poly *= (x-x_i), assuming there is only one y_i=0
pub fn fft_interpolate<S: PrimeField>(xs: &[S], ys: &[S]) -> Poly<S> {
    assert_eq!(xs.len(), ys.len());

    match xs.len() {
        1 => {
            let coeffs = vec![ys[0] - xs[0], S::one()];
            Poly::from_coefficients_vec(coeffs)
        }
        _ => {
            let tree = SubProductTree::new_from_points_parallel(xs);
            let m_prim = derive(&tree.product);

            let cs: Vec<S> = multi_eval(&m_prim, xs)
                .par_iter()
                .enumerate()
                .map(|(i, c)| ys[i] * c.inverse().unwrap())
                .collect();
            tree.linear_mod_comb_parallel(cs.as_slice())
        }
    }
}

// if the product tree has been computed, can use it to directly do interpolation
pub fn fft_interpolate_with_subproduct_tree<S: PrimeField>(
    xs: &[S],
    ys: &[S],
    tree: &SubProductTree<S>,
) -> Poly<S> {
    assert_eq!(xs.len(), ys.len());

    match xs.len() {
        1 => {
            let coeffs = vec![ys[0] - xs[0], S::one()];
            Poly::from_coefficients_vec(coeffs)
        }
        _ => {
            let m_prim = derive(&tree.product);

            let cs: Vec<S> = multi_eval_with_subproduct_tree(&m_prim, xs, tree)
                .par_iter()
                .enumerate()
                .map(|(i, c)| ys[i] * c.inverse().unwrap())
                .collect();

            tree.linear_mod_comb_parallel(cs.as_slice())
        }
    }
}

// if the product tree has been computed, can use it to directly do interpolation
pub fn fft_interpolate_with_subproduct_tree_single<S: PrimeField>(
    xs: &[S],
    ys: &[S],
    tree: &SubProductTree<S>,
) -> Poly<S> {
    assert_eq!(xs.len(), ys.len());

    match xs.len() {
        1 => {
            let coeffs = vec![ys[0] - xs[0], S::one()];
            Poly::from_coefficients_vec(coeffs)
        }
        _ => {
            let m_prim = derive_single(&tree.product);

            let cs: Vec<S> = multi_eval_with_subproduct_tree_single(&m_prim, xs, tree)
                .iter()
                .enumerate()
                .map(|(i, c)| ys[i] * c.inverse().unwrap())
                .collect();

            tree.linear_mod_comb(cs.as_slice())
        }
    }
}

// O(n^2) interpolate
pub fn simple_lagrange_interpolate<S: PrimeField>(xs: &[S], ys: &[S]) -> Poly<S> {
    assert!(xs.len() == ys.len());
    let mut res = vec![S::zero(); xs.len()];

    for i in 0..xs.len() {
        let mut numerator = Poly::from_coefficients_vec(vec![S::one()]);
        let mut denominator = S::one();

        for j in 0..xs.len() {
            if i == j {
                continue;
            }

            numerator = simple_mul(
                &numerator,
                &Poly::from_coefficients_vec(vec![-xs[j], S::one()]),
            );
            denominator *= xs[i] - xs[j];
        }

        let term: Vec<S> = numerator.iter().map(|&x| x * ys[i] / denominator).collect();

        for i in 0..res.len() {
            res[i] += term[i];
        }
    }

    Poly::from_coefficients_vec(res)
}

#[allow(unused_imports)]
mod tests {

    use crate::psi::poly::{
        derive, eval, fft_div, fft_mul, long_div, multi_eval, simple_lagrange_interpolate,
        simple_mul, Poly,
    };
    use crate::utils::*;
    use ark_ff::Zero;
    use ark_poly::univariate::DensePolynomial;
    use ark_poly::{DenseUVPolynomial, EvaluationDomain, Evaluations, GeneralEvaluationDomain};

    use super::fft_interpolate;

    #[test]
    fn test_eval() {
        // f(x) = 1 + 2x + x^2 + 3x^3
        let poly = Poly::from_coefficients_vec(points_from_num(vec![1, 2, 1, 3]));
        assert_eq!(eval(&poly, 0.into()), 1.into());
        assert_eq!(eval(&poly, 1.into()), 7.into());
        assert_eq!(eval(&poly, 2.into()), 33.into());

        assert_eq!(
            multi_eval(
                &poly,
                &vec![0.into(), 1.into(), 2.into(), 2.into(), 3.into()]
            ),
            vec![1.into(), 7.into(), 33.into(), 33.into(), 97.into()]
        );
    }

    #[test]
    fn test_derive() {
        let poly = Poly::from_coefficients_vec(points_from_num(vec![1]));
        let poly_prime = derive(&poly);
        let target = Poly::from_coefficients_vec(points_from_num::<u64>(vec![]));
        assert_eq!(poly_prime, target);

        let poly = Poly::from_coefficients_vec(points_from_num(vec![1, 2, 1, 3]));
        let poly_prime = derive(&poly);
        let target = Poly::from_coefficients_vec(points_from_num(vec![2, 2, 9]));
        assert_eq!(poly_prime, target);
    }

    #[test]
    fn test_mul() {
        let poly1 = Poly::from_coefficients_vec(points_from_num(vec![2, 1, 1]));
        let poly2 = Poly::from_coefficients_vec(points_from_num(vec![1, 1]));
        let product1 = fft_mul(&poly1, &poly2);
        let product2 = simple_mul(&poly1, &poly2);
        let target = Poly::from_coefficients_vec(points_from_num(vec![2, 3, 2, 1]));
        assert_eq!(product1, target);
        assert_eq!(product1, product2);
    }

    #[test]
    fn test_long_div() {
        // x^4+2x^3+2x^2+5x+7 / x+2 = x^3+2x+1 r 5
        let poly1 = Poly::from_coefficients_vec(points_from_num(vec![7, 5, 2, 2, 1]));
        let divisor = Poly::from_coefficients_vec(points_from_num(vec![2, 1]));
        let (q, r) = long_div(&poly1, &divisor);
        assert_eq!(
            q,
            Poly::from_coefficients_vec(vec![1.into(), 2.into(), 0.into(), 1.into()])
        );
        assert_eq!(r, Some(Poly::from_coefficients_vec(vec![5.into()])));

        // x^3 + 6x^2 + 13x + 10 / x + 2 = x^2 + 4x + 5 r 0
        let poly1 = Poly::from_coefficients_vec(points_from_num(vec![10, 13, 6, 1]));
        let divisor = Poly::from_coefficients_vec(points_from_num(vec![2, 1]));
        let (q, r) = long_div(&poly1, &divisor);
        assert_eq!(
            q,
            Poly::from_coefficients_vec(vec![5.into(), 4.into(), 1.into()])
        );
        assert_eq!(r, None);
    }

    #[test]
    fn test_fft_div() {
        let poly1 = Poly::from_coefficients_vec(points_from_num(vec![2, 3, 1]));
        let divisor = Poly::from_coefficients_vec(points_from_num(vec![1, 1]));
        let (q, r) = fft_div(&poly1, &divisor);
        assert_eq!(q, Poly::from_coefficients_vec(vec![2.into(), 1.into()]));
        assert_eq!(r, None);

        // x^4+2x^3+2x^2+5x+7 / x+2 = x^3+2x+1 r 5
        let poly1 = Poly::from_coefficients_vec(points_from_num(vec![7, 5, 2, 2, 1]));
        let divisor = Poly::from_coefficients_vec(points_from_num(vec![2, 1]));
        let (q, r) = fft_div(&poly1, &divisor);
        assert_eq!(
            q,
            Poly::from_coefficients_vec(vec![1.into(), 2.into(), 0.into(), 1.into()])
        );
        assert_eq!(r, Some(Poly::from_coefficients_vec(vec![5.into()])));

        // x^3 + 6x^2 + 13x + 10 / x + 2 = x^2 + 4x + 5 r 0
        let poly1 = Poly::from_coefficients_vec(points_from_num(vec![10, 13, 6, 1]));
        let divisor = Poly::from_coefficients_vec(points_from_num(vec![2, 1]));
        let (q, r) = fft_div(&poly1, &divisor);
        assert_eq!(
            q,
            Poly::from_coefficients_vec(vec![5.into(), 4.into(), 1.into()])
        );
        assert_eq!(r, None);
    }

    #[test]
    fn test_interpolate() {
        // 1+x+x^2+x^3+x^4 => [1, 1, 1, 1, 1]
        let target = Poly::from_coefficients_vec(points_from_num(vec![1, 1, 1, 1, 1]));
        let xs = points_from_num(vec![0, 1, 2, 3, 4]);
        let ys = points_from_num(vec![1, 5, 31, 121, 341]);
        assert_eq!(fft_interpolate(&xs, &ys), target);
        assert_eq!(simple_lagrange_interpolate(&xs, &ys), target);

        // 1+x+x^2+x^3 => [1, 1, 1, 1]
        let target = Poly::from_coefficients_vec(points_from_num(vec![1, 1, 1, 1]));
        let xs = points_from_num(vec![1, 2, 3, 4]);
        let ys = points_from_num(vec![4, 15, 40, 85]);
        assert_eq!(fft_interpolate(&xs, &ys), target);
        assert_eq!(simple_lagrange_interpolate(&xs, &ys), target);
    }

    #[test]
    fn test_interpolate_correctness() {
        let n = 100;
        let xs = points_from_num(gen_unique_random_unsorted::<u64>(n));
        let ys = points_from_num(gen_unique_random_unsorted::<u64>(n));
        let f = fft_interpolate(&xs, &ys);
        let f2 = simple_lagrange_interpolate(&xs, &ys);
        assert_eq!(f, f2);
        let vals = multi_eval(&f, &xs);
        assert_eq!(ys, vals);
    }

    #[test]
    fn test_div_time() {
        let n = 10000;
        let poly =
            Poly::from_coefficients_vec(points_from_num(gen_unique_random_unsorted::<u64>(n)));

        let m = 5000;
        let poly2 =
            Poly::from_coefficients_vec(points_from_num(gen_unique_random_unsorted::<u64>(m)));

        let timer1 = howlong::ProcessCPUTimer::new();
        let res1 = long_div(&poly, &poly2);
        let t = timer1.elapsed().real.as_micros() as u64;
        println!("time1: {} ms", t / 1000);

        let timer2 = howlong::ProcessCPUTimer::new();
        let res2 = fft_div(&poly, &poly2);
        let t = timer2.elapsed().real.as_micros() as u64;
        println!("time2: {} ms", t / 1000);

        assert_eq!(res1, res2);
    }

    #[test]
    fn test_iter() {
        let skip_len = 5;
        let a = vec![1, 2, 3, 4, 5, 6, 7, 8];
        let b = vec![1, 1, 1];
        let c: Vec<i32> = a
            .iter()
            .skip(skip_len)
            .zip(b.iter())
            .map(|(a_val, b_val)| a_val + b_val)
            .collect();
        assert_eq!(c, vec![7, 8, 9]);

        let mut a = vec![1, 2, 3, 4, 5, 6, 7, 8];
        let b = vec![1, 1, 1];
        a.iter_mut()
            .skip(skip_len)
            .zip(b.iter())
            .for_each(|(a_val, b_val)| *a_val += b_val);
        assert_eq!(a, vec![1, 2, 3, 4, 5, 7, 8, 9]);
    }
}
