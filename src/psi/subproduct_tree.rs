use ark_ff::PrimeField;
use ark_poly::DenseUVPolynomial;

use crate::psi::poly::{eval, fft_div, fft_mul, Poly};

#[derive(Clone)]
pub struct SubProductTree<S: PrimeField> {
    pub product: Poly<S>,
    pub left: Option<Box<SubProductTree<S>>>,
    pub right: Option<Box<SubProductTree<S>>>,
}

impl<S: PrimeField> SubProductTree<S> {
    pub fn new_from_points_single(xs: &[S]) -> Self {
        match xs.len() {
            1 => Self {
                // leaf node: (x - x_i)
                product: Poly::from_coefficients_vec(vec![-xs[0], S::one()]),
                left: None,
                right: None,
            },
            n => {
                let left = SubProductTree::new_from_points_single(&xs[..n / 2]);
                let right = SubProductTree::new_from_points_single(&xs[n / 2..]);
                SubProductTree {
                    product: fft_mul(&left.product, &right.product),
                    left: Some(Box::new(left)),
                    right: Some(Box::new(right)),
                }
            }
        }
    }

    pub fn new_from_points_parallel(xs: &[S]) -> Self {
        match xs.len() {
            1 => Self {
                // leaf node: (x - x_i)
                product: Poly::from_coefficients_vec(vec![-xs[0], S::one()]),
                left: None,
                right: None,
            },
            n => {
                let (left, right) = rayon::join(
                    || SubProductTree::new_from_points_parallel(&xs[..n / 2]),
                    || SubProductTree::new_from_points_parallel(&xs[n / 2..]),
                );
                // let left = SubProductTree::new_from_points(&xs[..n / 2]);
                // let right = SubProductTree::new_from_points(&xs[n / 2..]);
                SubProductTree {
                    product: fft_mul(&left.product, &right.product),
                    left: Some(Box::new(left)),
                    right: Some(Box::new(right)),
                }
            }
        }
    }

    pub fn multi_eval_single(&self, xs: &[S], f: &Poly<S>) -> Vec<S> {
        match xs.len() {
            1 => {
                let y = eval(f, xs[0]);
                vec![y]
            }
            n => {
                let left = self.left.as_ref().unwrap();
                let right = self.right.as_ref().unwrap();

                let (_, r_l) = fft_div(f, &left.product);
                let (_, r_r) = fft_div(f, &right.product);

                let mut l_l = left.multi_eval_single(&xs[..n / 2], &r_l.unwrap());
                let l_r = right.multi_eval_single(&xs[n / 2..], &r_r.unwrap());
                l_l.extend(l_r);
                l_l
            }
        }
    }

    pub fn multi_eval_parallel(&self, xs: &[S], f: &Poly<S>) -> Vec<S> {
        match xs.len() {
            1 => {
                let y = eval(f, xs[0]);
                vec![y]
            }
            n => {
                let left = self.left.as_ref().unwrap();
                let right = self.right.as_ref().unwrap();

                let (_, r_l) = fft_div(f, &left.product);
                let (_, r_r) = fft_div(f, &right.product);

                let (mut l_l, l_r) = rayon::join(
                    || left.multi_eval_parallel(&xs[..n / 2], &r_l.unwrap()),
                    || right.multi_eval_parallel(&xs[n / 2..], &r_r.unwrap()),
                );
                l_l.extend(l_r);
                l_l
            }
        }
    }

    // last step of lagrange interpolation
    pub fn linear_mod_comb(&self, cs: &[S]) -> Poly<S> {
        match cs.len() {
            1 => Poly::from_coefficients_vec(vec![cs[0]]),
            n => {
                let left = self.left.as_ref().unwrap();
                let right = self.right.as_ref().unwrap();

                let l = left.linear_mod_comb(&cs[..n / 2]);
                let r = right.linear_mod_comb(&cs[n / 2..]);

                fft_mul(&right.product, &l) + fft_mul(&left.product, &r)
            }
        }
    }

    pub fn linear_mod_comb_parallel(&self, cs: &[S]) -> Poly<S> {
        match cs.len() {
            1 => Poly::from_coefficients_vec(vec![cs[0]]),
            n => {
                let left = self.left.as_ref().unwrap();
                let right = self.right.as_ref().unwrap();

                let (l, r) = rayon::join(
                    || left.linear_mod_comb_parallel(&cs[..n / 2]),
                    || right.linear_mod_comb_parallel(&cs[n / 2..]),
                );

                fft_mul(&right.product, &l) + fft_mul(&left.product, &r)
            }
        }
    }
}

mod tests {

    #[test]
    fn test_parallel() {
        use super::*;
        use crate::utils::*;

        let n = 10000;
        let xs = points_from_num(gen_unique_random_unsorted::<u64>(n));

        let timer1 = howlong::ProcessCPUTimer::new();
        let tree1 = SubProductTree::new_from_points_single(&xs);
        let t = timer1.elapsed().real.as_micros() as u64;
        println!("time single: {} ms", t / 1000);

        let timer2 = howlong::ProcessCPUTimer::new();
        let tree2 = SubProductTree::new_from_points_parallel(&xs);
        let t = timer2.elapsed().real.as_micros() as u64;
        println!("time multi: {} ms", t / 1000);

        assert_eq!(tree1.product, tree2.product);
    }
}
