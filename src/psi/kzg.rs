// modified from https://github.com/eerkaijun/kzg-rust

use crate::{psi::poly::*, psi::subproduct_tree::*};
use ark_ec::{pairing::Pairing, VariableBaseMSM};
use ark_ff::Field;
use ark_poly::DenseUVPolynomial;
use ark_std::Zero;
use rayon::prelude::*;
use std::ops::Mul;

pub struct KZG<E: Pairing> {
    // generator G, a point
    pub g1: E::G1Affine,
    // generator H, a point
    pub g2: E::G2Affine,
    // sH
    pub g2_tau: E::G2,
    pub max_degree: usize,
    // commitment key for proof gen, [s^i]_1 = [G, s*G, s^2*G, ..., s^n*G]
    pub crs_g1: Vec<E::G1Affine>,
    // open key for verification, [s^i]_2 = [H, s*H, s^2*H, ..., s^n*H]
    pub crs_g2: Vec<E::G2Affine>,
}

impl<E: Pairing> KZG<E> {
    pub fn new(g1: E::G1Affine, g2: E::G2Affine, max_degree: usize) -> Self {
        Self {
            g1,
            g2,
            g2_tau: g2.mul(E::ScalarField::ZERO),
            max_degree,
            crs_g1: vec![],
            crs_g2: vec![],
        }
    }

    pub fn setup(&mut self, s: E::ScalarField) {
        let g1s: Vec<E::G1Affine> = (0..self.max_degree + 1)
            .into_par_iter()
            .map(|i| self.g1.mul(s.pow([i as u64])).into())
            .collect();
        let g2s: Vec<E::G2Affine> = (0..self.max_degree + 1)
            .into_par_iter()
            .map(|i| self.g2.mul(s.pow([i as u64])).into())
            .collect();
        self.crs_g1 = g1s;
        self.crs_g2 = g2s;
        self.g2_tau = self.g2.mul(s);
    }

    pub fn setup_single(&mut self, s: E::ScalarField) {
        for i in 0..self.max_degree + 1 {
            self.crs_g1.push(self.g1.mul(s.pow([i as u64])).into());
            self.crs_g2.push(self.g2.mul(s.pow([i as u64])).into());
        }
        self.g2_tau = self.g2.mul(s);
    }

    // standard way, slow
    pub fn commit(&self, poly: &Poly<E::ScalarField>) -> E::G1Affine {
        // commitment: c_0*G + c_1*s*G + c_2*s^2*G + ... + c_n*s^n*G
        E::G1::msm(&self.crs_g1, &poly.coeffs).unwrap().into()
    }

    // compute [\prod (s-x_j)]*G/[\prod_{i!=j} (x_i - x_j)]
    // note that here s should NOT be used for security, the polynomial \prod (x-x_j) should be calculated first and use self.crs_g1 to calculate the commitment value
    // this implementation is just for simplicity since it is a pre-compute function
    pub fn pre_compute_g1(&self, xs: &[E::ScalarField], s: E::ScalarField) -> Vec<E::G1Affine> {
        // denominator: \prod_{i!=j} (x_i-x_j)
        let size = xs.len();
        let mut denominators = vec![E::ScalarField::ONE; size];
        // numerator: (\prod (s-x_j))*G
        let mut numerators = vec![E::ScalarField::ONE; size];

        // for (i, x_i) in xs.iter().enumerate() {
        //     for (j, x_j) in xs.iter().enumerate() {
        //         if i != j {
        //             denominators[i] *= *x_i - x_j;
        //             numerators[i] *= s - x_j;
        //         }
        //     }
        // }

        denominators
            .par_iter_mut()
            .zip(numerators.par_iter_mut())
            .enumerate()
            .for_each(|(i, (deno_i, nume_i))| {
                xs.iter().enumerate().for_each(|(j, x_j)| {
                    if i != j {
                        *deno_i *= xs[i] - x_j;
                        *nume_i *= s - x_j;
                    }
                })
            });

        numerators
            .par_iter()
            .zip(denominators.par_iter())
            .map(|(a, b)| (self.g1 * *a * b.inverse().unwrap()).into())
            .collect()
    }

    // compute g1 commitment using pre-computed info: \sum y_i * info[i]
    pub fn commit_by_pre_info_g1(&self, ys: &[E::ScalarField], info: &Vec<E::G1Affine>) -> E::G1 {
        // println!("{}, {}", ys.len(), info.len());
        E::G1::msm(info, ys).unwrap()
    }

    // compute the g2 commitment for z_poly: (x-x_0)(x-x_1)...(x-x_{n-1})
    pub fn pre_compute_z_commitment(
        &self,
        xs: &[E::ScalarField],
        s: E::ScalarField,
    ) -> E::G2Affine {
        // let mut commitment_scalar = E::ScalarField::ONE;
        // for x in xs.iter() {
        //     commitment_scalar *= s - x;
        // }

        let commitment_scalar: E::ScalarField = xs
            .par_iter()
            .fold(|| E::ScalarField::ONE, |acc, &x| acc * (s - x))
            .sum();

        self.g2.mul(commitment_scalar).into()
    }

    // gen single proof for the given point x
    pub fn open_single(
        &self,
        poly: &Poly<E::ScalarField>,
        x: E::ScalarField,
    ) -> (E::ScalarField, E::G1Affine) {
        // evaluate poly at the x to get y value
        let y = eval(poly, x);

        // divisor: s - x: -x + s
        let divisor = Poly::from_coefficients_vec(vec![-x, E::ScalarField::ONE]);

        // numerator: P(s) - y
        let first = match poly.first() {
            Some(c) => *c - y,
            None => -y,
        }; // c0-y
        let rest = &poly[1..]; // [c1, ..., cn]
        let numerator_coeffs: Vec<E::ScalarField> =
            std::iter::once(first).chain(rest.iter().cloned()).collect(); // [c0-y, c1, ..., cn]
        let numerator_poly = Poly::from_coefficients_vec(numerator_coeffs);

        // cal quotient: (P(s)-y)/(s-x)
        let (quotient, _) = fft_div(&numerator_poly, &divisor);

        // cal pi as proof: quotient*G
        let mut pi = self.g1.mul(E::ScalarField::ZERO);

        // quotient is a polynomial: [c0, c1, ..., ck]
        // pi = G*c0 + s*G*c1 + s^2*G*c2 + ... + s^k*G*ck

        for (i, q) in quotient.iter().enumerate() {
            pi += self.crs_g1[i] * q;
        }

        (y, pi.into())
    }

    pub fn verify_single(
        &self,
        point: E::ScalarField,
        val: E::ScalarField,
        commitment: E::G1,
        pi: E::G1Affine,
    ) -> bool {
        // check e(pi, [s-x]_2) == e(C-[y]_1, H)
        // e(pi, s*H-x*H) == e(C-y*H, H)
        let lhs = E::pairing(pi, self.g2_tau - self.g2.mul(point));
        let rhs = E::pairing(commitment - self.g1.mul(val), self.g2);
        lhs == rhs
    }

    pub fn open_multi_with_subproduct_tree(
        &self,
        poly: &Poly<E::ScalarField>,
        xs: &[E::ScalarField],
        tree: &SubProductTree<E::ScalarField>,
    ) -> (Vec<E::ScalarField>, E::G1Affine) {
        // let timer1 = howlong::ProcessCPUTimer::new();
        let ys = multi_eval_with_subproduct_tree(poly, xs, tree);
        // let t = timer1.elapsed().real.as_micros() as u64;
        // println!("t1: {} ms", t / 1000);

        // let timer2 = howlong::ProcessCPUTimer::new();
        // fft interpolate (xs, ys) to get I(x)
        let poly_i = fft_interpolate_with_subproduct_tree(xs, &ys, tree);
        // let t = timer2.elapsed().real.as_micros() as u64;
        // println!("t2: {} ms", t / 1000);

        // numerator = P(x) - I(x)
        let numerator = poly - &poly_i;

        if numerator.is_zero() {
            // println!("### special case: numerator is zero");
            return (ys, E::G1::zero().into());
        }

        // let timer3 = howlong::ProcessCPUTimer::new();
        // compute q(x) = (P(x)-I(x))/Z(x)
        let (q, _) = fft_div(&numerator, &tree.product);
        // let t = timer3.elapsed().real.as_micros() as u64;
        // println!("t3: {} ms", t / 1000);

        // q is a polynomial: [c0, c1, ..., ck]
        // pi = G*c0 + s*G*c1 + s^2*G*c2 + ... + s^k*G*ck
        (ys, E::G1::msm_unchecked(&self.crs_g1, &q.coeffs).into())
    }

    pub fn open_multi(
        &self,
        poly: &Poly<E::ScalarField>,
        xs: &[E::ScalarField],
    ) -> (Vec<E::ScalarField>, E::G1Affine) {
        // compute sub-product tree, whose root node is Z(x) = \prod (x-x_i)
        let tree = SubProductTree::new_from_points_parallel(xs);
        let ys = multi_eval_with_subproduct_tree(poly, xs, &tree);
        // fft interpolate (xs, ys) to get I(x)
        let poly_i = fft_interpolate_with_subproduct_tree(xs, &ys, &tree);

        // numerator = P(x) - I(x)
        let numerator = poly - &poly_i;

        if numerator.is_zero() {
            // println!("### special case: numerator is zero");
            return (ys, E::G1::zero().into());
            // return (vec![], E::G1::zero().into());
        }
        // compute q(x) = (P(x)-I(x))/Z(x)
        let (q, _) = fft_div(&numerator, &tree.product);

        // q is a polynomial: [c0, c1, ..., ck]
        // pi = G*c0 + s*G*c1 + s^2*G*c2 + ... + s^k*G*ck

        (ys, E::G1::msm_unchecked(&self.crs_g1, &q.coeffs).into())
    }

    // standard way, slow
    pub fn verify_multi(
        &self,
        xs: &[E::ScalarField],
        ys: &[E::ScalarField],
        commitment: E::G1,
        pi: E::G1Affine,
    ) -> bool {
        let tree = SubProductTree::new_from_points_parallel(xs);

        // compute commitment of Z(x) in regards to crs_g2
        let z_commitment = E::G2::msm_unchecked(&self.crs_g2, &tree.product.coeffs).into();

        // compute lagrange polynomial
        let lagrange_poly = fft_interpolate_with_subproduct_tree(xs, ys, &tree);

        let lagrange_commitment = E::G1::msm_unchecked(&self.crs_g1, &lagrange_poly.coeffs).into();

        let lhs = E::pairing(pi, z_commitment);
        let rhs = E::pairing(commitment - lagrange_commitment, self.g2);
        lhs == rhs
    }

    pub fn fast_verify_multi(
        &self,
        ys: &[E::ScalarField],
        commitment: E::G1,
        pi: E::G1Affine,
        info_g1: &Vec<E::G1Affine>,
        z_commitment: E::G2Affine,
    ) -> bool {
        let lagrange_commitment = self.commit_by_pre_info_g1(ys, info_g1);

        let lhs = E::pairing(pi, z_commitment);
        let rhs = E::pairing(commitment - lagrange_commitment, self.g2);
        lhs == rhs
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils::{gen_unique_random_unsorted, get_fixed_rng, points_from_num};
    use ark_bls12_381::G1Projective as G3;
    use ark_bls12_381::{Bls12_381, Fr, G1Affine as G1, G2Affine as G2};
    use ark_ec::{pairing::Pairing, CurveGroup, Group};
    use ark_ff::UniformRand;

    #[test]
    fn test_group() {
        use ark_bls12_381::{Fr as ScalarField, G1Projective as G};
        use ark_ff::Field;
        use ark_std::{ops::Mul, UniformRand, Zero};

        let mut rng = ark_std::test_rng();
        let a = G::rand(&mut rng);
        let b = G::rand(&mut rng);

        let c = a + b;
        let d = a - b;
        assert_eq!(c + d, a.double());

        let e = -a;
        assert_eq!(e + a, G::zero());

        let scalar = ScalarField::rand(&mut rng);
        let e = c.mul(scalar);
        let f = e.mul(scalar.inverse().unwrap());
        assert_eq!(f, c);
    }

    #[test]
    fn test_pairing() {
        let mut rng = ark_std::test_rng();
        let a = G1::rand(&mut rng);
        let b = G2::rand(&mut rng);

        let e1 = Bls12_381::pairing(a, b);

        let ml_res = Bls12_381::miller_loop(a, b);
        let e2 = Bls12_381::final_exponentiation(ml_res).unwrap();

        assert_eq!(e1, e2);
    }

    #[test]
    fn test_kzg() {
        let mut rng = get_fixed_rng();
        // should be the max degree of poly
        let max_degree = 3;
        let mut kzg = KZG::<Bls12_381>::new(G1::rand(&mut rng), G2::rand(&mut rng), max_degree);
        // trust setup
        let s = Fr::rand(&mut rng);
        kzg.setup(s);

        // poly: 1+2x+3x^2+4x^3, attention: the degree should be consistent with degree
        let poly = Poly::from_coefficients_vec(points_from_num(vec![1, 2, 3, 4]));
        let commitment = kzg.commit(&poly);
        single_proof(&kzg, &poly, commitment);
        multi_proof(&kzg, &poly, commitment);
    }

    fn single_proof(kzg: &KZG<Bls12_381>, poly: &Poly<Fr>, commitment: G1) {
        // let mut rng = ark_std::test_rng();
        // let point = Fr::rand(&mut rng);
        let point = Fr::new(5u64.into());
        println!("point: {}", point);
        let (y, pi) = kzg.open_single(&poly, point);

        // verify proof
        let val = eval(&poly, point);
        assert_eq!(y, val);
        println!("val: {}", val);
        assert!(kzg.verify_single(point, val, commitment.into(), pi));

        println!("single verification passes!");
    }

    fn multi_proof(kzg: &KZG<Bls12_381>, poly: &Poly<Fr>, commitment: G1) {
        let mut rng = ark_std::test_rng();
        let points: Vec<Fr> = (0..4).map(|_| Fr::rand(&mut rng)).collect();
        let (ys, pi) = kzg.open_multi(poly, &points);

        // verify proof
        let vals = multi_eval(poly, &points);
        assert_eq!(ys, vals);
        assert!(kzg.verify_multi(&points, &vals, commitment.into(), pi));
        println!("multi verification passes!");
    }

    #[test]
    fn test_pre_compute_commit() {
        let mut rng = get_fixed_rng();
        // should be the max degree of poly
        let max_degree = 50;
        let mut kzg = KZG::<Bls12_381>::new(G1::rand(&mut rng), G2::rand(&mut rng), max_degree);
        // trust setup
        let s = Fr::rand(&mut rng);
        kzg.setup(s);

        let poly = Poly::from_coefficients_vec(points_from_num(gen_unique_random_unsorted::<u64>(
            max_degree + 1,
        )));
        let commitment1 = kzg.commit(&poly);

        // use ark_serialize::CanonicalSerialize;
        // let mut c_x_bytes: Vec<u8> = vec![];
        // commitment1.serialize_uncompressed(&mut c_x_bytes).unwrap();
        // println!("{}", c_x_bytes.len());

        let xs = points_from_num(gen_unique_random_unsorted::<u64>(max_degree + 1));
        let ys = multi_eval(&poly, &xs);

        let info = kzg.pre_compute_g1(&xs, s);
        let commitment2 = kzg.commit_by_pre_info_g1(&ys, &info);

        assert_eq!(commitment1, commitment2);
    }

    #[test]
    fn test_fast_kzg_multi_proof() {
        let mut rng = get_fixed_rng();
        let max_degree = 50;
        let mut kzg = KZG::<Bls12_381>::new(G1::rand(&mut rng), G2::rand(&mut rng), max_degree);
        let s = Fr::rand(&mut rng);
        kzg.setup(s);

        let poly = Poly::from_coefficients_vec(points_from_num(gen_unique_random_unsorted::<u64>(
            max_degree + 1,
        )));
        // just for verification
        let commitment = kzg.commit(&poly);
        let xs = points_from_num(gen_unique_random_unsorted::<u64>(max_degree + 1));
        let ys = multi_eval(&poly, &xs);
        // generate proof
        let (expected_ys, pi) = kzg.open_multi(&poly, &xs);
        assert_eq!(expected_ys, ys);

        // use ark_serialize::CanonicalSerialize;
        // let mut pi_bytes: Vec<u8> = vec![];
        // pi.serialize_uncompressed(&mut pi_bytes).unwrap();
        // println!("{}", pi_bytes.len());

        // off-line compute
        let info = kzg.pre_compute_g1(&xs, s);
        let z_commit = kzg.pre_compute_z_commitment(&xs, s);
        assert!(kzg.fast_verify_multi(&ys, commitment.into(), pi, &info, z_commit));
    }

    #[test]
    fn test_scalar_mul() {
        use ark_ec::scalar_mul::variable_base::VariableBaseMSM;

        let mut rng = get_fixed_rng();
        let max_degree = 50;
        let mut kzg = KZG::<Bls12_381>::new(G1::rand(&mut rng), G2::rand(&mut rng), max_degree);
        let s = Fr::rand(&mut rng);
        kzg.setup(s);

        let poly = Poly::from_coefficients_vec(points_from_num(gen_unique_random_unsorted::<u64>(
            max_degree + 1,
        )));

        let timer1 = howlong::ProcessCPUTimer::new();
        let commitment1 = kzg.commit(&poly);
        let t = timer1.elapsed().real.as_micros() as u64;
        println!("time1: {} ms", t / 1000);

        let timer2 = howlong::ProcessCPUTimer::new();
        let commitment2 = G3::msm(&kzg.crs_g1, &poly.coeffs).unwrap().into_affine();
        let t = timer2.elapsed().real.as_micros() as u64;
        println!("time2: {} ms", t / 1000);

        let timer3 = howlong::ProcessCPUTimer::new();
        let commitment3 = G3::msm_unchecked(&kzg.crs_g1, &poly.coeffs).into_affine();
        let t = timer3.elapsed().real.as_micros() as u64;
        println!("time3: {} ms", t / 1000);

        assert_eq!(commitment1, commitment2);
        assert_eq!(commitment2, commitment3);
    }

    #[test]
    fn test_scalar_mul_time() {
        use ark_bls12_381::Fr as ScalarField;
        use ark_bls12_381::{G1Affine, G1Projective};

        let mut rng = ark_std::test_rng();

        let mut a_s = vec![];
        let mut s_s = vec![];
        for _ in 0..1000 {
            a_s.push(G1Affine::rand(&mut rng));
            s_s.push(ScalarField::rand(&mut rng));
        }

        let timer1 = howlong::ProcessCPUTimer::new();

        let _ = G1Projective::msm(&a_s, &s_s).unwrap();
        let t = timer1.elapsed().real.as_micros() as u64;
        println!("time1: {} ms", t / 1000);

        let timer2 = howlong::ProcessCPUTimer::new();
        for i in 0..1000 {
            let _ = a_s[i].mul(&s_s[i]);
        }
        let t = timer2.elapsed().real.as_micros() as u64;
        println!("time2: {} ms", t / 1000);
    }

    #[test]
    fn test_nested_loop() {
        let n = 1000;
        let xs = points_from_num(gen_unique_random_unsorted::<u64>(n));
        let mut denominators = vec![Fr::ONE; n];
        let mut numerators = vec![Fr::ONE; n];
        let mut rng = get_fixed_rng();
        let s = Fr::rand(&mut rng);

        let timer1 = howlong::ProcessCPUTimer::new();
        for (i, x_i) in xs.iter().enumerate() {
            for (j, x_j) in xs.iter().enumerate() {
                if i != j {
                    denominators[i] *= *x_i - x_j;
                    numerators[i] *= s - x_j;
                }
            }
        }
        let t = timer1.elapsed().real.as_micros() as u64;
        println!("time2: {} ms", t / 1000);

        let mut denominators2 = vec![Fr::ONE; n];
        let mut numerators2 = vec![Fr::ONE; n];

        let timer2 = howlong::ProcessCPUTimer::new();
        denominators2
            .iter_mut()
            .zip(numerators2.iter_mut())
            .enumerate()
            .for_each(|(i, (a_i, b_i))| {
                xs.iter().enumerate().for_each(|(j, x_j)| {
                    if i != j {
                        *a_i *= xs[i] - x_j;
                        *b_i *= s - x_j;
                    }
                })
            });
        let t = timer2.elapsed().real.as_micros() as u64;
        println!("time3: {} ms", t / 1000);

        let mut denominators3 = vec![Fr::ONE; n];
        let mut numerators3 = vec![Fr::ONE; n];

        let timer3 = howlong::ProcessCPUTimer::new();
        denominators3
            .par_iter_mut()
            .zip(numerators3.par_iter_mut())
            .enumerate()
            .for_each(|(i, (a_i, b_i))| {
                xs.iter().enumerate().for_each(|(j, x_j)| {
                    if i != j {
                        *a_i *= xs[i] - x_j;
                        *b_i *= s - x_j;
                    }
                })
            });
        let t = timer3.elapsed().real.as_micros() as u64;
        println!("time1: {} ms", t / 1000);

        assert_eq!(denominators, denominators2);
        assert_eq!(numerators, numerators2);
        assert_eq!(denominators, denominators3);
        assert_eq!(numerators, numerators3);
    }
}
