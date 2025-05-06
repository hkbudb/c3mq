use crate::{tpch::Stream, utils::*};
// use fancy_garbling::{
//     twopac::semihonest::{Evaluator, Garbler},
//     util, BinaryBundle, BinaryGadgets, Fancy, FancyArithmetic, FancyBinary, FancyInput,
//     FancyReveal,
// };
use fancy_garbling::WireMod2;
use ocelot::{ot::AlszReceiver as OtReceiver, ot::AlszSender as OtSender};
use scuttlebutt::{AbstractChannel, AesRng, Channel, TrackChannel};
use std::{
    fmt::Debug,
    io::{BufReader, BufWriter},
};
use crate::garbled_circuit::my_fancy_garbling::{gb::Garbler, ev::Evaluator, traits::*};

use super::my_fancy_garbling::util;


#[derive(Clone, Copy)]
pub enum AggType {
    Add,
    Or,
}

struct AggInputs<F> {
    ind: Vec<BinaryBundle<F>>,
    anno1: Vec<BinaryBundle<F>>,
    anno2: Vec<BinaryBundle<F>>,
    out_share1: Vec<BinaryBundle<F>>,
}

struct SmallAggInputs<F> {
    ind: Vec<BinaryBundle<F>>,
    anno1: Vec<BinaryBundle<F>>,
    anno2: Vec<BinaryBundle<F>>,
    z0_share1: BinaryBundle<F>,
    z0_share2: BinaryBundle<F>,
    z_n_plus_1_share1: BinaryBundle<F>,
    z_n_plus_1_share2: BinaryBundle<F>,
    next_z0_share1: BinaryBundle<F>,
    out_share1: Vec<BinaryBundle<F>>,
}

pub fn gb_agg<C>(
    rng: &mut AesRng,
    channel: &mut C,
    ind: &Vec<u128>,
    anno1: &Vec<u128>,
    tp: AggType,
    out_share1: &Vec<u128>,
) where
    C: AbstractChannel + std::clone::Clone,
{
    let mut gb =
        Garbler::<C, AesRng, OtSender, WireMod2>::new(channel.clone(), rng.clone()).unwrap();
    let circuit_wires = gb_set_agg_inputs(&mut gb, ind, anno1, out_share1);

    match tp {
        AggType::Add => {
            let add_agg =
                fancy_add_agg::<Garbler<C, AesRng, OtSender, WireMod2>>(&mut gb, circuit_wires)
                    .unwrap();
            for agg in add_agg {
                gb.outputs(agg.wires()).unwrap();
            }
        }
        AggType::Or => {
            let or_agg =
                fancy_or_agg::<Garbler<C, AesRng, OtSender, WireMod2>>(&mut gb, circuit_wires)
                    .unwrap();
            for agg in or_agg {
                gb.outputs(agg.wires()).unwrap();
            }
        }
    }
}

pub fn gb_agg_small<C>(
    rng: &mut AesRng,
    channel: &mut C,
    ind: &Vec<u128>,
    anno1: &Vec<u128>,
    z0_share1: u128,
    z_n_plus_1_share1: u128,
    next_z0_share1: u128,
    tp: AggType,
    out_share1: &Vec<u128>,
) where
    C: AbstractChannel + std::clone::Clone,
{
    let mut gb =
        Garbler::<C, AesRng, OtSender, WireMod2>::new(channel.clone(), rng.clone()).unwrap();
    let circuit_wires = gb_set_agg_small_inputs(
        &mut gb,
        ind,
        anno1,
        z0_share1,
        z_n_plus_1_share1,
        next_z0_share1,
        out_share1,
    );

    match tp {
        AggType::Add => {
            let (add_agg, next_z0_share2) = fancy_add_agg_small::<
                Garbler<C, AesRng, OtSender, WireMod2>,
            >(&mut gb, circuit_wires)
            .unwrap();
            for agg in add_agg {
                gb.outputs(agg.wires()).unwrap();
            }
            gb.outputs(next_z0_share2.wires()).unwrap();
        }
        AggType::Or => {
            let (or_agg, next_z0_share2) =
                fancy_or_agg_small::<Garbler<C, AesRng, OtSender, WireMod2>>(&mut gb, circuit_wires)
                    .unwrap();
            for agg in or_agg {
                gb.outputs(agg.wires()).unwrap();
            }
            gb.outputs(next_z0_share2.wires()).unwrap();
        }
    }
}

fn gb_set_agg_inputs<F, E>(
    gb: &mut F,
    ind: &Vec<u128>,
    anno1: &Vec<u128>,
    out_share1: &Vec<u128>,
) -> AggInputs<F::Item>
where
    F: FancyInput<Item = WireMod2, Error = E>,
    E: Debug,
{
    let nbits = 128;
    let anno_size = anno1.len();
    let ind: Vec<BinaryBundle<F::Item>> = gb.bin_encode_many(ind, nbits).unwrap();
    let anno1: Vec<BinaryBundle<F::Item>> = gb.bin_encode_many(anno1, nbits).unwrap();
    let out_share1: Vec<BinaryBundle<F::Item>> = gb.bin_encode_many(out_share1, nbits).unwrap();
    let anno2: Vec<BinaryBundle<F::Item>> = gb.bin_receive_many(anno_size, nbits).unwrap();

    AggInputs {
        ind,
        anno1,
        anno2,
        out_share1,
    }
}

fn gb_set_agg_small_inputs<F, E>(
    gb: &mut F,
    ind: &Vec<u128>,
    anno1: &Vec<u128>,
    z0_share1: u128,
    z_n_plus_1_share1: u128,
    next_z0_share1: u128,
    out_share1: &Vec<u128>,
) -> SmallAggInputs<F::Item>
where
    F: FancyInput<Item = WireMod2, Error = E>,
    E: Debug,
{
    let nbits = 128;
    let anno_size = anno1.len();
    let ind: Vec<BinaryBundle<F::Item>> = gb.bin_encode_many(ind, nbits).unwrap();
    let anno1: Vec<BinaryBundle<F::Item>> = gb.bin_encode_many(anno1, nbits).unwrap();
    let out_share1: Vec<BinaryBundle<F::Item>> = gb.bin_encode_many(out_share1, nbits).unwrap();
    let z0_share1: BinaryBundle<F::Item> = gb.bin_encode(z0_share1, nbits).unwrap();
    let z_n_plus_1_share1: BinaryBundle<F::Item> = gb.bin_encode(z_n_plus_1_share1, nbits).unwrap();
    let next_z0_share1: BinaryBundle<F::Item> = gb.bin_encode(next_z0_share1, nbits).unwrap();

    let anno2: Vec<BinaryBundle<F::Item>> = gb.bin_receive_many(anno_size, nbits).unwrap();
    let z0_share2: BinaryBundle<F::Item> = gb.bin_receive(nbits).unwrap();
    let z_n_plus_1_share2: BinaryBundle<F::Item> = gb.bin_receive(nbits).unwrap();

    SmallAggInputs {
        ind,
        anno1,
        anno2,
        z0_share1,
        z0_share2,
        z_n_plus_1_share1,
        z_n_plus_1_share2,
        next_z0_share1,
        out_share1,
    }
}

pub fn ev_agg<C>(rng: &mut AesRng, channel: &mut C, anno2: &Vec<u128>, tp: AggType) -> Vec<u128>
where
    C: AbstractChannel + std::clone::Clone,
{
    let mut ev =
        Evaluator::<C, AesRng, OtReceiver, WireMod2>::new(channel.clone(), rng.clone()).unwrap();
    let circuit_wires = ev_set_agg_inputs(&mut ev, anno2);

    match tp {
        AggType::Add => {
            let add_agg =
                fancy_add_agg::<Evaluator<C, AesRng, OtReceiver, WireMod2>>(&mut ev, circuit_wires)
                    .unwrap();
            let mut res = vec![];
            for agg in add_agg {
                let val_bin = ev
                    .outputs(agg.wires())
                    .unwrap()
                    .expect("evaluator should produce outputs");
                res.push(util::u128_from_bits(&val_bin));
            }

            res
        }
        AggType::Or => {
            let or_agg =
                fancy_or_agg::<Evaluator<C, AesRng, OtReceiver, WireMod2>>(&mut ev, circuit_wires)
                    .unwrap();
            let mut res = vec![];
            for agg in or_agg {
                let val_bin = ev
                    .outputs(agg.wires())
                    .unwrap()
                    .expect("evaluator should produce outputs");
                res.push(util::u128_from_bits(&val_bin));
            }

            res
        }
    }
}

pub fn ev_agg_small<C>(
    rng: &mut AesRng,
    channel: &mut C,
    anno2: &Vec<u128>,
    z0_share2: u128,
    z_n_plus_1_share2: u128,
    tp: AggType,
    is_last: bool,
) -> (Vec<u128>, u128)
where
    C: AbstractChannel + std::clone::Clone,
{
    let mut ev =
        Evaluator::<C, AesRng, OtReceiver, WireMod2>::new(channel.clone(), rng.clone()).unwrap();
    let circuit_wires =
        ev_set_agg_small_inputs(&mut ev, anno2, z0_share2, z_n_plus_1_share2, is_last);
    match tp {
        AggType::Add => {
            let (add_agg, next_z0_share2) = fancy_add_agg_small::<
                Evaluator<C, AesRng, OtReceiver, WireMod2>,
            >(&mut ev, circuit_wires)
            .unwrap();
            let mut res = vec![];
            for agg in add_agg {
                let val_bin = ev
                    .outputs(agg.wires())
                    .unwrap()
                    .expect("evaluator should produce outputs");
                res.push(util::u128_from_bits(&val_bin));
            }
            let next_z0_share2 = util::u128_from_bits(
                &ev.outputs(next_z0_share2.wires())
                    .unwrap()
                    .expect("evaluator should produce outputs"),
            );

            (res, next_z0_share2)
        }
        AggType::Or => {
            let (or_agg, next_z0_share2) = fancy_or_agg_small::<
                Evaluator<C, AesRng, OtReceiver, WireMod2>,
            >(&mut ev, circuit_wires)
            .unwrap();
            let mut res = vec![];
            for agg in or_agg {
                let val_bin = ev
                    .outputs(agg.wires())
                    .unwrap()
                    .expect("evaluator should produce outputs");
                res.push(util::u128_from_bits(&val_bin));
            }
            let next_z0_share2 = util::u128_from_bits(
                &ev.outputs(next_z0_share2.wires())
                    .unwrap()
                    .expect("evaluator should produce outputs"),
            );
            (res, next_z0_share2)
        }
    }
}

fn ev_set_agg_inputs<F, E>(ev: &mut F, anno2: &Vec<u128>) -> AggInputs<F::Item>
where
    F: FancyInput<Item = WireMod2, Error = E>,
    E: Debug,
{
    let nbits = 128;
    let anno_size = anno2.len();
    let ind: Vec<BinaryBundle<F::Item>> = ev.bin_receive_many(anno_size - 1, nbits).unwrap();
    let anno1: Vec<BinaryBundle<F::Item>> = ev.bin_receive_many(anno_size, nbits).unwrap();
    let out_share1: Vec<BinaryBundle<F::Item>> = ev.bin_receive_many(anno_size, nbits).unwrap();
    let anno2: Vec<BinaryBundle<F::Item>> = ev.bin_encode_many(anno2, nbits).unwrap();

    AggInputs {
        ind,
        anno1,
        anno2,
        out_share1,
    }
}

fn ev_set_agg_small_inputs<F, E>(
    ev: &mut F,
    anno2: &Vec<u128>,
    z0_share2: u128,
    z_n_plus_1_share2: u128,
    is_last: bool,
) -> SmallAggInputs<F::Item>
where
    F: FancyInput<Item = WireMod2, Error = E>,
    E: Debug,
{
    let nbits = 128;
    let anno_size = anno2.len();
    let ind_size = if is_last { anno_size - 1 } else { anno_size };
    let ind: Vec<BinaryBundle<F::Item>> = ev.bin_receive_many(ind_size, nbits).unwrap();
    let anno1: Vec<BinaryBundle<F::Item>> = ev.bin_receive_many(anno_size, nbits).unwrap();
    let out_share1: Vec<BinaryBundle<F::Item>> = ev.bin_receive_many(anno_size, nbits).unwrap();
    let z0_share1: BinaryBundle<F::Item> = ev.bin_receive(nbits).unwrap();
    let z_n_plus_1_share1: BinaryBundle<F::Item> = ev.bin_receive(nbits).unwrap();
    let next_z0_share1: BinaryBundle<F::Item> = ev.bin_receive(nbits).unwrap();

    let anno2: Vec<BinaryBundle<F::Item>> = ev.bin_encode_many(anno2, nbits).unwrap();
    let z0_share2: BinaryBundle<F::Item> = ev.bin_encode(z0_share2, nbits).unwrap();
    let z_n_plus_1_share2: BinaryBundle<F::Item> = ev.bin_encode(z_n_plus_1_share2, nbits).unwrap();

    SmallAggInputs {
        ind,
        anno1,
        anno2,
        z0_share1,
        z0_share2,
        z_n_plus_1_share1,
        z_n_plus_1_share2,
        next_z0_share1,
        out_share1,
    }
}

// try to avoid multiplication, as it is very expensive
fn fancy_add_agg<F>(
    f: &mut F,
    wire_inputs: AggInputs<F::Item>,
) -> Result<Vec<BinaryBundle<F::Item>>, F::Error>
where
    F: FancyReveal + Fancy + BinaryGadgets + FancyBinary,
{
    let inds: Vec<BinaryBundle<_>> = wire_inputs.ind;
    let anno1: Vec<BinaryBundle<_>> = wire_inputs.anno1;
    let anno2: Vec<BinaryBundle<_>> = wire_inputs.anno2;
    let out_share1: Vec<BinaryBundle<_>> = wire_inputs.out_share1;

    let mut res = vec![];
    let mut z_i = f.bin_addition_no_carry(&anno1[0], &anno2[0])?;
    let len = inds.len();

    for (idx, ind) in inds.iter().enumerate() {
        let one = f.bin_constant_bundle(1, 128)?;
        let zero = f.bin_constant_bundle(0, 128)?;

        let check_eql = f.bin_eq_bundles(&ind, &zero)?;
        let z_i_prim = f.bin_multiplex(&check_eql, &zero, &z_i)?;

        let out_share2 = f.bin_subtraction(&z_i_prim, &out_share1[idx])?.0;
        res.push(out_share2);
        // TODO: here xor is simply add, so we just use +
        // attention: if you want to use multiplication, here should not use bin_mul as it will change moduli, instead, we should use bin_multiplication_lower_half()
        // However, multiplication is expensive, try to avoid using it

        let check_eql = f.bin_eq_bundles(&ind, &one)?;
        let mul = f.bin_multiplex(&check_eql, &zero, &z_i)?;

        let add = f.bin_addition_no_carry(&anno1[idx + 1], &anno2[idx + 1])?;

        let z_i_plus_1 = f.bin_addition_no_carry(&mul, &add)?;
        z_i = z_i_plus_1;
        if idx >= len - 1 {
            let out_share2 = f.bin_subtraction(&z_i, &out_share1[idx + 1])?.0;
            res.push(out_share2);
            break;
        }
    }

    Ok(res)
}

fn fancy_add_agg_small<F>(
    f: &mut F,
    wire_inputs: SmallAggInputs<F::Item>,
) -> Result<(Vec<BinaryBundle<F::Item>>, BinaryBundle<F::Item>), F::Error>
where
    F: FancyReveal + Fancy + BinaryGadgets + FancyBinary,
{
    let inds: Vec<BinaryBundle<_>> = wire_inputs.ind;
    let anno1: Vec<BinaryBundle<_>> = wire_inputs.anno1;
    let anno2: Vec<BinaryBundle<_>> = wire_inputs.anno2;
    let z0_share1: BinaryBundle<_> = wire_inputs.z0_share1;
    let z0_share2: BinaryBundle<_> = wire_inputs.z0_share2;
    let z_n_plus_1_share1: BinaryBundle<_> = wire_inputs.z_n_plus_1_share1;
    let z_n_plus_1_share2: BinaryBundle<_> = wire_inputs.z_n_plus_1_share2;
    let next_z0_share1: BinaryBundle<_> = wire_inputs.next_z0_share1;
    let out_share1: Vec<BinaryBundle<_>> = wire_inputs.out_share1;

    let mut res = vec![];
    let mut z_i = f.bin_addition_no_carry(&z0_share1, &z0_share2)?;
    let mut out_z_i = z_i.clone();

    let ind_len = inds.len();
    let anno_len = anno1.len();

    let one = f.bin_constant_bundle(1, 128)?;
    let zero = f.bin_constant_bundle(0, 128)?;

    for (idx, ind) in inds.iter().enumerate() {
        let check_eql = f.bin_eq_bundles(&ind, &zero)?;
        let z_i_prim = f.bin_multiplex(&check_eql, &zero, &z_i)?;

        let out_share2 = f.bin_subtraction(&z_i_prim, &out_share1[idx])?.0;
        res.push(out_share2);

        let check_eql = f.bin_eq_bundles(&ind, &one)?;
        let mul = f.bin_multiplex(&check_eql, &zero, &z_i)?;
        let add = f.bin_addition_no_carry(&anno1[idx + 1], &anno2[idx + 1])?;
        let z_i_plus_1 = f.bin_addition_no_carry(&mul, &add)?;
        z_i = z_i_plus_1;

        if idx >= ind_len - 2 {
            if ind_len != anno_len && idx >= ind_len - 1 {
                let out_share2 = f.bin_subtraction(&z_i, &out_share1[idx + 1])?.0;
                // res.push(z_i.clone());
                res.push(out_share2);
            } else if ind_len != anno_len && idx < ind_len - 1 {
                continue;
            } else {
                // last round
                let check_eql = f.bin_eq_bundles(&inds[idx + 1], &zero)?;
                let z_i_prim = f.bin_multiplex(&check_eql, &zero, &z_i)?;
                let out_share2 = f.bin_subtraction(&z_i_prim, &out_share1[idx + 1])?.0;
                // res.push(z_i_prim);
                res.push(out_share2);

                let check_eql = f.bin_eq_bundles(&inds[idx + 1], &one)?;
                let mul = f.bin_multiplex(&check_eql, &zero, &z_i)?;
                let add = f.bin_addition_no_carry(&z_n_plus_1_share1, &z_n_plus_1_share2)?;
                let z_i_plus_1 = f.bin_addition_no_carry(&mul, &add)?;
                out_z_i = z_i_plus_1;
            }
            break;
        }
    }
    // this subtraction is necessary
    out_z_i = f.bin_subtraction(&out_z_i, &next_z0_share1).unwrap().0;

    Ok((res, out_z_i))
}

fn fancy_or_agg<F>(
    f: &mut F,
    wire_inputs: AggInputs<F::Item>,
) -> Result<Vec<BinaryBundle<F::Item>>, F::Error>
where
    F: FancyReveal + Fancy + BinaryGadgets + FancyBinary,
{
    let inds: Vec<BinaryBundle<_>> = wire_inputs.ind;
    let anno1: Vec<BinaryBundle<_>> = wire_inputs.anno1;
    let anno2: Vec<BinaryBundle<_>> = wire_inputs.anno2;
    let out_share1: Vec<BinaryBundle<_>> = wire_inputs.out_share1;

    let mut res = vec![];
    let nbits = 128;

    let zero = f.bin_constant_bundle(0, nbits)?;
    let one = f.bin_constant_bundle(1, nbits)?;

    let sum = f.bin_addition_no_carry(&anno1[0], &anno2[0])?;
    // anno1[cnt] + anno2[cnt] == 0
    let check_eql = f.bin_eq_bundles(&sum, &zero)?;
    let mut z_i = f.bin_multiplex(&check_eql, &one, &zero)?;
    let len = inds.len();
    for (idx, ind) in inds.iter().enumerate() {
        let check_eql = f.bin_eq_bundles(&ind, &zero)?;
        let z_i_prim = f.bin_multiplex(&check_eql, &zero, &z_i)?;

        let out_share2 = f.bin_subtraction(&z_i_prim, &out_share1[idx])?.0;
        res.push(out_share2);

        let check_eql = f.bin_eq_bundles(&ind, &one)?;
        let mul = f.bin_multiplex(&check_eql, &zero, &z_i)?;

        // let mul = f.bin_multiplication_lower_half(&ind, &z_i)?;
        let sum = f.bin_addition_no_carry(&anno1[idx + 1], &anno2[idx + 1])?;
        // anno1[cnt] + anno2[cnt] == 0
        let check_eql = f.bin_eq_bundles(&sum, &zero)?;
        let bin_anno_sum = f.bin_multiplex(&check_eql, &one, &zero)?;
        let z_i_plus_1 = f.bin_or(&mul, &bin_anno_sum)?;
        z_i = z_i_plus_1;
        if idx >= len - 1 {
            let out_share2 = f.bin_subtraction(&z_i, &out_share1[idx + 1])?.0;
            res.push(out_share2);
            break;
        }
    }

    Ok(res)
}

fn fancy_or_agg_small<F>(
    f: &mut F,
    wire_inputs: SmallAggInputs<F::Item>,
) -> Result<(Vec<BinaryBundle<F::Item>>, BinaryBundle<F::Item>), F::Error>
where
    F: FancyReveal + Fancy + BinaryGadgets + FancyBinary,
{
    let inds: Vec<BinaryBundle<_>> = wire_inputs.ind;
    let anno1: Vec<BinaryBundle<_>> = wire_inputs.anno1;
    let anno2: Vec<BinaryBundle<_>> = wire_inputs.anno2;
    let z0_share1: BinaryBundle<_> = wire_inputs.z0_share1;
    let z0_share2: BinaryBundle<_> = wire_inputs.z0_share2;
    let z_n_plus_1_share1: BinaryBundle<_> = wire_inputs.z_n_plus_1_share1;
    let z_n_plus_1_share2: BinaryBundle<_> = wire_inputs.z_n_plus_1_share2;
    let next_z0_share1: BinaryBundle<_> = wire_inputs.next_z0_share1;
    let out_share1: Vec<BinaryBundle<_>> = wire_inputs.out_share1;

    let mut res = vec![];
    let zero = f.bin_constant_bundle(0, 128)?;
    let one = f.bin_constant_bundle(1, 128)?;

    let sum = f.bin_addition_no_carry(&z0_share1, &z0_share2)?;
    // anno1[cnt] + anno2[cnt] == 0
    let check_eql = f.bin_eq_bundles(&sum, &zero)?;
    let mut z_i = f.bin_multiplex(&check_eql, &one, &zero)?;
    let mut out_z_i = z_i.clone();

    let ind_len = inds.len();
    let anno_len = anno1.len();

    for (idx, ind) in inds.iter().enumerate() {
        let check_eql = f.bin_eq_bundles(&ind, &zero)?;
        let z_i_prim = f.bin_multiplex(&check_eql, &zero, &z_i)?;

        let out_share2 = f.bin_subtraction(&z_i_prim, &out_share1[idx])?.0;
        res.push(out_share2);

        let check_eql = f.bin_eq_bundles(&ind, &one)?;
        let mul = f.bin_multiplex(&check_eql, &zero, &z_i)?;
        let sum = f.bin_addition_no_carry(&anno1[idx + 1], &anno2[idx + 1])?;
        let check_eql = f.bin_eq_bundles(&sum, &zero)?;
        let bin_anno_sum = f.bin_multiplex(&check_eql, &one, &zero)?;
        let z_i_plus_1 = f.bin_or(&mul, &bin_anno_sum)?;
        z_i = z_i_plus_1;

        if idx >= ind_len - 2 {
            if ind_len != anno_len && idx >= ind_len - 1 {
                let out_share2 = f.bin_subtraction(&z_i, &out_share1[idx + 1])?.0;

                res.push(out_share2);
            } else if ind_len != anno_len && idx < ind_len - 1 {
                continue;
            } else {
                // last round
                let check_eql = f.bin_eq_bundles(&inds[idx + 1], &zero)?;
                let z_i_prim = f.bin_multiplex(&check_eql, &zero, &z_i)?;
                let out_share2 = f.bin_subtraction(&z_i_prim, &out_share1[idx + 1])?.0;
                res.push(out_share2);
                //==========
                let check_eql = f.bin_eq_bundles(&inds[idx + 1], &one)?;
                let mul = f.bin_multiplex(&check_eql, &zero, &z_i)?;
                let sum = f.bin_addition_no_carry(&z_n_plus_1_share1, &z_n_plus_1_share2)?;

                let check_eql = f.bin_eq_bundles(&sum, &zero)?;
                let bin_anno_sum = f.bin_multiplex(&check_eql, &one, &zero)?;
                let z_i_plus_1 = f.bin_or(&mul, &bin_anno_sum)?;

                out_z_i = z_i_plus_1;
            }
            break;
        }
    }

    // this subtraction is necessary
    out_z_i = f.bin_subtraction(&out_z_i, &next_z0_share1).unwrap().0;

    Ok((res, out_z_i))
}

// here xor means simply add
// add aggregate, assume sorted
// for each group, sum their anno together and set the last tuple's anno as the aggregated anno, while other tuples have 0-annotation
pub fn add_agg_in_clear(indicators: &Vec<u128>, anno1: &Vec<u128>, anno2: &Vec<u128>) -> Vec<u128> {
    let mut res = vec![];
    let mut z_i = anno1[0] + anno2[0];
    let len = indicators.len();
    for (idx, ind) in indicators.iter().enumerate() {
        let z_i_prim = (1 - ind) * z_i;
        res.push(z_i_prim);
        let z_i_plus_1 = (ind * z_i) + (anno1[idx + 1] + anno2[idx + 1]);
        z_i = z_i_plus_1;
        if idx >= len - 1 {
            res.push(z_i);
        }
    }

    res
}

pub fn add_agg_small_clear(
    indicators: &Vec<u128>,
    anno1: &Vec<u128>,
    anno2: &Vec<u128>,
    z0: u128,
    z_n_plus_1: u128,
) -> (Vec<u128>, u128) {
    let mut res = vec![];
    let mut z_i = z0;
    let mut out_z_i = z_i;
    let ind_len = indicators.len();
    let anno_len = anno1.len();
    for (idx, ind) in indicators.iter().enumerate() {
        let z_i_prim = (1 - ind) * z_i;
        res.push(z_i_prim);
        // TODO: here xor is simply add, so we just use +
        let z_i_plus_1 = (ind * z_i) + (anno1[idx + 1] + anno2[idx + 1]);
        z_i = z_i_plus_1;
        if idx >= ind_len - 2 {
            if ind_len != anno_len && idx >= ind_len - 1 {
                res.push(z_i);
            } else if ind_len != anno_len && idx < ind_len - 1 {
                continue;
            } else {
                // last round
                let z_i_prim = (1 - indicators[idx + 1]) * z_i;
                res.push(z_i_prim);
                let z_i_plus_1 = indicators[idx + 1] * z_i + z_n_plus_1;
                // z_i = z_i_plus_1; out_z_i = z_i;
                out_z_i = z_i_plus_1;
            }
            break;
        }
    }
    (res, out_z_i)
}

// or aggregate, assume sorted
// for each group, as long as there is one tuple whose anno != 0, set the last tuple's anno as 1 and other tuples' as 0
// if all tuples in a group have anno = 0, just do nothing (all tuples are dummy)
pub fn or_agg_in_clear(indicators: &Vec<u128>, anno1: &Vec<u128>, anno2: &Vec<u128>) -> Vec<u128> {
    let mut res = vec![];
    // let mut z_i = if anno1[cnt] + anno2[cnt] != 0 { 1 } else { 0 };

    let mut z_i = if anno1[0] + anno2[0] == 0 { 0 } else { 1 };
    let len = indicators.len();
    for (idx, ind) in indicators.iter().enumerate() {
        let z_i_prim = (1 - ind) * z_i;
        res.push(z_i_prim);
        let anno_sum = if anno1[idx + 1] + anno2[idx + 1] == 0 {
            0
        } else {
            1
        };
        let z_i_plus_1 = (ind * z_i) | anno_sum;
        z_i = z_i_plus_1;
        if idx >= len - 1 {
            res.push(z_i);
        }
    }

    res
}

pub fn or_agg_small_clear(
    indicators: &Vec<u128>,
    anno1: &Vec<u128>,
    anno2: &Vec<u128>,
    z0: u128,
    z_n_plus_1: u128,
) -> (Vec<u128>, u128) {
    let mut res = vec![];
    let mut z_i = if z0 == 0 { 0 } else { 1 };
    let mut out_z_i = z_i;
    let ind_len = indicators.len();
    let anno_len = anno1.len();
    for (idx, ind) in indicators.iter().enumerate() {
        let z_i_prim = (1 - ind) * z_i;
        res.push(z_i_prim);
        let anno_sum = if anno1[idx + 1] + anno2[idx + 1] == 0 {
            0
        } else {
            1
        };
        let z_i_plus_1 = (ind * z_i) | anno_sum;
        z_i = z_i_plus_1;
        if idx >= ind_len - 2 {
            if ind_len != anno_len && idx >= ind_len - 1 {
                res.push(z_i);
            } else if ind_len != anno_len && idx < ind_len - 1 {
                continue;
            } else {
                // last round
                let z_i_prim = (1 - indicators[idx + 1]) * z_i;
                res.push(z_i_prim);
                let anno_sum = if z_n_plus_1 == 0 { 0 } else { 1 };
                let z_i_plus_1 = (indicators[idx + 1] * z_i) | anno_sum;
                // z_i = z_i_plus_1; out_z_i = z_i;
                out_z_i = z_i_plus_1;
            }
            break;
        }
    }
    (res, out_z_i)
}




pub fn gb_agg_fast<S: Stream>(
    chunk_size: usize,
    ind: Vec<u128>,
    anno1: Vec<u128>,
    stream: S,
    tp: AggType,
    out_share1: Vec<u128>,
) {
    // next_z0_share1 should be a random val, here just for performance test
    let next_z0_share1 = 0_u128;
    let inds = split_by_chunk_size(ind, chunk_size);
    let anno1s = strict_split(anno1, chunk_size);
    let out_share1s = strict_split(out_share1, chunk_size);
    let mut rng_gb = AesRng::new();

    let chunk_num = anno1s.len();
    let mut z0_share1 = anno1s[0][0];
    for i in 0..chunk_num {
        let reader = BufReader::new(stream.try_clone().unwrap());
        let writer = BufWriter::new(stream.try_clone().unwrap());
        let mut channel = Channel::new(reader, writer);
        if i < chunk_num - 1 {
            gb_agg_small(
                &mut rng_gb,
                &mut channel,
                &inds[i],
                &anno1s[i],
                z0_share1,
                anno1s[i + 1][0],
                next_z0_share1,
                tp,
                &out_share1s[i],
            );
            z0_share1 = next_z0_share1;
        } else {
            gb_agg_small(
                &mut rng_gb,
                &mut channel,
                &inds[i],
                &anno1s[i],
                z0_share1,
                0,
                0,
                tp,
                &out_share1s[i],
            );
        }
    }
}

pub fn ev_agg_fast<S: Stream>(
    chunk_size: usize,
    anno2: Vec<u128>,
    stream: S,
    tp: AggType,
) -> Vec<u128> {
    let anno2s = strict_split(anno2, chunk_size);
    let mut rng_ev = AesRng::new();
    let mut res = vec![];
    let chunk_num = anno2s.len();
    let mut z0_share2 = anno2s[0][0];
    for i in 0..chunk_num {
        let reader = BufReader::new(stream.try_clone().unwrap());
        let writer = BufWriter::new(stream.try_clone().unwrap());
        let mut channel = Channel::new(reader, writer);
        if i < chunk_num - 1 {
            let (mut sub_anno2, next_z0_share2) = ev_agg_small(
                &mut rng_ev,
                &mut channel,
                &anno2s[i],
                z0_share2,
                anno2s[i + 1][0],
                tp,
                false,
            );
            z0_share2 = next_z0_share2;
            res.append(&mut sub_anno2);
        } else {
            let (mut sub_anno2, _) = ev_agg_small(
                &mut rng_ev,
                &mut channel,
                &anno2s[i],
                z0_share2,
                0,
                tp,
                true,
            );
            res.append(&mut sub_anno2);
        }
    }
    res
}

pub fn gb_agg_entire<S: Stream>(
    ind: &Vec<u128>,
    anno1: &Vec<u128>,
    stream: &mut S,
    tp: AggType,
    out_share1: &Vec<u128>,
) {
    // TODO: if size too large, break down to small gates
    let mut rng_ev = AesRng::new();
    let reader = BufReader::new(stream.try_clone().unwrap());
    let writer = BufWriter::new(stream);
    let channel = Channel::new(reader, writer);
    // gb_agg(&mut rng_ev, &mut channel, ind, anno1, tp, out_share1);
    let mut track_channle = TrackChannel::new(channel);
    gb_agg(&mut rng_ev, &mut track_channle, ind, anno1, tp, out_share1);
    let bytes_num = 256 * track_channle.total_kilobytes() as u64;
    crate::add_cross_shard(bytes_num);
}

pub fn ev_agg_entire<S: Stream>(
    anno2: &Vec<u128>,
    stream:&mut S,
    tp: AggType,
) -> Vec<u128> {
    let mut rng_ev = AesRng::new();
    let reader = BufReader::new(stream.try_clone().unwrap());
    let writer = BufWriter::new(stream);
    let mut channel = Channel::new(reader, writer);
    ev_agg(&mut rng_ev, &mut channel, anno2, tp)
}

mod test {
    /*
    test case
    F  Anno  Res
    A  1     0
    A  2     0
    A  2     5
    B  4     4
    C  1     0
    C  2     0
    C  3     6
    */

    #[test]
    fn test_add_agg() {
        use super::*;
        use scuttlebutt::{AesRng, Channel};

        let ind = vec![1, 1, 0, 0, 1, 1];
        let anno1 = vec![1, 1, 1, 1, 1, 1, 1];
        let anno2 = vec![0, 1, 1, 3, 0, 1, 2];
        let out_share1: Vec<u128> = vec![1, 3, 4, 2, 5, 4, 1];
        let out_share1_cp = out_share1.clone();

        let (sender, receiver) = obtain_tcp_stream();
        std::thread::scope(|s| {
            s.spawn(|| {
                let mut rng_gb = AesRng::new();
                let reader = BufReader::new(sender.try_clone().unwrap());
                let writer = BufWriter::new(sender);
                let mut channel = Channel::new(reader, writer);
                gb_agg(
                    &mut rng_gb,
                    &mut channel,
                    &ind,
                    &anno1,
                    AggType::Add,
                    &out_share1,
                );
            });

            let rng_ev = AesRng::new();
            let reader = BufReader::new(receiver.try_clone().unwrap());
            let writer = BufWriter::new(receiver);
            let mut channel = Channel::new(reader, writer);
            let res = ev_agg(&mut rng_ev.clone(), &mut channel, &anno2, AggType::Add);
            let res: Vec<u128> = res
                .into_iter()
                .zip(out_share1_cp.into_iter())
                .map(|(a, b)| a.wrapping_add(b))
                .collect();

            println!("res: {:?}", res);

            let resut_in_clear = add_agg_in_clear(&ind, &anno1, &anno2);

            assert!(
                res == resut_in_clear,
                "The result is incorrect and should be {:?}",
                resut_in_clear
            );
        });
    }

    #[allow(dead_code)]
    fn or_agg(ind: &Vec<u128>, anno: &Vec<u128>) -> Vec<u128> {
        let num_rows = anno.len(); // ind.len() + 1 = anno.len()
        let mut binary_anno = anno.clone();
        for i in 0..num_rows {
            if anno[i] != 0 {
                binary_anno[i] = 1;
            }
        }
        for i in 0..num_rows - 1 {
            if ind[i] == 1 {
                binary_anno[i + 1] |= binary_anno[i];
                binary_anno[i] = 0
            }
        }

        binary_anno
    }

    /*
    test case
    F  Anno  Res
    A  1     0
    A  0     0
    A  2     1
    B  4     1
    C  0     0
    C  0     0
    C  3     1
    D  5     0
    D  0     0
    D  0     0
    D  0     0
    D  0     1
    E  0     0
    E  0     0
    E  0     0
    */

    #[test]
    fn test_or_agg() {
        use super::*;
        use scuttlebutt::{AesRng, Channel};

        let ind = vec![1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1];
        let anno = vec![1, 0, 2, 4, 0, 0, 3, 5, 0, 0, 0, 0, 0, 0, 0];
        let anno1 = vec![0; 15];
        let anno2 = anno.clone();
        let out_share1 = vec![3, 24, 3, 4, 23, 42, 24, 32, 13, 42, 23, 42, 43, 23, 43];
        let out_share1_cp = out_share1.clone();
        let res_anno = or_agg(&ind, &anno);
        let res_anno2 = or_agg_in_clear(&ind, &anno1, &anno2);

        println!("{:?}", res_anno);
        assert_eq!(res_anno, res_anno2);

        let (sender, receiver) = obtain_tcp_stream();
        std::thread::scope(|s| {
            s.spawn(|| {
                let mut rng_gb = AesRng::new();
                let reader = BufReader::new(sender.try_clone().unwrap());
                let writer = BufWriter::new(sender);
                let mut channel = Channel::new(reader, writer);
                gb_agg(
                    &mut rng_gb,
                    &mut channel,
                    &ind,
                    &anno1,
                    AggType::Or,
                    &out_share1,
                );
            });

            let rng_ev = AesRng::new();
            let reader = BufReader::new(receiver.try_clone().unwrap());
            let writer = BufWriter::new(receiver);
            let mut channel = Channel::new(reader, writer);
            let res = ev_agg(&mut rng_ev.clone(), &mut channel, &anno2, AggType::Or);
            let res: Vec<u128> = res
                .into_iter()
                .zip(out_share1_cp.into_iter())
                .map(|(a, b)| a.wrapping_add(b))
                .collect();

            assert!(
                res == res_anno,
                "The result is incorrect and should be {:?}",
                res_anno
            );
        });
    }

    #[test]
    fn test_add_agg_small_clear() {
        use super::*;
        use rand::Rng;

        let n = 1000;
        let chunk_size = 100;
        let mut rng = rand::thread_rng();
        let ind: Vec<u128> = (0..n - 1).map(|_| rng.gen_range(0..2)).collect();
        let anno1: Vec<u128> = gen_unique_random_unsorted::<u32>(n)
            .into_iter()
            .map(|v| v as u128)
            .collect();
        let anno2: Vec<u128> = gen_unique_random_unsorted::<u32>(n)
            .into_iter()
            .map(|v| v as u128)
            .collect();

        let res1 = add_agg_in_clear(&ind, &anno1, &anno2);
        let mut z0 = anno1[0] + anno2[0];
        let indicators = split_by_chunk_size(ind, chunk_size);
        let anno1s = strict_split(anno1, chunk_size);
        let anno2s = strict_split(anno2, chunk_size);
        let mut res2 = vec![];

        let chunk_num = anno1s.len();
        for i in 0..chunk_num {
            if i < chunk_num - 1 {
                let (mut sub_res, z_i) = add_agg_small_clear(
                    &indicators[i],
                    &anno1s[i],
                    &anno2s[i],
                    z0,
                    &anno1s[i + 1][0] + &anno2s[i + 1][0],
                );
                res2.append(&mut sub_res);
                z0 = z_i;
            } else {
                let (mut sub_res, _) =
                    add_agg_small_clear(&indicators[i], &anno1s[i], &anno2s[i], z0, 0);
                res2.append(&mut sub_res);
            }
        }
        // println!("{:?}", res1);
        // println!("{:?}", res2);
        for i in 0..res1.len() {
            assert!(res1[i] == res2[i], "mismatched at {}", i);
        }
    }

    #[test]
    fn test_fast_add_agg() {
        use super::*;
        use rand::Rng;

        let n = 1000;
        let chunk_size = 100;
        let mut rng = rand::thread_rng();
        let ind: Vec<u128> = (0..n - 1).map(|_| rng.gen_range(0..2)).collect();
        let anno1: Vec<u128> = gen_unique_random_unsorted::<u32>(n)
            .into_iter()
            .map(|v| v as u128)
            .collect();
        let anno2: Vec<u128> = gen_unique_random_unsorted::<u32>(n)
            .into_iter()
            .map(|v| v as u128)
            .collect();

        let out_share1: Vec<u128> = gen_unique_random_unsorted::<u32>(n)
            .into_iter()
            .map(|v| v as u128)
            .collect();
        let out_share1_cp = out_share1.clone();
        let exp_res = add_agg_in_clear(&ind, &anno1, &anno2);

        let (sender, receiver) = obtain_tcp_stream();
        let (tx, rx) = std::sync::mpsc::channel();
        let thread1 = std::thread::spawn(move || {
            gb_agg_fast(chunk_size, ind, anno1, sender, AggType::Add, out_share1);
        });

        let thread2 = std::thread::spawn(move || {
            let res = ev_agg_fast(chunk_size, anno2, receiver, AggType::Add);
            tx.send(res).unwrap();
        });
        thread1.join().unwrap();
        thread2.join().unwrap();
        let res = rx.recv().unwrap();
        let res: Vec<u128> = res
            .into_iter()
            .zip(out_share1_cp.into_iter())
            .map(|(a, b)| a.wrapping_add(b))
            .collect();
        assert_eq!(res, exp_res);
    }

    #[test]
    fn test_or_agg_small_clear() {
        use super::*;
        use rand::Rng;

        let n = 1000;
        let chunk_size = 100;
        let mut rng = rand::thread_rng();
        let ind: Vec<u128> = (0..n - 1).map(|_| rng.gen_range(0..2)).collect();
        let anno1: Vec<u128> = gen_unique_random_unsorted::<u32>(n)
            .into_iter()
            .map(|v| v as u128)
            .collect();
        let anno2: Vec<u128> = gen_unique_random_unsorted::<u32>(n)
            .into_iter()
            .map(|v| v as u128)
            .collect();

        let res1 = or_agg_in_clear(&ind, &anno1, &anno2);
        let mut z0 = anno1[0] + anno2[0];
        let indicators = split_by_chunk_size(ind, chunk_size);
        let anno1s = strict_split(anno1, chunk_size);
        let anno2s = strict_split(anno2, chunk_size);
        let mut res2 = vec![];

        let chunk_num = anno1s.len();
        for i in 0..chunk_num {
            if i < chunk_num - 1 {
                let (mut sub_res, z_i) = or_agg_small_clear(
                    &indicators[i],
                    &anno1s[i],
                    &anno2s[i],
                    z0,
                    &anno1s[i + 1][0] + &anno2s[i + 1][0],
                );
                res2.append(&mut sub_res);
                z0 = z_i;
            } else {
                let (mut sub_res, _) =
                    or_agg_small_clear(&indicators[i], &anno1s[i], &anno2s[i], z0, 0);
                res2.append(&mut sub_res);
            }
        }
        // println!("{:?}", res1);
        // println!("{:?}", res2);
        for i in 0..res1.len() {
            assert!(res1[i] == res2[i], "mismatched at {}", i);
        }
    }

    #[test]
    fn test_fast_or_agg() {
        use super::*;
        use rand::Rng;

        let n = 1500;
        let chunk_size = 50;
        let mut rng = rand::thread_rng();
        let ind: Vec<u128> = (0..n - 1).map(|_| rng.gen_range(0..2)).collect();
        let anno1: Vec<u128> = gen_unique_random_unsorted::<u32>(n)
            .into_iter()
            .map(|v| v as u128)
            .collect();
        let anno2: Vec<u128> = gen_unique_random_unsorted::<u32>(n)
            .into_iter()
            .map(|v| v as u128)
            .collect();
        let out_share1: Vec<u128> = gen_unique_random_unsorted::<u32>(n)
            .into_iter()
            .map(|v| v as u128)
            .collect();
        let out_share1_cp = out_share1.clone();

        let exp_res = or_agg_in_clear(&ind, &anno1, &anno2);

        let (sender, receiver) = obtain_tcp_stream();
        let (tx, rx) = std::sync::mpsc::channel();
        let thread1 = std::thread::spawn(move || {
            gb_agg_fast(chunk_size, ind, anno1, sender, AggType::Or, out_share1);
        });

        let thread2 = std::thread::spawn(move || {
            let res = ev_agg_fast(chunk_size, anno2, receiver, AggType::Or);
            tx.send(res).unwrap();
        });
        thread1.join().unwrap();
        thread2.join().unwrap();
        let res = rx.recv().unwrap();
        let res: Vec<u128> = res
            .into_iter()
            .zip(out_share1_cp.into_iter())
            .map(|(a, b)| a.wrapping_add(b))
            .collect();
        assert_eq!(res, exp_res);
    }
}
