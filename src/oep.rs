// use rand::Rng;
use scuttlebutt::Block;
use std::fmt::Debug;

use crate::{
    ot::{ot_receiver, ot_sender},
    psi::ZERO_PLACE_HOLDER, tpch::Stream,
    // utils::gen_rand_from_fixed_seed,
};

// refer to https://github.com/hkustDB/SECYAN/blob/main/src/core/OEP.cpp
pub const GATE_NUM_MAP_SIZE: usize = 27;
pub const GATE_NUM_MAP: [u8; GATE_NUM_MAP_SIZE] = [
    0, 0, 1, 3, 5, 8, 11, 14, 17, 21, 25, 29, 33, 37, 41, 45, 49, 54, 59, 64, 69, 74, 79, 84, 89,
    94, 99,
];

pub const A: [u8; 1] = [1];

fn floor_log2(n: u32) -> u32 {
    if n == 0 {
        panic!("Cannot compute log2 of zero");
    }
    31 - n.leading_zeros() // This gives the floor of log2 for a non-zero u32
}

fn compute_gate_num(n: usize) -> u32 {
    if n < GATE_NUM_MAP_SIZE {
        return GATE_NUM_MAP[n] as u32;
    }
    let power = floor_log2(n as u32) + 1;

    power * n as u32 + 1 - (1 << power)
}

#[inline]
fn pack(a: u32, b: u32) -> u64 {
    (a as u64) << 32 | b as u64
}

#[inline]
fn unpack(c: u64) -> GateBlinder {
    GateBlinder {
        upper: (c >> 32) as u32,
        lower: (c & 0xffffffff) as u32,
    }
}

#[derive(Clone, Default)]
pub struct Label {
    input1: u32,
    input2: u32,
    output1: u32,
    output2: u32,
}

impl Debug for Label {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "({}, {}, {}, {})",
            self.input1, self.input2, self.output1, self.output2
        )
    }
}

#[derive(Clone, Default)]
pub struct GateBlinder {
    upper: u32,
    lower: u32,
}

impl Debug for GateBlinder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}, {})", self.upper, self.lower)
    }
}

fn write_gate_labels(input_labels: &mut Vec<u32>, size: usize, gate_labels: &mut [Label]) {
    // let mut rng = get_fixed_rng();
    if size == 2 {
        if let Some(gate_label) = gate_labels.get_mut(0) {
            gate_label.input1 = input_labels[0];
            gate_label.input2 = input_labels[1];
            // TODO
            // gate_label.output1 = rng.gen::<u32>();
            // gate_label.output2 = rng.gen::<u32>();
            // gate_label.output1 = gen_rand_from_fixed_seed();
            // gate_label.output2 = gen_rand_from_fixed_seed();
            gate_label.output1 = 0;
            gate_label.output2 = 0;
        } else {
            let new_label = Label {
                input1: input_labels[0],
                input2: input_labels[1],
                // TODO
                // output1: rng.gen::<u32>(),
                // output2: rng.gen::<u32>(),
                // output1: gen_rand_from_fixed_seed(),
                // output2: gen_rand_from_fixed_seed(),
                output1: 0,
                output2: 0,
            };
            gate_labels[0] = new_label;
        }
        input_labels[0] = gate_labels[0].output1;
        input_labels[1] = gate_labels[0].output2;
    }

    if size <= 2 {
        return;
    }

    let odd = size & 1;
    let half_size = size / 2;

    // compute left gates
    for i in 0..half_size {
        gate_labels[i].input1 = input_labels[2 * i];
        gate_labels[i].input2 = input_labels[2 * i + 1];
        // TODO
        // gate_labels[i].output1 = rng.gen::<u32>();
        // gate_labels[i].output2 = rng.gen::<u32>();
        // gate_labels[i].output1 = gen_rand_from_fixed_seed();
        // gate_labels[i].output2 = gen_rand_from_fixed_seed();
        gate_labels[i].output1 = 0;
        gate_labels[i].output2 = 0;
        input_labels[2 * i] = gate_labels[i].output1;
        input_labels[2 * i + 1] = gate_labels[i].output2;
    }

    let right_half_gate_labels = &mut gate_labels[half_size..];

    // compute upper subnetwork
    let mut upper_inputs = vec![0; half_size];
    for i in 0..half_size {
        upper_inputs[i] = input_labels[2 * i];
    }
    write_gate_labels(&mut upper_inputs, half_size, right_half_gate_labels);
    let upper_gate_num = compute_gate_num(half_size) as usize;
    // println!("upper_gate_num: {}", upper_gate_num);
    let upper_gate_labels = &mut right_half_gate_labels[upper_gate_num..];

    // compute lower subnetwork
    let lower_size = half_size + odd;
    let mut lower_inputs = vec![0; lower_size];
    for i in 0..half_size {
        lower_inputs[i] = input_labels[2 * i + 1];
    }
    if odd == 1 {
        // last element
        lower_inputs[lower_size - 1] = input_labels[size - 1];
    }
    write_gate_labels(input_labels, lower_size, upper_gate_labels);
    let lower_gate_num = if odd == 1 {
        compute_gate_num(lower_size) as usize
    } else {
        upper_gate_num
    };

    // println!("lower_gate_num: {}", lower_gate_num);
    // println!("upper_gate_labels size: {}", upper_gate_labels.len());
    let lower_gate_labels = &mut upper_gate_labels[lower_gate_num..];

    // handle subnetwork outputs
    for i in 0..half_size {
        input_labels[2 * i] = upper_inputs[i];
        input_labels[2 * i + 1] = lower_inputs[i];
    }
    if odd == 1 {
        // last element
        input_labels[size - 1] = lower_inputs[lower_size - 1];
    }

    // compute right gates
    for i in 0..(half_size - 1 + odd) {
        lower_gate_labels[i].input1 = input_labels[2 * i];
        lower_gate_labels[i].input2 = input_labels[2 * i + 1];
        // TODO
        // lower_gate_labels[i].output1 = rng.gen::<u32>();
        // lower_gate_labels[i].output2 = rng.gen::<u32>();
        // lower_gate_labels[i].output1 = gen_rand_from_fixed_seed();
        // lower_gate_labels[i].output2 = gen_rand_from_fixed_seed();
        lower_gate_labels[i].output1 = 0;
        lower_gate_labels[i].output2 = 0;
        input_labels[2 * i] = lower_gate_labels[i].output1;
        input_labels[2 * i + 1] = lower_gate_labels[i].output2;
    }
}

#[allow(dead_code)]
fn sub_with_overflow(left: u32, right: u32) -> u32 {
    if left >= right {
        return left - right;
    } else {
        return u32::MAX - right + left + 1;
    }
}

// sender
pub fn sender_permute<S: Stream>(stream: &mut S, val: &Vec<u32>) -> Vec<u32> {
    let size = val.len();
    let gate_num = compute_gate_num(size) as usize;

    // sender generate blinded inputs
    let mut gate_labels = vec![Label::default(); gate_num];
    let mut out = val.clone(); // permute order
                               // println!("gate_num: {}", gate_num);

    // randomly write label for each gate locally
    write_gate_labels(&mut out, size, &mut gate_labels);

    // println!("after wirte, gate_labels: \n{:?}", gate_labels);

    let mut msg0 = vec![0; gate_num];
    let mut msg1 = vec![0; gate_num];

    for i in 0..gate_num {
        let label = gate_labels.get(i as usize).unwrap();

        msg0[i] = pack(
            label.input1.wrapping_sub(label.output1),
            label.input2.wrapping_sub(label.output2),
            // sub_with_overflow(label.input1, label.output1),
            // sub_with_overflow(label.input2, label.output2),
        );
        msg1[i] = pack(
            label.input2.wrapping_sub(label.output1),
            label.input1.wrapping_sub(label.output2),
            // sub_with_overflow(label.input2, label.output1),
            // sub_with_overflow(label.input1, label.output2),
        );
    }

    // println!("msg0: {:?}", msg0);
    // println!("msg1: {:?}", msg1);

    // OT to send (msg0, msg1)
    let msg0_blk: Vec<Block> = msg0.into_iter().map(|d| Block::from(d as u128)).collect();
    let msg1_blk: Vec<Block> = msg1.into_iter().map(|d| Block::from(d as u128)).collect();

    ot_sender::<ocelot::ot::AlszSender, S>(msg0_blk, msg1_blk, stream);

    out
}

fn gen_selection_bits(permut_idxs: &Vec<usize>, size: usize, bits: &mut [bool]) {
    if size == 2 {
        bits[0] = permut_idxs[0] != 0;
    }
    if size <= 2 {
        return;
    }

    let mut inv_permut_idxs = vec![0; size];
    for i in 0..size {
        inv_permut_idxs[permut_idxs[i]] = i;
    }

    let odd = if size & 1 == 0 { false } else { true };
    let odd_num = if odd { 1 } else { 0 };

    // solve the edge coloring problem

    // flag=0: non-specified; flag=1: upper_network; flag=2: lower_network
    let mut left_flag = vec![0_u32; size];
    let mut right_flag = vec![0_u32; size];
    let mut right_ptr = size - 1;
    let mut left_ptr;
    while right_flag[right_ptr] == 0 {
        right_flag[right_ptr] = 2;
        left_ptr = permut_idxs[right_ptr];
        left_flag[left_ptr] = 2;
        if odd && left_ptr == size - 1 {
            break;
        }
        left_ptr = if left_ptr & 1 == 1 {
            left_ptr - 1
        } else {
            left_ptr + 1
        };
        left_flag[left_ptr] = 1;
        right_ptr = inv_permut_idxs[left_ptr];
        right_flag[right_ptr] = 1;
        right_ptr = if right_ptr & 1 == 1 {
            right_ptr - 1
        } else {
            right_ptr + 1
        };
    }

    for i in 0..size - 1 {
        right_ptr = i;
        while right_flag[right_ptr] == 0 {
            right_flag[right_ptr] = 2;
            left_ptr = permut_idxs[right_ptr];
            left_flag[left_ptr] = 2;
            left_ptr = if left_ptr & 1 == 1 {
                left_ptr - 1
            } else {
                left_ptr + 1
            };
            left_flag[left_ptr] = 1;
            right_ptr = inv_permut_idxs[left_ptr];

            right_flag[right_ptr] = 1;
            right_ptr = if right_ptr & 1 == 1 {
                right_ptr - 1
            } else {
                right_ptr + 1
            };
        }
    }

    // determine bits on left gates
    let half_size = size / 2;
    for i in 0..half_size {
        bits[i] = left_flag[2 * i] == 2;
    }

    let upper_idx = half_size;
    let upper_gate_num = compute_gate_num(half_size) as usize;
    let lower_idx = upper_idx + upper_gate_num;
    let right_gate_idx = lower_idx
        + if odd {
            compute_gate_num(half_size + 1) as usize
        } else {
            upper_gate_num
        };

    // determine bits on right gates
    for i in 0..half_size - 1 {
        bits[right_gate_idx + i] = right_flag[2 * i] == 2;
    }
    if odd {
        bits[right_gate_idx + half_size - 1] = right_flag[size - 2] == 1;
    }

    // compute upper network
    let mut upper_idxs = vec![0; half_size];

    for i in 0..half_size - 1 + odd_num {
        let bool_val = if bits[right_gate_idx + i] { 1 } else { 0 };
        upper_idxs[i] = permut_idxs[2 * i + bool_val] / 2;
    }
    if !odd {
        upper_idxs[half_size - 1] = permut_idxs[size - 2] / 2;
    }
    let upper_bits = &mut bits[upper_idx..];
    gen_selection_bits(&upper_idxs, half_size, upper_bits);

    // compute lower network
    let lower_size = half_size + odd_num;
    let mut lower_idxs = vec![0; lower_size];
    for i in 0..half_size - 1 + odd_num {
        let bool_val = if bits[right_gate_idx + i] { 1 } else { 0 };
        lower_idxs[i] = permut_idxs[2 * i + 1 - bool_val] / 2;
    }

    if odd {
        lower_idxs[half_size] = permut_idxs[size - 1] / 2;
    } else {
        lower_idxs[half_size - 1] = permut_idxs[2 * half_size - 1] / 2;
    }
    let lower_bits = &mut bits[lower_idx..];
    gen_selection_bits(&lower_idxs, lower_size, lower_bits);
}

// gate inputs: v0 = x0 - r1, v1 = x1 - r2
// gate outputs: if bit == 1, then v0 = x1 - r3, v1 = x0 - r4; otherwise, v0 = x0 - r3, v1 = x1 - r4
// m0 = r1 - r3, m1 = r2 - r4
fn evaluate_gate(v0: &u32, v1: &u32, blinder: &GateBlinder, bit: bool) -> (u32, u32) {
    if bit {
        let tmp = v1.wrapping_add(blinder.upper);
        let new_v1 = v0.wrapping_add(blinder.lower);
        let new_v0 = tmp;
        (new_v0, new_v1)

        // // let new_v1 = v0 + blinder.lower;
        // let new_v1 = v0.wrapping_add(blinder.lower) % u32::MAX;
        // // let new_v0 = v1 + blinder.upper;
        // let new_v0 = v1.wrapping_add(blinder.upper) % u32::MAX;
        // (new_v0, new_v1)
    } else {
        // let new_v0 = v0 + blinder.upper;
        let new_v0 = v0.wrapping_add(blinder.upper);
        // let new_v1 = v1 + blinder.lower;
        let new_v1 = v1.wrapping_add(blinder.lower);
        (new_v0, new_v1)
    }
}

// to apply the original exchange operation, set blinders to be 0
fn evaluate_network(vals: &mut Vec<u32>, size: usize, bits: &[bool], blinders: &[GateBlinder]) {
    // println!("vals: {:?}", vals);
    // println!("bits: {:?}", bits);
    // println!("blinders: {:?}", blinders);

    if size == 2 {
        // println!("0");
        let (new_v0, new_v1) = evaluate_gate(&vals[0], &vals[1], &blinders[0], bits[0]);
        // println!("new_v0: {}, new_v1: {}", new_v0, new_v1);
        vals[0] = new_v0;
        vals[1] = new_v1;
    }
    if size <= 2 {
        return;
    }
    let odd = size & 1;
    let half_size = size / 2;

    // compute left gates
    for i in 0..half_size {
        let (new_v0, new_v1) = evaluate_gate(&vals[2 * i], &vals[2 * i + 1], &blinders[i], bits[i]);
        // println!("new_v2*i: {}, new_v2*i+1: {}", new_v0, new_v1);
        vals[2 * i] = new_v0;
        vals[2 * i + 1] = new_v1;
    }

    let right_bits = &bits[half_size..];
    let right_blinders = &blinders[half_size..];

    // compute upper subnetwork
    let mut upper_vals = vec![0; half_size]; // len = half_size
    for i in 0..half_size {
        upper_vals[i] = vals[i * 2];
    }
    // println!("1");
    evaluate_network(&mut upper_vals, half_size, right_bits, right_blinders);
    let upper_gate_num = compute_gate_num(half_size) as usize;

    let upper_bits = &right_bits[upper_gate_num..];
    let upper_blinders = &right_blinders[upper_gate_num..];

    // compute lower subnetwork
    let low_size = half_size + odd;
    let mut lower_vals = vec![0; low_size]; // len = lower_size
    for i in 0..half_size {
        lower_vals[i] = vals[i * 2 + 1];
    }

    if odd == 1 {
        lower_vals[low_size - 1] = vals[size - 1];
    }
    // println!("2");
    evaluate_network(&mut lower_vals, low_size, upper_bits, upper_blinders);
    let lower_gate_num = if odd == 1 {
        compute_gate_num(low_size) as usize
    } else {
        upper_gate_num
    };

    let lower_bits = &upper_bits[lower_gate_num..];
    let lower_blinders = &upper_blinders[lower_gate_num..];

    // deal with outputs of subnetworks
    for i in 0..half_size {
        vals[2 * i] = upper_vals[i];
        vals[2 * i + 1] = lower_vals[i];
    }

    if odd == 1 {
        // the last element
        vals[size - 1] = lower_vals[low_size - 1];
    }

    // compute right gates
    for i in 0..half_size - 1 + odd {
        let (new_v0, new_v1) = evaluate_gate(
            &vals[2 * i],
            &vals[2 * i + 1],
            &lower_blinders[i],
            lower_bits[i],
        );
        vals[2 * i] = new_v0;
        vals[2 * i + 1] = new_v1;
    }
}

// permutor
pub fn permutor_permute<S: Stream>(
    stream: &mut S,
    pmt: &Vec<usize>,
    permutor_val: &Vec<u32>,
) -> Vec<u32> {
    let size = pmt.len();

    // check whether idxs is a valid permutation, i.e., idxs contains 0, ..., size-1
    // TODO: can use hashset to reduce a loop, or just remove the check
    let mut flags = vec![false; size];
    for i in pmt {
        // special case for zero position
        if *i == ZERO_PLACE_HOLDER {
            flags[0] = true;
        } else {
            flags[*i] = true;
        }
        // flags[*i] = true;
    }
    for flag in flags {
        assert!(flag, "invalid permutation");
    }
    assert_eq!(size, permutor_val.len());

    let gate_num = compute_gate_num(size);
    let mut select_bits = vec![false; gate_num as usize];
    gen_selection_bits(pmt, size, &mut select_bits);

    // OT to receive msg
    let msg_blk = ot_receiver::<ocelot::ot::AlszReceiver, S>(&select_bits, stream);
    let msg: Vec<u64> = msg_blk.into_iter().map(|d| u128::from(d) as u64).collect();

    // println!("msg: {:?}", msg);

    let mut gate_blinders = vec![GateBlinder::default(); gate_num as usize];

    for i in 0..gate_num as usize {
        let new_blinder = unpack(msg[i]);
        if let Some(b) = gate_blinders.get_mut(i) {
            *b = new_blinder;
        } else {
            panic!("cannot find the blinder at position {}", i);
        }
    }

    // println!("select_bits: {:?}", select_bits);
    // println!("gate_blinders: {:?}", gate_blinders);

    let mut out = permutor_val.clone();
    // println!("=======================");
    evaluate_network(&mut out, size, &select_bits, &gate_blinders);

    out
}

fn sender_replicate<S: Stream>(stream: &mut S, vals: &Vec<u32>) -> Vec<u32> {
    let size = vals.len();
    let mut labels = vec![Label::default(); size - 1];
    let mut out = vec![0_u32; size];
    for i in 0..size - 1 {
        if i == 0 {
            labels[i].input1 = vals[0];
        } else {
            labels[i].input1 = labels[i - 1].output2;
        }
        labels[i].input2 = vals[i + 1];
        // TODO
        // let rand_val = gen_rand_from_fixed_seed();
        let rand_val = 0;
        out[i] = rand_val;
        labels[i].output1 = rand_val;
        // labels[i].output2 = gen_rand_from_fixed_seed();
        labels[i].output2 = 0;
    }
    out[size - 1] = labels[size - 2].output2;
    let mut msg0 = vec![0_u64; size - 1];
    let mut msg1 = vec![0_u64; size - 1];

    for i in 0..size - 1 {
        msg0[i] = pack(
            labels[i].input1.wrapping_sub(labels[i].output1),
            labels[i].input2.wrapping_sub(labels[i].output2),
            // sub_with_overflow(labels[i].input1, labels[i].output1),
            // sub_with_overflow(labels[i].input2, labels[i].output2),
        );
        msg1[i] = pack(
            labels[i].input1.wrapping_sub(labels[i].output1),
            labels[i].input1.wrapping_sub(labels[i].output2),
            // sub_with_overflow(labels[i].input1, labels[i].output1),
            // sub_with_overflow(labels[i].input1, labels[i].output2),
        );
    }

    // println!("msg0: {:?}", msg0);
    // println!("================");
    // println!("msg1: {:?}", msg1);

    // OT to send (msg0, msg1)
    let msg0_blk: Vec<Block> = msg0.into_iter().map(|d| Block::from(d as u128)).collect();
    let msg1_blk: Vec<Block> = msg1.into_iter().map(|d| Block::from(d as u128)).collect();

    ot_sender::<ocelot::ot::AlszSender, S>(msg0_blk, msg1_blk, stream);

    out
}

fn permutor_replicate<S: Stream>(
    stream: &mut S,
    rep_bits: &Vec<bool>,
    permutor_vals: &Vec<u32>,
) -> Vec<u32> {
    let size = rep_bits.len() + 1;
    assert_eq!(size, permutor_vals.len());

    // OT to receive msg
    let msg_blk = ot_receiver::<ocelot::ot::AlszReceiver, S>(&rep_bits, stream);
    let msg: Vec<u64> = msg_blk.into_iter().map(|d| u128::from(d) as u64).collect();

    let mut out = vec![0_u32; size];
    let mut labels = vec![Label::default(); size - 1];
    for i in 0..size - 1 {
        let new_blinder = unpack(msg[i]);
        let upper = new_blinder.upper;
        let lower = new_blinder.lower;
        // println!("***upper: {}, lower: {}", upper, lower);
        if i == 0 {
            labels[i].input1 = permutor_vals[i]
        } else {
            labels[i].input1 = labels[i - 1].output2;
        }
        // println!("***labels[i].input1: {}", labels[i].input1);
        labels[i].input2 = permutor_vals[i + 1];

        let val = labels[i].input1.wrapping_add(upper);
        out[i] = val;
        labels[i].output1 = val;
        if rep_bits[i] {
            labels[i].output2 = labels[i].input1.wrapping_add(lower);
        } else {
            labels[i].output2 = labels[i].input2.wrapping_add(lower);
        }
    }
    out[size - 1] = labels[size - 2].output2;

    out
}

pub fn sender_extended_permute<S: Stream>(stream: &mut S, vals: &Vec<u32>, n: usize) -> Vec<u32> {
    let mut m = vals.len();
    if n > m {
        m = n;
    }
    let mut extended_vals = vals.clone();
    extended_vals.resize(m, 0);
    let mut out = sender_permute(stream, &extended_vals);
    // here n <= out.size = m
    out.resize(n, 0);
    out = sender_replicate(stream, &out);
    // println!("out after sender_replicate: {:?}", out);
    sender_permute(stream, &out)
}

pub fn permutor_extended_permute<S: Stream>(
    stream: &mut S,
    pmt: &Vec<usize>,         // len=n
    permutor_vals: &Vec<u32>, // len=m
) -> Vec<u32> {
    let mut m = permutor_vals.len();
    let n = pmt.len();
    if n > m {
        m = n;
    }
    let mut idx_cnt = vec![0_u32; m];
    for i in 0..n {
        // special case for zero position
        match pmt[i] {
            ZERO_PLACE_HOLDER => {
                idx_cnt[0] += 1;
            }
            v => {
                assert!(v < permutor_vals.len());
                idx_cnt[v] += 1;
            }
        }

        // assert!((pmt[i]) < permutor_vals.len());
        // idx_cnt[pmt[i]] += 1;
    }
    let mut first_perm = vec![0_usize; m];
    let mut dummy_idx = 0;
    let mut fp_idx = 0;
    let mut rep_bits = vec![false; n - 1];

    // call those idx with idxs_cnt[idx]==0 as dummy index
    for i in 0..m {
        if idx_cnt[i] > 0 {
            first_perm[fp_idx] = i; // attention here for i++
            fp_idx += 1;
            for _ in 0..idx_cnt[i] - 1 {
                while idx_cnt[dummy_idx] > 0 {
                    dummy_idx += 1;
                }
                first_perm[fp_idx] = dummy_idx; // attention here for i++
                fp_idx += 1;
                dummy_idx += 1;
            }
        }
    }

    while fp_idx < m {
        while idx_cnt[dummy_idx] > 0 {
            dummy_idx += 1;
        }
        first_perm[fp_idx] = dummy_idx; // attention here for i++
        fp_idx += 1;
        dummy_idx += 1;
    }

    let mut out = permutor_vals.clone();
    out.resize(m, 0);
    out = permutor_permute(stream, &first_perm, &out);
    // println!("out after permutor_permute: {:?}", out);
    out.resize(n, 0);
    for i in 0..n - 1 {
        rep_bits[i] = idx_cnt[first_perm[i + 1]] == 0;
    }
    // println!("=====================");
    // println!("rep_bits: {:?}", rep_bits);
    // println!("out before permutor_replicate: {:?}", out);
    // println!("=====================");
    out = permutor_replicate(stream, &rep_bits, &out);
    // println!("out after permutor_replicate: {:?}", out);
    let mut pointers = vec![0_u32; m];
    let mut sum = 0;
    for i in 0..m {
        pointers[i] = sum;
        sum += idx_cnt[i];
    }
    let mut total_map = vec![0_u32; n];
    for i in 0..n {
        // special case for zero position
        let idx = if pmt[i] == ZERO_PLACE_HOLDER {
            0
        } else {
            pmt[i]
        };
        total_map[i] = first_perm[pointers[idx] as usize] as u32;
        pointers[idx] += 1; // attention here for i++

        // total_map[i] = first_perm[pointers[pmt[i]] as usize] as u32;
        // pointers[pmt[i]] += 1; // attention here for i++
    }
    let mut inv_first_permu = vec![0usize; m];
    for i in 0..m {
        inv_first_permu[first_perm[i]] = i;
    }
    let mut second_permu = vec![0_usize; n];
    for i in 0..n {
        second_permu[i] = inv_first_permu[total_map[i] as usize];
    }
    // println!("second_permu before final permutor_permute: {:?}", second_permu);
    return permutor_permute(stream, &second_permu, &out);
}

// only consider m=n
pub fn inv_pmt(permutor: &Vec<usize>) -> Vec<usize> {
    let n = permutor.len();
    let mut inv_pmt = vec![0; n];
    for i in 0..n {
        // match permutor[i] {
        //     ZERO_PLACE_HOLDER => {inv_pmt[0] = i;}
        //     x => {
        //         assert!(x < n);
        //         inv_pmt[x] = i;
        //     }
        // }
        assert!(permutor[i] < n);
        inv_pmt[permutor[i]] = i;
    }
    inv_pmt
}

#[allow(dead_code)]
fn extended_permute(source: &Vec<u32>, permutor: &Vec<usize>) -> Vec<u32> {
    let m = source.len();
    let n = permutor.len();
    let mut res = vec![0; n];
    for i in 0..n {
        assert!(permutor[i] < m);
        res[i] = source[permutor[i]];
    }
    res
}

mod test {
    use std::{
        fmt::Display,
        io::{BufReader, BufWriter},
    };

    use ocelot::ot::{Receiver, Sender};
    use scuttlebutt::{AesRng, Block, Channel};

    use crate::utils::obtain_tcp_stream;

    #[allow(unused_imports)]
    use super::{floor_log2, pack, unpack};

    #[test]
    fn test_pack_unpack() {
        let a = 37;
        let b = 24;
        let c = pack(a, b);
        println!("packed, c = {}", c);
        let d = unpack(c);
        println!("unpacked, a = {}, b = {}", d.upper, d.lower);
    }

    #[test]
    fn test_floor_log2() {
        let a = 20;
        let b = floor_log2(a);
        println!("{}", b);
    }

    #[test]
    fn test_and_opt() {
        for i in 0..10 {
            let odd = i & 1;
            println!("i: {}, odd: {}", i, odd);
        }
    }

    #[test]
    fn test_ptr_move() {
        let bits = vec![1, 0, 0, 1, 1, 1, 0, 0];
        let part1 = &bits[2..];
        println!("{:?}", part1);
        let part2 = &part1[2..];
        println!("{:?}", part2);
    }

    #[test]
    fn test_compute_gate_num() {
        use super::compute_gate_num;
        let ns = vec![
            10, 20, 30, 40, 50, 60, 70, 80, 90, 100, 200, 500, 1000, 2000,
        ];
        for n in ns {
            let res = compute_gate_num(n);
            println!("{}: {}", n, res);
        }
    }

    #[allow(dead_code)]
    fn rand_blk_vec(size: usize) -> Vec<Block> {
        (0..size)
            .map(|_| Block::from(rand::random::<u128>()))
            .collect()
    }

    #[allow(dead_code)]
    fn rand_bool_vec(size: usize) -> Vec<bool> {
        (0..size).map(|_| rand::random::<bool>()).collect()
    }

    #[allow(dead_code)]
    fn test_ot<OTSender: Sender<Msg = Block>, OTReceiver: Receiver<Msg = Block> + Display>() {
        let size = 8977;
        let m0s = rand_blk_vec(size);
        let m1s = rand_blk_vec(size);
        let bs = rand_bool_vec(size);
        let m0s_clone = m0s.clone();
        let m1s_clone = m1s.clone();
        let (sender, receiver) = obtain_tcp_stream();
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::new();
            let reader = BufReader::new(sender.try_clone().unwrap());
            let writer = BufWriter::new(sender);
            let mut channel = Channel::new(reader, writer);
            let mut ot = OTSender::init(&mut channel, &mut rng).unwrap();
            let ms = m0s
                .into_iter()
                .zip(m1s.into_iter())
                .collect::<Vec<(Block, Block)>>();
            ot.send(&mut channel, &ms, &mut rng).unwrap();
        });
        let mut rng = AesRng::new();
        let reader = BufReader::new(receiver.try_clone().unwrap());
        let writer = BufWriter::new(receiver);
        let mut channel = Channel::new(reader, writer);
        let mut ot = OTReceiver::init(&mut channel, &mut rng).unwrap();
        let res = ot.receive(&mut channel, &bs, &mut rng).unwrap();
        for j in 0..size {
            assert_eq!(res[j], if bs[j] { m1s_clone[j] } else { m0s_clone[j] });
        }
        handle.join().unwrap();
    }

    #[test]
    pub fn test_different_ot() {
        // chou_orlandi OT is around 3x faster than naor_pinkas

        // let timer = howlong::ProcessCPUTimer::new();
        // test_ot::<ocelot::ot::NaorPinkasSender, ocelot::ot::NaorPinkasReceiver>();
        // let t = timer.elapsed().real.as_micros() as u64;
        // println!("time 1: {} ms", t / 1000);

        let timer = howlong::ProcessCPUTimer::new();
        test_ot::<ocelot::ot::ChouOrlandiSender, ocelot::ot::ChouOrlandiReceiver>();
        let t = timer.elapsed().real.as_micros() as u64;
        println!("time 2: {} ms", t / 1000);
    }

    #[allow(dead_code)]
    fn test_otext<OTSender: Sender<Msg = Block>, OTReceiver: Receiver<Msg = Block> + Display>() {
        let size = 8977;
        let m0s = rand_blk_vec(size);
        let m1s = rand_blk_vec(size);
        let bs = rand_bool_vec(size);
        let m0s_clone = m0s.clone();
        let m1s_clone = m1s.clone();
        let (sender, receiver) = obtain_tcp_stream();
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::new();
            let reader = BufReader::new(sender.try_clone().unwrap());
            let writer = BufWriter::new(sender);
            let mut channel = Channel::new(reader, writer);
            let mut otext = OTSender::init(&mut channel, &mut rng).unwrap();
            let ms = m0s
                .into_iter()
                .zip(m1s.into_iter())
                .collect::<Vec<(Block, Block)>>();
            otext.send(&mut channel, &ms, &mut rng).unwrap();
        });
        let mut rng = AesRng::new();
        let reader = BufReader::new(receiver.try_clone().unwrap());
        let writer = BufWriter::new(receiver);
        let mut channel = Channel::new(reader, writer);
        let mut otext = OTReceiver::init(&mut channel, &mut rng).unwrap();
        let res = otext.receive(&mut channel, &&bs, &mut rng).unwrap();
        handle.join().unwrap();
        for j in 0..size {
            assert_eq!(res[j], if bs[j] { m1s_clone[j] } else { m0s_clone[j] });
        }
    }

    #[test]
    pub fn test_different_otext() {
        // alsz OTE is slightly faster than kos OTE

        let timer = howlong::ProcessCPUTimer::new();
        test_otext::<ocelot::ot::AlszSender, ocelot::ot::AlszReceiver>();
        let t = timer.elapsed().real.as_micros() as u64;
        println!("time 1: {} ms", t / 1000);

        let timer = howlong::ProcessCPUTimer::new();
        test_otext::<ocelot::ot::KosSender, ocelot::ot::KosReceiver>();
        let t = timer.elapsed().real.as_micros() as u64;
        println!("time 2: {} ms", t / 1000);
    }

    #[test]
    fn test_op() {
        use super::{permutor_permute, sender_permute};
        use crate::utils::get_fixed_rng;
        use rand::seq::SliceRandom;

        let n = 100;
        let source: Vec<u32> = (0..n).collect();
        let mut target = source.clone();
        let mut rng = get_fixed_rng();

        target.shuffle(&mut rng);

        let dest: Vec<usize> = target.iter().map(|a| *a as usize).collect();

        let (mut sender, mut receiver) = obtain_tcp_stream();
        let handle = std::thread::spawn(move || {
            let res = sender_permute(&mut sender, &source);
            res
        });

        let zero = vec![0; n as usize];
        let res2 = permutor_permute(&mut receiver, &dest, &zero);

        let res1 = handle.join().unwrap();
        let res: Vec<u32> = res1
            .iter()
            .zip(res2.iter())
            .map(|(a, b)| a.wrapping_add(*b))
            .collect();

        println!("{:?}", res);
        assert_eq!(target, res);
    }

    // TODO: OP has err when n is odd, trying to debug
    #[test]
    fn dbg_op() {
        use super::*;
        let source = vec![11, 12, 13, 14, 15, 0, 0, 0, 0];
        let s1 = vec![1, 1, 2, 1, 3, 0, 0, 0, 0];
        let s2 = vec![10, 11, 11, 13, 12, 0, 0, 0, 0];
        let pmt = vec![8, 5, 7, 2, 3, 4, 1, 6, 0];
        // let pmt = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];
        // let pmt = vec![8, 7, 6, 5, 4, 3, 2, 1, 0];
        let target = extended_permute(&source, &pmt);
        let (mut sender, mut receiver) = obtain_tcp_stream();
        let handle = std::thread::spawn(move || {
            let res = sender_permute(&mut sender, &s1);
            res
        });
        let res2 = permutor_permute(&mut receiver, &pmt, &s2);
        let res1 = handle.join().unwrap();
        println!("res1: {:?}", res1);
        println!("res2: {:?}", res2);
        let res: Vec<u32> = res1
            .iter()
            .zip(res2.iter())
            .map(|(a, b)| a.wrapping_add(*b))
            .collect();
        println!("{:?}", target);
        println!("{:?}", res);
    }

    #[test]
    fn test_oep() {
        use rand::seq::SliceRandom;

        let m = 200;
        let n = 100;
        let one = vec![1; m];
        let source: Vec<u32> = (0..m as u32).collect();
        // debug only
        // let dest = vec![5, 0, 1, 3, 4, 0, 2, 3, 9, 6, 9, 4, 2, 3, 2, 4, 6, 0, 3, 0];

        let mut dest: Vec<usize> = (0..n).collect();
        let mut rng = rand::thread_rng();
        if m > n {
            dest.shuffle(&mut rng);
            dest.resize(n, 0);
        } else {
            for i in 0..dest.len() {
                let rand_val: usize = rand::Rng::gen(&mut rng);
                dest[i] = rand_val % m;
            }
        }

        let (mut sender, mut receiver) = obtain_tcp_stream();

        let handle = std::thread::spawn(move || {
            let res = super::sender_extended_permute(&mut sender, &source, n);
            res
        });

        let res2 = crate::oep::permutor_extended_permute(&mut receiver, &dest, &one);

        let res1 = handle.join().unwrap();
        let res: Vec<usize> = res1
            .iter()
            .zip(res2.iter())
            .map(|(a, b)| a.wrapping_add(*b).wrapping_sub(1) as usize)
            .collect();

        // println!("=============");
        // println!("dest: {:?}", dest);
        println!("res: {:?}", res);
        assert_eq!(dest, res);
    }

    // consider m=n only
    #[test]
    fn test_inv_pmt() {
        use super::inv_pmt;
        use crate::oep::extended_permute;
        use rand::seq::SliceRandom;
        use rand::Rng;

        let mut rng = rand::thread_rng();
        let n: usize = 100;
        let vec: Vec<u32> = (0..n as u32).map(|_| rng.gen::<u32>()).collect();

        let mut permutor: Vec<usize> = (0..n).collect();
        permutor.shuffle(&mut rng);

        let permuted_vec = extended_permute(&vec, &permutor);

        let inv_pmt = inv_pmt(&permutor);
        let vec_back = extended_permute(&permuted_vec, &inv_pmt);

        assert_eq!(vec, vec_back);

        let permuted_vec = extended_permute(&vec, &inv_pmt);
        let vec_back = extended_permute(&permuted_vec, &permutor);
        assert_eq!(vec, vec_back);
    }
}
