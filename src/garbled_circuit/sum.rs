use crate::tpch::Stream;
use fancy_garbling::WireMod2;
use ocelot::{ot::AlszReceiver as OtReceiver, ot::AlszSender as OtSender};
use scuttlebutt::{AbstractChannel, AesRng, Channel, TrackChannel};
use std::{
    fmt::Debug,
    io::{BufReader, BufWriter},
};

use crate::garbled_circuit::my_fancy_garbling::{gb::Garbler, ev::Evaluator, traits::*};

use super::my_fancy_garbling::util::u128_from_bits;

// struct containing both garbler and evaluators wires
// simplify the API of garbled circuit
struct SUMInputs<F> {
    pub garbler_wires: Vec<BinaryBundle<F>>,
    pub evaluator_wires: Vec<BinaryBundle<F>>,
}

// garbler's main method
// i): create garbler using rng and value
// ii): garbler exchanges its wires obliviously with evaluator
// iii): garbler and evaluator run the garbled circuit
// iv): garbler and evaluator open the res of computation
pub fn gb_sum<C>(rng: &mut AesRng, channel: &mut C, input: Vec<u128>)
where
    C: AbstractChannel + std::clone::Clone,
{
    // i)
    let mut gb =
        Garbler::<C, AesRng, OtSender, WireMod2>::new(channel.clone(), rng.clone()).unwrap();
    // ii)
    let circuit_wires = gb_set_fancy_inputs(&mut gb, input);
    // iii)
    let sum = fancy_sum::<Garbler<C, AesRng, OtSender, WireMod2>>(&mut gb, circuit_wires).unwrap();
    // iv) garbler does not have output, so here the output is trash
    gb.outputs(sum.wires()).unwrap();
}

// gabler's wire exchange method
fn gb_set_fancy_inputs<F, E>(gb: &mut F, input: Vec<u128>) -> SUMInputs<F::Item>
where
    F: FancyInput<Item = WireMod2, Error = E>,
    E: Debug,
{
    // num of bits needed to represent a single input, here it is u128
    let nbits = 128;
    let len = input.len();
    // garbler encodes their input into binary wires
    let garbler_wires: Vec<BinaryBundle<F::Item>> = gb.bin_encode_many(&input, nbits).unwrap();
    // evaluator receives their input lables using OT
    let evaluator_wires: Vec<BinaryBundle<F::Item>> = gb.bin_receive_many(len, nbits).unwrap();

    SUMInputs {
        garbler_wires,
        evaluator_wires,
    }
}

// evaluator's main method
// i): create evaluator using rng and value
// ii): evaluator exchanges its wires obliviously with garbler
// iii): evaluator and garbler run the garbled circuit
// iv): evaluator and garbler open the res of computation
// v): evaluator translates the binary output of circuit into its decimal format
pub fn ev_sum<C>(rng: &mut AesRng, channel: &mut C, input: Vec<u128>) -> u128
where
    C: AbstractChannel + std::clone::Clone,
{
    // i)
    let mut ev =
        Evaluator::<C, AesRng, OtReceiver, WireMod2>::new(channel.clone(), rng.clone()).unwrap();
    // ii)
    let circuit_wires = ev_set_fancy_inputs(&mut ev, input);
    // iii)
    let sum =
        fancy_sum::<Evaluator<C, AesRng, OtReceiver, WireMod2>>(&mut ev, circuit_wires).unwrap();
    // iv)
    let sum_binary = ev
        .outputs(sum.wires())
        .unwrap()
        .expect("evaluator should produce outputs");
    // v)
    u128_from_bits(&sum_binary)
}

// evaluator's wire exchange method
fn ev_set_fancy_inputs<F, E>(ev: &mut F, input: Vec<u128>) -> SUMInputs<F::Item>
where
    F: FancyInput<Item = WireMod2, Error = E>,
    E: Debug,
{
    let nbits = 128;
    let len = input.len();
    // evaluator receives the garblers input labels
    let garbler_wires: Vec<BinaryBundle<F::Item>> = ev.bin_receive_many(len, nbits).unwrap();
    // evaluator receives its input labels using OT
    let evaluator_wires: Vec<BinaryBundle<F::Item>> = ev.bin_encode_many(&input, nbits).unwrap();

    SUMInputs {
        garbler_wires,
        evaluator_wires,
    }
}

// main function that describes the garbled circuit
fn fancy_sum<F>(
    f: &mut F,
    wire_inputs: SUMInputs<F::Item>,
) -> Result<BinaryBundle<F::Item>, F::Error>
where
    F: FancyReveal + Fancy + BinaryGadgets + FancyBinary,
{
    // garbler and evaluator's values are added together
    // for simplicity, we assume that addition will not result in a carry
    let nbits = 128;
    let xs = wire_inputs.garbler_wires;
    let ys = wire_inputs.evaluator_wires;
    let mut sum = f.bin_constant_bundle(0, nbits)?;
    for i in 0..xs.len() {
        let addition = f.bin_addition_no_carry(&xs[i], &ys[i])?;
        sum = f.bin_addition_no_carry(&addition, &sum)?;

    }
    Ok(sum)
}

pub fn sum_in_clear(gb_val: Vec<u128>, ev_val: Vec<u128>) -> u128 {
    gb_val.iter().zip(ev_val.iter()).map(|(x, y)| x+y).sum()
}


pub fn gb_vec_sum<S: Stream>(
    anno1: Vec<u128>,
    stream: &mut S,
) {
    let reader = BufReader::new(stream.try_clone().unwrap());
    let mut rng_gb = AesRng::new();
    let writer = BufWriter::new(stream);
    let channel = Channel::new(reader, writer);
    // gb_sum(&mut rng_gb, &mut channel, &anno1);
    let mut track_channle = TrackChannel::new(channel);
    gb_sum(&mut rng_gb, &mut track_channle, anno1);
    let bytes_num = 256 * track_channle.total_kilobytes() as u64;
    crate::add_cross_shard(bytes_num);
}

pub fn ev_vec_sum<S: Stream>(
    anno2: Vec<u128>,
    stream: &mut S,
) -> u128 {
    let mut rng_ev = AesRng::new();
    let reader = BufReader::new(stream.try_clone().unwrap());
    let writer = BufWriter::new(stream);
    let mut channel = Channel::new(reader, writer);
    ev_sum(&mut rng_ev, &mut channel, anno2)
}

mod test {

    #[test]
    pub fn test_sum() {
        use super::{ev_sum, gb_sum, sum_in_clear};
        use scuttlebutt::AesRng;
        use scuttlebutt::Channel;
        use std::io::{BufReader, BufWriter};
        use std::os::unix::net::UnixStream;

        let gb_val = vec![1, 2, 3, 4, 5];
        let gb_val_ = gb_val.clone();
        let ev_val = vec![9, 8, 7, 6, 5];
        let ev_val_ = ev_val.clone();

        let (sender, receiver) = UnixStream::pair().unwrap();
        std::thread::spawn(move || {
            let rng_gb = AesRng::new();
            let reader = BufReader::new(sender.try_clone().unwrap());
            let writer = BufWriter::new(sender);
            let mut channel = Channel::new(reader, writer);
            gb_sum(&mut rng_gb.clone(), &mut channel, gb_val);
        });

        let rng_ev = AesRng::new();
        let reader = BufReader::new(receiver.try_clone().unwrap());
        let writer = BufWriter::new(receiver);
        let mut channel = Channel::new(reader, writer);
        
        let res = ev_sum(&mut rng_ev.clone(), &mut channel, ev_val);
        println!("res: {}", res);

        let expect_sum = sum_in_clear(gb_val_, ev_val_);
        assert!(expect_sum == res, "the garbled circuit result is incorrect");
    }
}
