use fancy_garbling::{
    twopac::semihonest::{Evaluator, Garbler},
    util::u128_from_bits,
    AllWire, BinaryBundle, BinaryGadgets, Fancy, FancyArithmetic, FancyBinary, FancyInput,
    FancyReveal,
};
use ocelot::{ot::AlszReceiver as OtReceiver, ot::AlszSender as OtSender};
use scuttlebutt::{AbstractChannel, AesRng};
use std::fmt::Debug;

// struct containing both garbler and evaluators wires
// simplify the API of garbled circuit
struct EQLInputs<F> {
    pub garbler_wires: BinaryBundle<F>,
    pub evaluator_wires: BinaryBundle<F>,
}

// garbler's main method
// i): create garbler using rng and value
// ii): garbler exchanges its wires obliviously with evaluator
// iii): garbler and evaluator run the garbled circuit
// iv): garbler and evaluator open the res of computation
pub fn gb_eql<C>(rng: &mut AesRng, channel: &mut C, input: u128)
where
    C: AbstractChannel + std::clone::Clone,
{
    // i)
    let mut gb =
        Garbler::<C, AesRng, OtSender, AllWire>::new(channel.clone(), rng.clone()).unwrap();
    // ii)
    let circuit_wires = gb_set_fancy_inputs(&mut gb, input);
    // iii)
    let eql = fancy_eql::<Garbler<C, AesRng, OtSender, AllWire>>(&mut gb, circuit_wires).unwrap();
    // iv) garbler does not have output, so here the output is trash
    gb.outputs(eql.wires()).unwrap();
}

// gabler's wire exchange method
fn gb_set_fancy_inputs<F, E>(gb: &mut F, input: u128) -> EQLInputs<F::Item>
where
    F: FancyInput<Item = AllWire, Error = E>,
    E: Debug,
{
    // num of bits needed to represent a single input, here it is u128
    let nbits = 128;
    // garbler encodes their input into binary wires
    let garbler_wires: BinaryBundle<F::Item> = gb.bin_encode(input, nbits).unwrap();
    // evaluator receives their input lables using OT
    let evaluator_wires: BinaryBundle<F::Item> = gb.bin_receive(nbits).unwrap();

    EQLInputs {
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
pub fn ev_eql<C>(rng: &mut AesRng, channel: &mut C, input: u128) -> u128
where
    C: AbstractChannel + std::clone::Clone,
{
    // i)
    let mut ev =
        Evaluator::<C, AesRng, OtReceiver, AllWire>::new(channel.clone(), rng.clone()).unwrap();
    // ii)
    let circuit_wires = ev_set_fancy_inputs(&mut ev, input);
    // iii)
    let eql =
        fancy_eql::<Evaluator<C, AesRng, OtReceiver, AllWire>>(&mut ev, circuit_wires).unwrap();
    // iv)
    let eql_binary = ev
        .outputs(eql.wires())
        .unwrap()
        .expect("evaluator should produce outputs");
    // v)
    u128_from_bits(&eql_binary)
}

// evaluator's wire exchange method
fn ev_set_fancy_inputs<F, E>(ev: &mut F, input: u128) -> EQLInputs<F::Item>
where
    F: FancyInput<Item = AllWire, Error = E>,
    E: Debug,
{
    let nbits = 128;
    // evaluator receives the garblers input labels
    let garbler_wires: BinaryBundle<F::Item> = ev.bin_receive(nbits).unwrap();
    // evaluator receives its input labels using OT
    let evaluator_wires: BinaryBundle<F::Item> = ev.bin_encode(input, nbits).unwrap();

    EQLInputs {
        garbler_wires,
        evaluator_wires,
    }
}

// main function that describes the garbled circuit
fn fancy_eql<F>(
    f: &mut F,
    wire_inputs: EQLInputs<F::Item>,
) -> Result<BinaryBundle<F::Item>, F::Error>
where
    F: FancyReveal + Fancy + BinaryGadgets + FancyBinary + FancyArithmetic,
    // <F as Fancy>::Item: Debug,
{
    // data type is u128, therefore it is 128
    let nbits = 128;

    // garbler and evaluator's values are added together
    // for simplicity, we assume that addition will not result in a carry
    let combine =
        f.bin_addition_no_carry(&wire_inputs.garbler_wires, &wire_inputs.evaluator_wires)?;
    let zero = f.constant(0, 2)?;
    let one = f.constant(1, 2)?;

    // check if combine is 0
    let check_eql = f.bin_eq_bundles(
        &combine,
        &BinaryBundle::<F::Item>::new(vec![zero.clone(); nbits]),
    )?;

    let res = f.bin_multiplex(
        &check_eql,
        &BinaryBundle::<F::Item>::new(vec![one]),
        &BinaryBundle::<F::Item>::new(vec![zero]),
    )?;

    Ok(res)
}

// for debug only, check correctness
pub fn eql_in_clear(gb_val: u128, ev_val: u128) -> u128 {
    if gb_val + ev_val == 0 {
        0
    } else {
        1
    }
}

mod test {

    #[test]
    pub fn test_eql() {
        use super::{eql_in_clear, ev_eql, gb_eql};
        use scuttlebutt::AesRng;
        use scuttlebutt::Channel;
        use std::io::{BufReader, BufWriter};
        use std::os::unix::net::UnixStream;

        let gb_val = 0;
        let ev_val = 1;

        let (sender, receiver) = UnixStream::pair().unwrap();
        std::thread::spawn(move || {
            let rng_gb = AesRng::new();
            let reader = BufReader::new(sender.try_clone().unwrap());
            let writer = BufWriter::new(sender);
            let mut channel = Channel::new(reader, writer);
            gb_eql(&mut rng_gb.clone(), &mut channel, gb_val);
        });

        let rng_ev = AesRng::new();
        let reader = BufReader::new(receiver.try_clone().unwrap());
        let writer = BufWriter::new(receiver);
        let mut channel = Channel::new(reader, writer);

        let expect_eql = eql_in_clear(gb_val, ev_val);
        let res = ev_eql(&mut rng_ev.clone(), &mut channel, ev_val);
        println!("res: {}", res);
        assert!(expect_eql == res, "the garbled circuit result is incorrect");
    }
}
