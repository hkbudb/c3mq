use fancy_garbling::{
    twopac::semihonest::{Evaluator, Garbler},
    AllWire, BinaryGadgets, Fancy, FancyArithmetic, FancyBinary, FancyInput, FancyReveal,
};
use ocelot::{ot::AlszReceiver as OtReceiver, ot::AlszSender as OtSender};
use scuttlebutt::{AbstractChannel, AesRng};
use std::fmt::Debug;

// struct containing both garbler and evaluators wires
// simplify the API of garbled circuit
struct ORInputs<F> {
    pub garbler_wires: F,
    pub evaluator_wires: F,
}

// garbler's main method
// i): create garbler using rng and value
// ii): garbler exchanges its wires obliviously with evaluator
// iii): garbler and evaluator run the garbled circuit
// iv): garbler and evaluator open the res of computation
pub fn gb_or<C>(rng: &mut AesRng, channel: &mut C, input: bool)
where
    C: AbstractChannel + std::clone::Clone,
{
    // i)
    let mut gb =
        Garbler::<C, AesRng, OtSender, AllWire>::new(channel.clone(), rng.clone()).unwrap();
    // ii)
    let circuit_wires = gb_set_fancy_inputs(&mut gb, input);
    // iii)
    let or = fancy_or::<Garbler<C, AesRng, OtSender, AllWire>>(&mut gb, circuit_wires).unwrap();
    // iv) garbler does not have output, so here the output is trash
    gb.output(&or).unwrap();
}

// gabler's wire exchange method
fn gb_set_fancy_inputs<F, E>(gb: &mut F, input: bool) -> ORInputs<F::Item>
where
    F: FancyInput<Item = AllWire, Error = E>,
    E: Debug,
{
    // num of bits needed to represent a single input, here it is 2 because there are totally 4 conditions
    let nbits = 2;
    // garbler encodes their input into binary wires
    let garbler_wires: F::Item = gb.encode(input as u16, nbits).unwrap();
    // evaluator receives their input lables using OT
    let evaluator_wires: F::Item = gb.receive(nbits).unwrap();

    ORInputs {
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
pub fn ev_or<C>(rng: &mut AesRng, channel: &mut C, input: bool) -> bool
where
    C: AbstractChannel + std::clone::Clone,
{
    // i)
    let mut ev =
        Evaluator::<C, AesRng, OtReceiver, AllWire>::new(channel.clone(), rng.clone()).unwrap();
    // ii)
    let circuit_wires = ev_set_fancy_inputs(&mut ev, input);
    // iii)
    let or = fancy_or::<Evaluator<C, AesRng, OtReceiver, AllWire>>(&mut ev, circuit_wires).unwrap();
    // iv)
    let or_binary = ev
        .output(&or)
        .unwrap()
        .expect("evaluator should produce outputs");
    // v)
    bool_from_bit(or_binary)
}

fn bool_from_bit(val: u16) -> bool {
    val != 0
}

// evaluator's wire exchange method
fn ev_set_fancy_inputs<F, E>(ev: &mut F, input: bool) -> ORInputs<F::Item>
where
    F: FancyInput<Item = AllWire, Error = E>,
    E: Debug,
{
    let nbits = 2;
    // evaluator receives the garblers input labels
    let garbler_wires: F::Item = ev.receive(nbits).unwrap();
    // evaluator receives its input labels using OT
    let evaluator_wires: F::Item = ev.encode(input as u16, nbits).unwrap();

    ORInputs {
        garbler_wires,
        evaluator_wires,
    }
}

// main function that describes the garbled circuit
fn fancy_or<F>(f: &mut F, wire_inputs: ORInputs<F::Item>) -> Result<F::Item, F::Error>
where
    F: FancyReveal + Fancy + BinaryGadgets + FancyBinary + FancyArithmetic,
{
    // garbler and evaluator's values are added together
    let or = f.or(&wire_inputs.garbler_wires, &wire_inputs.evaluator_wires)?;

    Ok(or)
}

pub fn or_in_clear(gb_val: bool, ev_val: bool) -> bool {
    gb_val | ev_val
}

mod test {

    #[test]
    pub fn test_or() {
        use super::{ev_or, gb_or, or_in_clear};
        use scuttlebutt::AesRng;
        use scuttlebutt::Channel;
        use std::io::{BufReader, BufWriter};
        use std::os::unix::net::UnixStream;

        let gb_val = true;
        let ev_val = true;

        let (sender, receiver) = UnixStream::pair().unwrap();
        std::thread::spawn(move || {
            let rng_gb = AesRng::new();
            let reader = BufReader::new(sender.try_clone().unwrap());
            let writer = BufWriter::new(sender);
            let mut channel = Channel::new(reader, writer);
            gb_or(&mut rng_gb.clone(), &mut channel, gb_val);
        });

        let rng_ev = AesRng::new();
        let reader = BufReader::new(receiver.try_clone().unwrap());
        let writer = BufWriter::new(receiver);
        let mut channel = Channel::new(reader, writer);

        let expect_or = or_in_clear(gb_val, ev_val);
        let res = ev_or(&mut rng_ev.clone(), &mut channel, ev_val);
        println!("res: {}", res);
        assert!(expect_or == res, "the garbled circuit result is incorrect");
    }
}
