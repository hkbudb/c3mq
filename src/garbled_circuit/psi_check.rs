use crate::{garbled_circuit::my_fancy_garbling::util, tpch::Stream, utils::*};
use fancy_garbling::WireMod2;
use ocelot::{ot::AlszReceiver as OtReceiver, ot::AlszSender as OtSender};
use rayon::iter::{
    IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, IntoParallelRefMutIterator, ParallelIterator
};
use scuttlebutt::{AbstractChannel, AesRng, Channel, TrackChannel};
use std::{
    fmt::Debug,
    io::{BufReader, BufWriter},
};

use crate::garbled_circuit::my_fancy_garbling::{gb::Garbler, ev::Evaluator, traits::*};

struct CheckInputs<F> {
    // sender input
    anno1: Vec<BinaryBundle<F>>,
    r: BinaryBundle<F>,
    // receiver input
    vs_pp: Vec<BinaryBundle<F>>,
    ys_hat: Vec<BinaryBundle<F>>,
}

pub fn gb_psi_check<C>(rng: &mut AesRng, channel: &mut C, r: u128, anno1: &Vec<u128>)
where
    C: AbstractChannel + std::clone::Clone,
{
    let mut gb =
        Garbler::<C, AesRng, OtSender, WireMod2>::new(channel.clone(), rng.clone()).unwrap();
    let circuit_wires = gb_set_check_inputs(&mut gb, r, anno1);

    let check_res =
        fancy_check::<Garbler<C, AesRng, OtSender, WireMod2>>(&mut gb, circuit_wires).unwrap();

    for res in check_res {
        gb.outputs(res.wires()).unwrap();
    }
}

fn gb_set_check_inputs<F, E>(gb: &mut F, r: u128, anno1: &Vec<u128>) -> CheckInputs<F::Item>
where
    F: FancyInput<Item = WireMod2, Error = E>,
    E: Debug,
{
    let nbits = 128;
    let anno_size = anno1.len();
    let anno1: Vec<BinaryBundle<F::Item>> = gb.bin_encode_many(anno1, nbits).unwrap();
    let r: BinaryBundle<F::Item> = gb.bin_encode(r, nbits).unwrap();

    let vs_pp: Vec<BinaryBundle<F::Item>> = gb.bin_receive_many(anno_size, nbits).unwrap();

    let ys_hat: Vec<BinaryBundle<F::Item>> = gb.bin_receive_many(anno_size, nbits).unwrap();

    CheckInputs {
        anno1,
        r,
        vs_pp,
        ys_hat,
    }
}

pub fn ev_psi_check<C>(
    rng: &mut AesRng,
    channel: &mut C,
    vs_pp: &Vec<u128>,
    ys_hat: &Vec<u128>,
) -> Vec<u128>
where
    C: AbstractChannel + std::clone::Clone,
{
    let mut ev =
        Evaluator::<C, AesRng, OtReceiver, WireMod2>::new(channel.clone(), rng.clone()).unwrap();
    
    let circuit_wires = ev_set_check_inputs(&mut ev, vs_pp, ys_hat);

    let check_res =
        fancy_check::<Evaluator<C, AesRng, OtReceiver, WireMod2>>(&mut ev, circuit_wires).unwrap();

    let mut res = vec![];
    for check in check_res {
        let val_bin = ev
            .outputs(check.wires())
            .unwrap()
            .expect("evaluator should produce outputs");
        res.push(util::u128_from_bits(&val_bin));
    }

    res
}

fn ev_set_check_inputs<F, E>(
    ev: &mut F,
    vs_pp: &Vec<u128>,
    ys_hat: &Vec<u128>,
) -> CheckInputs<F::Item>
where
    F: FancyInput<Item = WireMod2, Error = E>,
    E: Debug,
{
    let nbits = 128;
    let size = vs_pp.len();

    let anno1: Vec<BinaryBundle<F::Item>> = ev.bin_receive_many(size, nbits).unwrap();
    let r: BinaryBundle<F::Item> = ev.bin_receive(nbits).unwrap();
    let vs_pp: Vec<BinaryBundle<F::Item>> = ev.bin_encode_many(vs_pp, nbits).unwrap();
    let ys_hat: Vec<BinaryBundle<F::Item>> = ev.bin_encode_many(ys_hat, nbits).unwrap();

    CheckInputs {
        anno1,
        r,
        vs_pp,
        ys_hat,
    }
}

// exist_flag indicates whether the annotation is existing annotation, if it is true, the multiplexer will have different order due to implementation of the lib
fn fancy_check<F>(
    f: &mut F,
    wire_inputs: CheckInputs<F::Item>,
) -> Result<Vec<BinaryBundle<F::Item>>, F::Error>
where
    F: FancyReveal + Fancy + BinaryGadgets + FancyBinary,
{
    let r: BinaryBundle<_> = wire_inputs.r;
    let anno1: Vec<BinaryBundle<_>> = wire_inputs.anno1;
    let vs_pp: Vec<BinaryBundle<_>> = wire_inputs.vs_pp;
    let ys_hat: Vec<BinaryBundle<_>> = wire_inputs.ys_hat;

    assert_eq!(vs_pp.len(), ys_hat.len());
    assert_eq!(anno1.len(), vs_pp.len());

    let nbits = 128;
    let mut res = vec![];

    for i in 0..anno1.len() {
        let check_eql = f.bin_eq_bundles(&r, &ys_hat[i])?;

        // additive sharing
        let intermediate_xor = f.bin_xor(&vs_pp[i], &r)?;
        let case1 = f.bin_subtraction(&intermediate_xor, &anno1[i])?.0;

        let zero = f.bin_constant_bundle(0, nbits)?;
        let case2 = f.bin_subtraction(&zero, &anno1[i])?.0;
        // multiplex(b, x, y): b=0 => return x; otherwise return y
        let val = f.bin_multiplex(&check_eql, &case2, &case1)?;

        // xor sharing
        // let intermediate_xor = f.bin_xor(&anno1[i], &vs_pp[i])?;
        // let case1 = f.bin_xor(&intermediate_xor, &r)?;
        // let case2 = &anno1[i];
        // let val = f.bin_multiplex(&check_eql, &case2, &case1)?;

        res.push(val);
    }

    Ok(res)
}

pub fn check_in_clear(
    anno1: &Vec<u128>,  // sender
    r: u128,            // sender
    vs_pp: &Vec<u128>,  // receiver
    ys_hat: &Vec<u128>, // receiver
) -> Vec<u128> {
    assert_eq!(vs_pp.len(), ys_hat.len());
    assert_eq!(anno1.len(), vs_pp.len());
    let size = vs_pp.len();
    let mut res = vec![];
    for i in 0..size {
        if r == ys_hat[i] {
            res.push((vs_pp[i] ^ r).wrapping_sub(anno1[i]));
        } else {
            res.push(0_u128.wrapping_sub(anno1[i]));
        }
    }
    res
}

pub fn gb_psi_check_fast<S: Stream>(chunk_size: usize, anno1: Vec<u128>, r: u128, stream: &mut S) {
    let anno1s = strict_split(anno1, chunk_size);
    let mut rng_gb = AesRng::new();

    for anno1 in &anno1s {
        let reader = BufReader::new(stream.try_clone().unwrap());
        let writer = BufWriter::new(stream.try_clone().unwrap());
        let mut channel = Channel::new(reader, writer);
        gb_psi_check(&mut rng_gb, &mut channel, r, &anno1);
    }
}

pub fn gb_psi_check_parallel<S: Stream>(
    anno1: Vec<u128>,
    r: u128,
    streams: &mut Vec<S>,
){
    let anno1s = split_by(anno1, streams.len());

    assert_eq!(anno1s.len(), streams.len());

    anno1s
        .par_iter()
        .zip(streams.par_iter_mut())
        .for_each(|(anno1, stream)| {
            let reader = BufReader::new(stream.try_clone().unwrap());
            let mut rng_gb = AesRng::new();
            let writer = BufWriter::new(stream);
            let channel = Channel::new(reader, writer);
            // gb_psi_check(&mut rng_gb, &mut channel, r, &anno1);
            let mut track_channle = TrackChannel::new(channel);
            gb_psi_check(&mut rng_gb, &mut track_channle, r, &anno1);
            let bytes_num = 256 * track_channle.total_kilobytes() as u64;
            crate::add_cross_shard(bytes_num);
        });
}

pub fn ev_psi_check_parallel<S: Stream>(
    vs_pp: Vec<u128>,
    ys_hat: Vec<u128>,
    streams: &mut Vec<S>,
) -> Vec<u128> {
    let n = streams.len();
    let vs_pps = split_by(vs_pp, n);
    let ys_hats = split_by(ys_hat, n);

    let size = vs_pps.len();

    assert_eq!(size, ys_hats.len());
    assert_eq!(size, streams.len());

    let res: Vec<Vec<u128>> = vs_pps
        .par_iter()
        .zip(ys_hats.par_iter())
        .zip(streams.par_iter_mut())
        .map(|((vs_pp, ys_hat), stream)| {
            let mut rng_ev = AesRng::new();
            let reader = BufReader::new(stream.try_clone().unwrap());
            let writer = BufWriter::new(stream);
            let mut channel = Channel::new(reader, writer);
            ev_psi_check(&mut rng_ev, &mut channel, &vs_pp, &ys_hat)
        })
        .collect();

    let res: Vec<u128> = res
        .into_par_iter()
        .flat_map(|vec| vec.into_par_iter())
        .collect();

    res
}

pub fn ev_psi_check_fast<S: Stream>(
    chunk_size: usize,
    vs_pp: Vec<u128>,
    ys_hat: Vec<u128>,
    stream: &mut S,
) -> Vec<u128> {
    let vs_pps = strict_split(vs_pp, chunk_size);
    let ys_hats = strict_split(ys_hat, chunk_size);

    let rng_ev = AesRng::new();

    let mut res = vec![];
    for i in 0..vs_pps.len() {
        let reader = BufReader::new(stream.try_clone().unwrap());
        let writer = BufWriter::new(stream.try_clone().unwrap());
        let mut channel = Channel::new(reader, writer);
        let mut sub_res: Vec<u128> =
            ev_psi_check(&mut rng_ev.clone(), &mut channel, &vs_pps[i], &ys_hats[i]);
        res.append(&mut sub_res);
    }
    res
}
mod tests {

    #[test]
    fn test_psi_check() {
        use super::*;
        use rand::Rng;
        use scuttlebutt::channel::TrackChannel;
        use scuttlebutt::{AesRng, Channel};
        use std::{
            io::{BufReader, BufWriter},
            os::unix::net::UnixStream,
        };

        let mut rng = rand::thread_rng();
        let r: u128 = rng.gen();
        let anno1 = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let vs_pp = vec![11, 12, 13, 14, 15, 16, 17, 18, 19, 20];
        let ys_hat = vec![1, 2, 3, r, r, r, r, r, 4, 5];
        let anno2_clear = check_in_clear(&anno1, r, &vs_pp, &ys_hat);

        let res: Vec<u128> = anno1
            .iter()
            .zip(anno2_clear.iter())
            .map(|(a, b)| a.wrapping_add(*b))
            .collect();
        let exp_res = vec![
            0,
            0,
            0,
            vs_pp[3] ^ r,
            vs_pp[4] ^ r,
            vs_pp[5] ^ r,
            vs_pp[6] ^ r,
            vs_pp[7] ^ r,
            0,
            0,
        ];
        assert_eq!(res, exp_res);
        // println!("{:?}", res);

        let (sender, receiver) = UnixStream::pair().unwrap();
        std::thread::scope(|s| {
            s.spawn(|| {
                let mut rng_gb = AesRng::new();
                let reader = BufReader::new(sender.try_clone().unwrap());
                let writer = BufWriter::new(sender);
                let channel = Channel::new(reader, writer);
                let mut track_channle = TrackChannel::new(channel);
                gb_psi_check(&mut rng_gb, &mut track_channle, r, &anno1);
                println!("inner: {} kilobytes", track_channle.total_kilobytes());
            });

            let rng_ev = AesRng::new();
            let reader = BufReader::new(receiver.try_clone().unwrap());
            let writer = BufWriter::new(receiver);
            let channel = Channel::new(reader, writer);
            let mut track_channle = TrackChannel::new(channel);
            let anno2 = ev_psi_check(&mut rng_ev.clone(), &mut track_channle, &vs_pp, &ys_hat);
            println!("outer: {} kilobytes", track_channle.total_kilobytes());

            assert_eq!(anno2, anno2_clear);
        });
    }

    #[test]
    fn test_psi_check_fast() {
        use super::*;
        use rand::prelude::SliceRandom;
        use rand::Rng;

        let mut rng = rand::thread_rng();
        let r: u128 = rng.gen();
        let n = 1000;
        let chunk_size = 100;

        let sel = (n as f64 * 0.1) as usize; // sel: 10%
        let rs = vec![r; sel];
        let anno1 = gen_unique_random_unsorted::<u128>(n);
        let vs_pp = gen_unique_random_unsorted::<u128>(n);
        let mut ys_hat = gen_unique_random_unsorted::<u128>(n - sel);
        ys_hat.extend(rs);
        ys_hat.shuffle(&mut rng);

        let exp_anno2 = check_in_clear(&anno1, r, &vs_pp, &ys_hat);

        let (mut sender, mut receiver) = obtain_tcp_stream();
        

        let (tx, rx) = std::sync::mpsc::channel();

        let thread1 = std::thread::spawn(move || {
            gb_psi_check_fast(chunk_size, anno1, r, &mut sender);
        });

        let thread2 = std::thread::spawn(move || {
            let res = ev_psi_check_fast(chunk_size, vs_pp, ys_hat, &mut receiver);
            tx.send(res).unwrap();
        });

        thread1.join().unwrap();
        thread2.join().unwrap();
        let anno2 = rx.recv().unwrap();
        assert_eq!(anno2, exp_anno2);
    }
}
