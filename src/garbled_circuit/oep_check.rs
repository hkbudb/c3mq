use crate::{tpch::Stream, utils::*};
use fancy_garbling::{
    twopac::semihonest::{Evaluator, Garbler},
    util, AllWire, BinaryBundle, BinaryGadgets, Fancy, FancyArithmetic, FancyBinary, FancyInput,
    FancyReveal,
};
use ocelot::{ot::AlszReceiver as OtReceiver, ot::AlszSender as OtSender};
use rayon::iter::{IndexedParallelIterator, IntoParallelIterator, ParallelIterator};
use scuttlebutt::{AbstractChannel, AesRng, Channel, TrackChannel};
use std::{
    fmt::Debug,
    io::{BufReader, BufWriter},
};

struct CheckInputs<F> {
    // sender input
    oep_anno1: Vec<BinaryBundle<F>>,   // s ele
    permutation: Vec<BinaryBundle<F>>, // s ele
    // receiver input
    oep_anno2: Vec<BinaryBundle<F>>, // s ele
}

pub fn gb_oep_check<C>(
    rng: &mut AesRng,
    channel: &mut C,
    oep_anno1: &Vec<u128>,   // s
    permutation: &Vec<u128>, // s, (entire pmt is n+s, but only last s are used)
) where
    C: AbstractChannel + std::clone::Clone,
{
    let mut gb =
        Garbler::<C, AesRng, OtSender, AllWire>::new(channel.clone(), rng.clone()).unwrap();
    let circuit_wires = gb_set_check_inputs(&mut gb, oep_anno1, permutation);
    let check_res =
        fancy_check::<Garbler<C, AesRng, OtSender, AllWire>>(&mut gb, circuit_wires).unwrap();
    for res in check_res {
        gb.outputs(res.wires()).unwrap();
    }
}

fn gb_set_check_inputs<F, E>(
    gb: &mut F,
    oep_anno1: &Vec<u128>,
    permutation: &Vec<u128>,
) -> CheckInputs<F::Item>
where
    F: FancyInput<Item = AllWire, Error = E>,
    E: Debug,
{
    let nbits = 128;
    let anno_size = oep_anno1.len();
    let oep_anno1: Vec<BinaryBundle<F::Item>> = gb.bin_encode_many(oep_anno1, nbits).unwrap();

    let permutation: Vec<BinaryBundle<F::Item>> = gb.bin_encode_many(permutation, nbits).unwrap();

    let oep_anno2: Vec<BinaryBundle<F::Item>> = gb.bin_receive_many(anno_size, nbits).unwrap();

    CheckInputs {
        oep_anno1,
        permutation,
        oep_anno2,
    }
}

pub fn ev_oep_check<C>(rng: &mut AesRng, channel: &mut C, oep_anno2: &Vec<u128>) -> Vec<u128>
where
    C: AbstractChannel + std::clone::Clone,
{
    let mut ev =
        Evaluator::<C, AesRng, OtReceiver, AllWire>::new(channel.clone(), rng.clone()).unwrap();
    // println!("@@@@ before ev check inputs");
    let circuit_wires = ev_set_check_inputs(&mut ev, oep_anno2);
    let check_res =
        fancy_check::<Evaluator<C, AesRng, OtReceiver, AllWire>>(&mut ev, circuit_wires).unwrap();
    let mut res = vec![];
    // println!("check_res len: {}", check_res.len());
    // let mut cnt = 0;
    for check in check_res {
        let val_bin = ev
            .outputs(check.wires())
            .unwrap()
            .expect("evaluator should produce outputs");
        res.push(util::u128_from_bits(&val_bin));
        // println!("{}", cnt);
        // cnt += 1;
    }

    res
}

fn ev_set_check_inputs<F, E>(ev: &mut F, oep_anno2: &Vec<u128>) -> CheckInputs<F::Item>
where
    F: FancyInput<Item = AllWire, Error = E>,
    E: Debug,
{
    let nbits = 128;
    let anno_size = oep_anno2.len(); // s

    let oep_anno1: Vec<BinaryBundle<F::Item>> = ev.bin_receive_many(anno_size, nbits).unwrap();
    let permutation: Vec<BinaryBundle<F::Item>> = ev.bin_receive_many(anno_size, nbits).unwrap();
    let oep_anno2: Vec<BinaryBundle<F::Item>> = ev.bin_encode_many(oep_anno2, nbits).unwrap();

    CheckInputs {
        oep_anno1,
        permutation,
        oep_anno2,
    }
}

fn fancy_check<F>(
    f: &mut F,
    wire_inputs: CheckInputs<F::Item>,
) -> Result<Vec<BinaryBundle<F::Item>>, F::Error>
where
    F: FancyReveal + Fancy + BinaryGadgets + FancyBinary + FancyArithmetic,
{
    let oep_anno1: Vec<BinaryBundle<_>> = wire_inputs.oep_anno1; // s
    let permutation: Vec<BinaryBundle<_>> = wire_inputs.permutation; // s+n ele
    let oep_anno2: Vec<BinaryBundle<_>> = wire_inputs.oep_anno2; // s
    let nbits = 128;
    let s = oep_anno1.len();

    let mut res = vec![];
    for i in 0..s {
        let anno = f
            .bin_addition_no_carry(&oep_anno1[i], &oep_anno2[i])
            .unwrap();
        // let anno = f
        //     .bin_xor(&oep_anno1[i], &oep_anno2[i])
        //     .unwrap();
        let case2 = &permutation[i];

        let zero = f.bin_constant_bundle(0, nbits)?;

        let check_eql = f.bin_eq_bundles(&anno, &zero)?;

        let val = f.bin_multiplex(&check_eql, &anno, case2)?;

        res.push(val);
    }

    Ok(res)
}

// dbg only, check correctness
pub fn check_in_clear(
    oep_anno1: &Vec<u128>,   // s elements
    permutation: &Vec<u128>, // s + n elements
    oep_anno2: &Vec<u128>,   // s elements
) -> Vec<u128> {
    assert_eq!(oep_anno1.len(), oep_anno2.len());
    let s = oep_anno1.len();
    let n = permutation.len() - s;

    let mut res = vec![];
    for i in 0..s {
        let oep_anno = oep_anno1[i].wrapping_add(oep_anno2[i]);
        if oep_anno == 0 {
            res.push(permutation[n + i]);
        } else {
            res.push(oep_anno)
        }
    }
    res
}

pub fn gb_oep_check_fast<S: Stream>(
    chunk_size: usize,
    psi_res1: Vec<u128>,
    stream: S,
    permutation: Vec<u128>,
) {
    let mut rng_gb = AesRng::new();
    let psi_res1s = strict_split(psi_res1, chunk_size);
    let inv_pmts = strict_split(permutation, chunk_size);

    for i in 0..psi_res1s.len() {
        let reader = BufReader::new(stream.try_clone().unwrap());
        let writer = BufWriter::new(stream.try_clone().unwrap());
        let channel = Channel::new(reader, writer);
        // gb_oep_check(&mut rng_gb, &mut channel, &psi_res1s[i], &inv_pmts[i]);
        let mut track_channle = TrackChannel::new(channel);
        gb_oep_check(&mut rng_gb, &mut track_channle, &psi_res1s[i], &inv_pmts[i]);
        let bytes_num = 256 * track_channle.total_kilobytes() as u64;
        crate::add_cross_shard(bytes_num);
    }
}

pub fn ev_oep_check_fast<S: Stream>(chunk_size: usize, psi_res2: Vec<u128>, stream: S) -> Vec<u128> {
    let rng_ev = AesRng::new();
    let psi_res2s = strict_split(psi_res2, chunk_size);
    let mut res = vec![];

    for psi_res2 in &psi_res2s {
        let reader = BufReader::new(stream.try_clone().unwrap());
        let writer = BufWriter::new(stream.try_clone().unwrap());
        let mut channel = Channel::new(reader, writer);
        let mut sub_ks = ev_oep_check(&mut rng_ev.clone(), &mut channel, &psi_res2);
        res.append(&mut sub_ks);
    }

    res
}

pub fn gb_oep_check_parallel<S: Stream>(
    _chunk_size: usize,
    psi_res1: Vec<u128>,
    streams: &mut Vec<S>,
    permutation: Vec<u128>,
) {
    let n = streams.len();
    let psi_res1s = split_by(psi_res1, n);

    let inv_pmts = split_by(permutation, n);

    psi_res1s
        .into_par_iter()
        .zip(inv_pmts.into_par_iter())
        .zip(streams.into_par_iter())
        .for_each(|((psi_res1, inv_pmt), stream)| {
            let mut rng_gb = AesRng::new();
            let reader = BufReader::new(stream.try_clone().unwrap());
            let writer = BufWriter::new(stream);
            let channel = Channel::new(reader, writer);
            // gb_oep_check(&mut rng_gb, &mut channel, &psi_res1, &inv_pmt);

            let mut track_channle = TrackChannel::new(channel);
            gb_oep_check(&mut rng_gb, &mut track_channle, &psi_res1, &inv_pmt);
            let bytes_num = 256 * track_channle.total_kilobytes() as u64;
            crate::add_cross_shard(bytes_num);
        });
}

pub fn ev_oep_check_parallel<S: Stream>(
    _chunk_size: usize,
    psi_res2: Vec<u128>,
    streams: &mut Vec<S>,
) -> Vec<u128> {
    let n = streams.len();
    let psi_res2s = split_by(psi_res2, n);
    let res: Vec<Vec<u128>> = psi_res2s
        .into_par_iter()
        .zip(streams.into_par_iter())
        .map(|(psi_res2, stream)| {
            let mut rng_ev = AesRng::new();
            let reader = BufReader::new(stream.try_clone().unwrap());
            let writer = BufWriter::new(stream);
            let mut channel = Channel::new(reader, writer);
            ev_oep_check(&mut rng_ev, &mut channel, &psi_res2)
        })
        .collect();

    let res: Vec<u128> = res
        .into_par_iter()
        .flat_map(|vec| vec.into_par_iter())
        .collect();

    res
}

mod tests {

    #[test]
    fn test_oep_check() {
        use super::*;
        use rand::prelude::SliceRandom;
        use rand::Rng;
        use scuttlebutt::{AesRng, Channel};

        let mut rng = rand::thread_rng();
        let n = 1000;
        let sel: u128 = 100;
        let pmt_size: usize = 2000;
        let mut permutation: Vec<u128> = (0..pmt_size as u128).collect();
        permutation.shuffle(&mut rng);

        let mut oep_anno = vec![];
        let zeros = vec![0_u128; sel as usize];
        oep_anno.extend(zeros);
        for _ in 0..(n - sel) {
            oep_anno.push(rng.gen::<u128>());
        }
        oep_anno.shuffle(&mut rng);

        let mut oep_anno1 = vec![];
        let mut oep_anno2 = vec![];
        for i in 0..(n as usize) {
            let share1 = rng.gen();
            let share2 = oep_anno[i].wrapping_sub(share1);
            oep_anno1.push(share1);
            oep_anno2.push(share2);
        }

        let exp_ks = check_in_clear(&oep_anno1, &permutation, &oep_anno2);

        let (sender, receiver) = obtain_tcp_stream();
        std::thread::scope(|s| {
            s.spawn(|| {
                let mut rng_gb = AesRng::new();
                let reader = BufReader::new(sender.try_clone().unwrap());
                let writer = BufWriter::new(sender);
                let mut channel = Channel::new(reader, writer);
                gb_oep_check(
                    &mut rng_gb,
                    &mut channel,
                    &oep_anno1,
                    &permutation[n as usize..].to_vec(),
                );
            });

            let rng_ev = AesRng::new();
            let reader = BufReader::new(receiver.try_clone().unwrap());
            let writer = BufWriter::new(receiver);
            let mut channel = Channel::new(reader, writer);
            let ks = ev_oep_check(&mut rng_ev.clone(), &mut channel, &oep_anno2);

            assert_eq!(ks, exp_ks);
        });
    }

    #[test]
    fn test_fast_oep_check() {
        use super::*;
        use rand::prelude::SliceRandom;
        use rand::Rng;

        let mut rng = rand::thread_rng();
        let n: usize = 1000;
        let chunk_size = 100;
        let sel: usize = 100;
        let pmt_size: usize = 2000;
        let mut permutation: Vec<u128> = (0..pmt_size as u128).collect();
        permutation.shuffle(&mut rng);

        let mut oep_anno = vec![];
        let zeros = vec![0_u128; sel];
        oep_anno.extend(zeros);
        for _ in 0..(n - sel) {
            oep_anno.push(rng.gen::<u128>());
        }
        oep_anno.shuffle(&mut rng);

        let mut oep_anno1 = vec![];
        let mut oep_anno2 = vec![];
        for i in 0..(n as usize) {
            let share1 = rng.gen();
            let share2 = oep_anno[i].wrapping_sub(share1);
            oep_anno1.push(share1);
            oep_anno2.push(share2);
        }

        let exp_ks = check_in_clear(&oep_anno1, &permutation, &oep_anno2);

        let (sender, receiver) = obtain_tcp_stream();
        let (tx, rx) = std::sync::mpsc::channel();

        let thread1 = std::thread::spawn(move || {
            gb_oep_check_fast(chunk_size, oep_anno1, sender, permutation[n..].to_vec());
        });

        let thread2 = std::thread::spawn(move || {
            let res = ev_oep_check_fast(chunk_size, oep_anno2, receiver);
            tx.send(res).unwrap();
        });
        thread1.join().unwrap();
        thread2.join().unwrap();
        let res = rx.recv().unwrap();
        assert_eq!(res, exp_ks);
    }

    #[test]
    fn dbg() {
        use super::*;
        use rand::prelude::SliceRandom;
        use scuttlebutt::{AesRng, Channel};
        use std::{
            io::{BufReader, BufWriter},
            os::unix::net::UnixStream,
        };

        let mut rng = rand::thread_rng();
        let n = 1200;
        let s = 1400;
        let pmt_size = s + n;
        let mut pmt: Vec<u128> = (0..pmt_size as u128).collect();
        pmt.shuffle(&mut rng);
        let psi_res1 = crate::utils::gen_unique_random_unsorted::<u128>(s);
        let psi_res2 = crate::utils::gen_unique_random_unsorted::<u128>(s);

        let (sender, receiver) = UnixStream::pair().unwrap();
        std::thread::scope(|s| {
            s.spawn(|| {
                let mut rng_gb = AesRng::new();
                let reader = BufReader::new(sender.try_clone().unwrap());
                let writer = BufWriter::new(sender);
                let mut channel = Channel::new(reader, writer);
                gb_oep_check(&mut rng_gb, &mut channel, &psi_res1, &pmt[n..].to_vec());
            });

            let rng_ev = AesRng::new();
            let reader = BufReader::new(receiver.try_clone().unwrap());
            let writer = BufWriter::new(receiver);
            let mut channel = Channel::new(reader, writer);
            let ks = ev_oep_check(&mut rng_ev.clone(), &mut channel, &psi_res2);

            let exp_ks = check_in_clear(&psi_res1, &pmt, &psi_res2);
            assert_eq!(ks, exp_ks);
        });
    }
}
