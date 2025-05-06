use ark_bls12_381::{g1::Config, Bls12_381, Fr, G1Affine as G1, G2Affine as G2};
use ark_ec::pairing::Pairing;
use ark_ec::short_weierstrass::Projective;
use ark_serialize::CanonicalDeserialize;
use ark_serialize::CanonicalSerialize;
use ark_std::UniformRand;
use crypto_hash::digest;
use crypto_hash::Algorithm;
use kzg::KZG;
use oblivious_transfer_protocols::{
    base_ot::simplest_ot::{OneOfTwoROTSenderKeys, ROTReceiverKeys, ROTSenderSetup},
    configs::OTConfig,
};
use opprf::{alice_opprf, bob_opprf};
use poly::fft_interpolate_with_subproduct_tree;
use poly::Poly;
use rand::seq::SliceRandom;
use rand::{rngs::StdRng, Rng};
use rayon::iter::IndexedParallelIterator;
use rayon::iter::IntoParallelIterator;
use rayon::iter::IntoParallelRefIterator;
use rayon::iter::IntoParallelRefMutIterator;
use rayon::iter::ParallelIterator;
use rayon::ThreadPoolBuilder;
use std::collections::HashMap;
use std::net::TcpListener;
use std::net::TcpStream;
use std::thread;
use std::time::Duration;
use subproduct_tree::SubProductTree;
use utils::receive_data_by_stream;
use utils::send_data_by_stream;

use crate::garbled_circuit::oep_check::ev_oep_check_fast;
use crate::garbled_circuit::oep_check::ev_oep_check_parallel;
use crate::garbled_circuit::oep_check::gb_oep_check_fast;
use crate::garbled_circuit::oep_check::gb_oep_check_parallel;
use crate::garbled_circuit::psi_check::ev_psi_check_fast;
use crate::garbled_circuit::psi_check::ev_psi_check_parallel;
use crate::garbled_circuit::psi_check::gb_psi_check_fast;
use crate::garbled_circuit::psi_check::gb_psi_check_parallel;
use crate::oep::*;
use crate::relation::copy_duplicate;
use crate::tpch::Stream;
use crate::utils::fr_xor;
use crate::utils::points_to_u128;
use crate::utils::run_consensus;
use crate::utils::{get_fixed_rng, points_from_num};
use crate::*;

pub mod kzg;
pub mod opprf;
pub mod poly;
pub mod subproduct_tree;
pub mod utils;

pub const OT_KEY_SIZE: u16 = 128;
pub const YES_FLAG: u8 = 1;
pub const NO_FLAG: u8 = 0;
pub const SHARD_BASE_PORT: u16 = 9000;

fn do_1_of_2_base_ot<const KEY_SIZE: u16>(
    rng: &mut StdRng,
    base_ot_cnt: u16,
    b: &G1,
) -> (Vec<u16>, OneOfTwoROTSenderKeys, ROTReceiverKeys) {
    let ot_config = OTConfig::new_2_message(base_ot_cnt).unwrap();
    let (base_ot_sender_setup, s) = ROTSenderSetup::new(rng, ot_config, b);

    let base_ot_choices = (0..base_ot_cnt)
        .map(|_| u16::rand(rng) % 2)
        .collect::<Vec<_>>();
    let (base_ot_receiver_keys, r) =
        ROTReceiverKeys::new::<_, _, KEY_SIZE>(rng, ot_config, base_ot_choices.clone(), s, b)
            .unwrap();

    let base_ot_sender_keys =
        OneOfTwoROTSenderKeys::try_from(base_ot_sender_setup.derive_keys::<KEY_SIZE>(r).unwrap())
            .unwrap();
    (base_ot_choices, base_ot_sender_keys, base_ot_receiver_keys)
}

// TODO: this setup can be done off-line and then we can retrieve the keys directly
pub fn base_ot_setup(base_ot_cnt: u16) -> (Vec<u16>, OneOfTwoROTSenderKeys, ROTReceiverKeys) {
    let mut rng = get_fixed_rng();
    let b = G1::rand(&mut rng);
    do_1_of_2_base_ot::<OT_KEY_SIZE>(&mut rng, base_ot_cnt, &b)
}

pub fn setup_kzg(max_deg: usize) -> KZG<Bls12_381> {
    let mut rng = get_fixed_rng();
    let mut kzg = KZG::<Bls12_381>::new(G1::rand(&mut rng), G2::rand(&mut rng), max_deg);
    let s = Fr::rand(&mut rng);
    kzg.setup(s);
    kzg
}

fn anno_xor_r(vs: Vec<u64>, r: u128) -> Vec<Fr> {
    let vs_p: Vec<u128> = vs.into_par_iter().map(|v| (v as u128) ^ r).collect();
    points_from_num(vs_p)
}

fn sender_multi_oprf<S: Stream>(
    xs: &Vec<Vec<u64>>,
    stream: &mut S,
    self_id: u16,
    debug: bool,
    ys_len_larger: bool,
) -> Vec<(Vec<u128>, u128)> {
    let mut oprf_info = vec![];
    for i in 0..xs.len() {
        let (xs_p, r) = alice_opprf(stream, &xs[i], ys_len_larger);
        oprf_info.push((xs_p, r));
    }

    // consensus oprf info
    let bytes = bincode::serialize(&oprf_info).unwrap();
    let dig = digest(Algorithm::SHA256, &bytes);
    if !debug {
        run_consensus(dig, self_id);
    }
    oprf_info
}

fn receiver_multi_oprf<S: Stream>(
    ys: &Vec<Vec<u64>>,
    stream: &mut S,
    self_id: u16,
    debug: bool,
    ys_len_larger: bool,
) -> Vec<Vec<u128>> {
    let mut oprf_info = vec![];
    for i in 0..ys.len() {
        let ys_p = bob_opprf(stream, &ys[i], ys_len_larger);
        oprf_info.push(ys_p);
    }

    // consensus on oprf res
    let bytes = bincode::serialize(&oprf_info).unwrap();
    let dig = digest(Algorithm::SHA256, &bytes);
    if !debug {
        run_consensus(dig, self_id);
    }

    oprf_info
}

const TEST_THREAD_NUM: usize = 4;

// sender do interpolation for two polys
fn sender_poly<S: Stream>(
    xs: &Vec<Fr>,
    xs_p: &Vec<Fr>,
    vs_p: &Vec<Fr>,
    tree: &SubProductTree<Fr>, // built by xs
    stream: &mut S,
) {
    let timer = howlong::ProcessCPUTimer::new();
    // interpolation for (x, x_p), (x, v_p)

    let pool1 = ThreadPoolBuilder::new().num_threads(TEST_THREAD_NUM).build().unwrap();

    let poly_x = pool1.install(|| {fft_interpolate_with_subproduct_tree(&xs, &xs_p, tree)});

    let pool2 = ThreadPoolBuilder::new().num_threads(TEST_THREAD_NUM).build().unwrap();
    let poly_v = pool2.install(|| {fft_interpolate_with_subproduct_tree(&xs, &vs_p, tree)});
    let t = timer.elapsed().real.as_micros() as u64;
    println!("sender interpolate time: {} ms", t / 1000);

    // send two poly to receiver
    let mut poly_x_bytes: Vec<u8> = vec![];
    poly_x.serialize_uncompressed(&mut poly_x_bytes).unwrap();
    let mut poly_v_bytes: Vec<u8> = vec![];
    poly_v.serialize_uncompressed(&mut poly_v_bytes).unwrap();
    send_data_by_stream(stream, &poly_x_bytes, false);
    send_data_by_stream(stream, &poly_v_bytes, false);
}

// receive two poly from sender
fn receiver_poly<S: Stream>(stream: &mut S) -> (Poly<Fr>, Poly<Fr>) {
    // get poly_x and poly_v
    let poly_x_bytes = receive_data_by_stream(stream);
    let poly_x: Poly<Fr> = Poly::deserialize_uncompressed(&*poly_x_bytes).unwrap();
    let poly_v_bytes = receive_data_by_stream(stream);
    let poly_v: Poly<Fr> = Poly::deserialize_uncompressed(&*poly_v_bytes).unwrap();
    (poly_x, poly_v)
}

fn receive_proof<S: Stream>(mut stream: S) -> (usize, Vec<Fr>, G1, Vec<Fr>, G1) {
    let idx_bytes = receive_data_by_stream(&mut stream);
    let ys_pp_bytes = receive_data_by_stream(&mut stream);
    let pi_x_bytes = receive_data_by_stream(&mut stream);
    let vs_pp_bytes = receive_data_by_stream(&mut stream);
    let pi_v_bytes = receive_data_by_stream(&mut stream);

    let idx: usize = bincode::deserialize(&idx_bytes).unwrap();
    let ys_pp: Vec<Fr> = Vec::<Fr>::deserialize_uncompressed(&*ys_pp_bytes).unwrap();
    let pi_x: G1 = G1::deserialize_uncompressed(&*pi_x_bytes).unwrap();
    let vs_pp: Vec<Fr> = Vec::<Fr>::deserialize_uncompressed(&*vs_pp_bytes).unwrap();
    let pi_v: G1 = G1::deserialize_uncompressed(&*pi_v_bytes).unwrap();
    (idx, ys_pp, pi_x, vs_pp, pi_v)
}

fn listen_to_receive_proof(
    self_id: u16,
    threshold: usize,
) -> Vec<(usize, Vec<Fr>, G1, Vec<Fr>, G1)> {
    let addr = format!("127.0.0.1:{}", SHARD_BASE_PORT + self_id);
    let listener = TcpListener::bind(addr).unwrap();
    let mut proof_info = vec![];
    for stream in listener.incoming() {
        let stream = stream.unwrap();
        let proof = receive_proof(stream);
        proof_info.push(proof);
        if proof_info.len() >= threshold {
            break;
        }
    }
    proof_info
}

fn broadcast_proof(self_id: u16, ys_pp: &Vec<Fr>, pi_x: G1, vs_pp: &Vec<Fr>, pi_v: G1) {
    let base = self_id / N;
    let self_id_mod_n = self_id % N;
    let mut targets_mod_n: Vec<u16> = (0..N).collect();
    targets_mod_n.retain(|x| *x != self_id_mod_n);
    let targets: Vec<u16> = targets_mod_n.into_iter().map(|x| base * N + x).collect();
    targets.par_iter().for_each(|target_port| {
        let target_addr = format!("127.0.0.1:{}", SHARD_BASE_PORT + target_port);
        loop {
            match TcpStream::connect(target_addr.clone()) {
                Ok(mut stream) => {
                    let idx_bytes = bincode::serialize(&(self_id_mod_n as usize)).unwrap();
                    let mut ys_pp_bytes: Vec<u8> = vec![];
                    ys_pp.serialize_uncompressed(&mut ys_pp_bytes).unwrap();
                    let mut pi_x_bytes: Vec<u8> = vec![];
                    pi_x.serialize_uncompressed(&mut pi_x_bytes).unwrap();
                    let mut vs_pp_bytes: Vec<u8> = vec![];
                    vs_pp.serialize_uncompressed(&mut vs_pp_bytes).unwrap();
                    let mut pi_v_bytes: Vec<u8> = vec![];
                    pi_v.serialize_uncompressed(&mut pi_v_bytes).unwrap();
                    send_data_by_stream(&mut stream, &idx_bytes, true);
                    send_data_by_stream(&mut stream, &ys_pp_bytes, true);
                    send_data_by_stream(&mut stream, &pi_x_bytes, true);
                    send_data_by_stream(&mut stream, &vs_pp_bytes, true);
                    send_data_by_stream(&mut stream, &pi_v_bytes, true);
                    break;
                }
                Err(_) => {
                    thread::sleep(Duration::from_millis(200));
                }
            }
        }
    });
}

pub fn batch_psi_anno_sender<S: Stream>(
    xs: Vec<Vec<u64>>,
    vs: Vec<Vec<u64>>,
    kzg: &KZG<Bls12_381>,        // should be a vec
    send_stream: &mut S, // stream for oprf and sending poly
    xs_com_infos: &Vec<Vec<G1>>,
    trees: &Vec<SubProductTree<Fr>>, // built over xs
    debug: bool,
    self_id: u16,
    ys_len_larger: bool,  // should be a vec
    receiver_size: usize, // should be a vec
    chunk_size: usize,    // should be a vec
) -> Vec<Vec<u128>> {
    assert_eq!(xs.len(), vs.len());
    assert_eq!(xs.len(), xs_com_infos.len());
    assert_eq!(xs.len(), trees.len());

    let self_id_mod_n = self_id % N;
    let query_num = xs.len();
    // sender oprf
    let oprf_info = sender_multi_oprf(&xs, send_stream, self_id, debug, ys_len_larger);
    let mut xses = vec![];
    let mut rs = vec![];
    let mut commits_x = vec![];
    let mut commits_v = vec![];
    let mut own_xs_p = vec![];
    let mut own_vs_p = vec![];
    for i in 0..query_num {
        let (xs_p, r) = oprf_info.get(i).unwrap();
        let xs = points_from_num(xs.get(i).unwrap().to_vec());
        xses.push(xs);
        let xs_p = points_from_num(xs_p.to_vec());
        let vs_p = anno_xor_r(vs.get(i).unwrap().to_vec(), *r);
        // C_x
        let commit_x = kzg.commit_by_pre_info_g1(&xs_p, &xs_com_infos.get(i).unwrap());
        // C_v
        let commit_v = kzg.commit_by_pre_info_g1(&vs_p, &xs_com_infos.get(i).unwrap());
        commits_x.push(commit_x);
        commits_v.push(commit_v);
        rs.push(*r);
        if i == self_id_mod_n as usize {
            own_xs_p = xs_p;
            own_vs_p = vs_p;
        }
    }

    // consensus for C_x and C_v
    let mut c_x_bytes: Vec<u8> = vec![];
    commits_x.serialize_uncompressed(&mut c_x_bytes).unwrap();
    let mut c_v_bytes: Vec<u8> = vec![];
    commits_v.serialize_uncompressed(&mut c_v_bytes).unwrap();

    send_data_by_stream(send_stream, &c_x_bytes, false);
    send_data_by_stream(send_stream, &c_v_bytes, false);

    c_x_bytes.append(&mut c_v_bytes);
    let dig = digest(Algorithm::SHA256, &c_x_bytes);
    if !debug {
        run_consensus(dig, self_id);
    }

    // for prover, do interpolation and send to receiver
    if self_id_mod_n < query_num as u16 {
        sender_poly(
            &xses.get(self_id_mod_n as usize).unwrap(),
            &own_xs_p,
            &own_vs_p,
            trees.get(self_id_mod_n as usize).unwrap(),
            send_stream,
        );
    }

    // run circuit
    let mut rng = get_fixed_rng();
    let mut anno_share1s = vec![];

    for _ in 0..query_num {
        let mut anno_share1 = vec![];
        for _ in 0..receiver_size {
            anno_share1.push(rng.gen::<u128>());
        }
        anno_share1s.push(anno_share1);
    }

    let data = (rs, &anno_share1s);
    let bytes = bincode::serialize(&data).unwrap();
    let dig = digest(Algorithm::SHA256, &bytes);
    if !debug {
        run_consensus(dig, self_id);
    }

    let timer = howlong::ProcessCPUTimer::new();
    for (r, anno_share1) in data.0.into_iter().zip(data.1.into_iter()) {
        gb_psi_check_fast(chunk_size, anno_share1.to_vec(), r, send_stream);
    }
    let t = timer.elapsed().real.as_micros() as u64;
    println!("sender circuit time: {} ms", t / 1000);
    anno_share1s
}

pub fn batch_psi_anno_receiver<S: Stream>(
    ys_orignial: &Vec<Vec<u32>>, // may contain duplicate
    has_duplicate: bool,         // only for the target query
    ys_num: Vec<Vec<u64>>,       // no duplicate
    kzg: &KZG<Bls12_381>,
    rec_stream: &mut S,      // stream for oprf and receiving poly
    trees: &Vec<SubProductTree<Fr>>, // built over the target query's ys
    veri_info: &Vec<Vec<G1>>,
    z_commit: Vec<<Bls12_381 as Pairing>::G2Affine>,
    chunk_size: usize, // should be a vec
    self_id: u16,
    ys_len_larger: bool, // should be a vec
    debug: bool,
) -> Vec<Vec<u128>> {
    assert_eq!(ys_orignial.len(), ys_num.len());
    assert_eq!(ys_orignial.len(), trees.len());
    assert_eq!(ys_orignial.len(), veri_info.len());
    assert_eq!(ys_orignial.len(), z_commit.len());

    // start handler for collecting proof from brothers
    let handle = thread::spawn(move || listen_to_receive_proof(self_id, N as usize - 1));

    let self_id_mod_n = self_id % N;
    let query_num = ys_num.len();
    // receiver oprf
    let oprf_info = receiver_multi_oprf(&ys_num, rec_stream, self_id, debug, ys_len_larger);
    let ys = points_from_num(ys_num.get(self_id_mod_n as usize).unwrap().to_vec());
    let ys_ps: Vec<Vec<Fr>> = oprf_info.into_iter().map(|x| points_from_num(x)).collect();

    let c_x_bytes = receive_data_by_stream(rec_stream);
    let c_v_bytes = receive_data_by_stream(rec_stream);

    let commits_x: Vec<Projective<Config>> =
        Vec::<Projective<Config>>::deserialize_uncompressed(&*c_x_bytes).unwrap();
    let commits_v: Vec<Projective<Config>> =
        Vec::<Projective<Config>>::deserialize_uncompressed(&*c_v_bytes).unwrap();

    let mut ys_pps = vec![];
    let mut vs_pps = vec![];
    if self_id_mod_n < query_num as u16 {
        // receive polys from sender
        let (poly_x, poly_v) = receiver_poly(rec_stream);

        // gen_proof
        let tree = trees.get(self_id_mod_n as usize).unwrap();
        let (ys_pp, pi_x) = kzg.open_multi_with_subproduct_tree(&poly_x, &ys, tree);
        let (vs_pp, pi_v) = kzg.open_multi_with_subproduct_tree(&poly_v, &ys, tree);
        // send proof to all brothers
        broadcast_proof(self_id, &ys_pp, pi_x, &vs_pp, pi_v);
        ys_pps.push(ys_pp);
        vs_pps.push(vs_pp);
    }
    // receive proof from all brothers & verify
    let proofs_info = handle.join().expect("thread panicked");
    for (idx, ys_pp, pi_x, vs_pp, pi_v) in proofs_info {
        let _res1 = kzg.fast_verify_multi(
            &ys_pp,
            commits_x.get(idx).unwrap().clone(),
            pi_x,
            veri_info.get(idx).unwrap(),
            z_commit.get(idx).unwrap().clone(),
        );
        let _res2 = kzg.fast_verify_multi(
            &vs_pp,
            commits_v.get(idx).unwrap().clone(),
            pi_v,
            veri_info.get(idx).unwrap(),
            z_commit.get(idx).unwrap().clone(),
        );
        ys_pps.push(ys_pp);
        vs_pps.push(vs_pp);
    }

    let ys_hats: Vec<Vec<u128>> = ys_ps
        .into_iter()
        .zip(ys_pps.into_iter())
        .map(|(ys_p, ys_pp)| {
            points_to_u128(
                ys_p.into_iter()
                    .zip(ys_pp.into_iter())
                    .map(|(y_p, y_pp)| fr_xor(&y_p, &y_pp))
                    .collect(),
            )
        })
        .collect();
    let vs_pp_u128s: Vec<Vec<u128>> = vs_pps
        .into_iter()
        .map(|vs_pp| points_to_u128(vs_pp))
        .collect();

    let mut vs_pp_ys_hat = vec![];
    for (((ys_num, ys_hat), vs_pp), ys_orig) in ys_num
        .into_iter()
        .zip(ys_hats.into_iter())
        .zip(vs_pp_u128s.into_iter())
        .zip(ys_orignial.iter())
    {
        if has_duplicate {
            let mut map = HashMap::new();
            for (i, ele) in ys_num.iter().enumerate() {
                map.insert(*ele as u32, (vs_pp[i], ys_hat[i]));
            }
            let (new_vs_pp, new_ys_hat) = copy_duplicate::<u128>(ys_orig, &map);
            vs_pp_ys_hat.push((new_vs_pp, new_ys_hat));
        } else {
            vs_pp_ys_hat.push((vs_pp, ys_hat));
        }
    }

    // run consensus for circuit input
    let bytes = bincode::serialize(&vs_pp_ys_hat).unwrap();
    let dig = digest(Algorithm::SHA256, &bytes);
    if !debug {
        run_consensus(dig, self_id);
    }

    let timer = howlong::ProcessCPUTimer::new();
    let mut anno_share2s = vec![];
    for (vs_pp, ys_hat) in vs_pp_ys_hat {
        let anno2 = ev_psi_check_fast(chunk_size, vs_pp, ys_hat, rec_stream);
        anno_share2s.push(anno2);
    }
    let t = timer.elapsed().real.as_micros() as u64;
    println!("receiver circuit time: {} ms", t / 1000);

    anno_share2s
}

use std::sync::Mutex;

pub fn batch_psi_anno_sender_parallel<S: Stream>(
    xs: Vec<Vec<u64>>,
    vs: Vec<Vec<u64>>,
    kzg: &KZG<Bls12_381>,        // should be a vec
    send_stream: &mut S, // stream for oprf and sending poly
    xs_com_infos: &Vec<Vec<G1>>,
    trees: &Vec<SubProductTree<Fr>>, // built over xs
    debug: bool,
    self_id: u16,
    ys_len_larger: bool,  // should be a vec
    receiver_size: usize, // should be a vec
    mut psi_streams: Vec<S>,
) -> Vec<Vec<u128>> {
    assert_eq!(xs.len(), vs.len());
    assert_eq!(xs.len(), xs_com_infos.len());
    assert_eq!(xs.len(), trees.len());

    let self_id_mod_n = self_id % N;
    let query_num = xs.len();
    // sender oprf
    let oprf_info = sender_multi_oprf(&xs, send_stream, self_id, debug, ys_len_larger);

    let mut xses = vec![];
    let mut rs = vec![];
    let mut commits_x = vec![];
    let mut commits_v = vec![];
    // let mut own_xs_p = vec![];
    // let mut own_vs_p = vec![];

    let own_xs_p = Mutex::new(vec![]);
    let own_vs_p = Mutex::new(vec![]);

    let info: Vec<(Vec<Fr>, u128, Projective<Config>, Projective<Config>)> = oprf_info
        .into_par_iter()
        .zip(xs.into_par_iter())
        .zip(vs.into_par_iter())
        .zip(xs_com_infos.into_par_iter())
        .zip((0..query_num).into_par_iter())
        .map(|(((((xs_p, r), xs), vs), xs_info), idx)| {
            let xs = points_from_num(xs);
            let xs_p = points_from_num(xs_p);
            let vs_p = anno_xor_r(vs, r);
            let commit_x = kzg.commit_by_pre_info_g1(&xs_p, xs_info);
            let commit_v = kzg.commit_by_pre_info_g1(&vs_p, xs_info);
            if idx == self_id_mod_n as usize {
                let mut own_xs_p_guard = own_xs_p.lock().unwrap();
                *own_xs_p_guard = xs_p;
                let mut own_vs_p_guard = own_vs_p.lock().unwrap();
                *own_vs_p_guard = vs_p;
            }
            (xs, r, commit_x, commit_v)
        })
        .collect();
    let own_xs_p = own_xs_p.lock().unwrap();
    let own_vs_p = own_vs_p.lock().unwrap();

    for (xs, r, commit_x, commit_v) in info {
        xses.push(xs);
        rs.push(r);
        commits_x.push(commit_x);
        commits_v.push(commit_v);
    }

    // consensus for C_x and C_v
    let mut c_x_bytes: Vec<u8> = vec![];
    commits_x.serialize_uncompressed(&mut c_x_bytes).unwrap();
    let mut c_v_bytes: Vec<u8> = vec![];
    commits_v.serialize_uncompressed(&mut c_v_bytes).unwrap();

    send_data_by_stream(send_stream, &c_x_bytes, false);
    send_data_by_stream(send_stream, &c_v_bytes, false);

    c_x_bytes.append(&mut c_v_bytes);
    let dig = digest(Algorithm::SHA256, &c_x_bytes);
    if !debug {
        run_consensus(dig, self_id);
    }

    // for prover, do interpolation and send to receiver
    if self_id_mod_n < query_num as u16 {
        sender_poly(
            &xses.get(self_id_mod_n as usize).unwrap(),
            &own_xs_p,
            &own_vs_p,
            trees.get(self_id_mod_n as usize).unwrap(),
            send_stream,
        );
    }

    // run circuit
    let mut rng = get_fixed_rng();
    let mut anno_share1s = vec![];

    for _ in 0..query_num {
        let mut anno_share1 = vec![];
        for _ in 0..receiver_size {
            anno_share1.push(rng.gen::<u128>());
        }
        anno_share1s.push(anno_share1);
    }

    let data = (rs, anno_share1s.clone());
    let bytes = bincode::serialize(&data).unwrap();
    let dig = digest(Algorithm::SHA256, &bytes);
    if !debug {
        run_consensus(dig, self_id);
    }

    let timer = howlong::ProcessCPUTimer::new();

    data.0.into_iter()
            .zip(data.1.into_iter())
            .for_each(|(r, anno_share1)| {
                gb_psi_check_parallel(anno_share1, r, &mut psi_streams);
            });


    let t = timer.elapsed().real.as_micros() as u64;
    println!("sender circuit time: {} ms", t / 1000);
    anno_share1s
}

pub fn batch_psi_anno_receiver_parallel<S: Stream>(
    ys_orignial: &Vec<Vec<u32>>, // may contain duplicate
    has_duplicate: bool,         // only for the target query
    ys_num: Vec<Vec<u64>>,       // no duplicate
    kzg: &KZG<Bls12_381>,
    rec_stream: &mut S,      // stream for oprf and receiving poly
    trees: &Vec<SubProductTree<Fr>>, // built over the target query's ys
    veri_info: &Vec<Vec<G1>>,
    z_commit: Vec<<Bls12_381 as Pairing>::G2Affine>,
    self_id: u16,
    ys_len_larger: bool, // should be a vec
    debug: bool,
    mut psi_streams: Vec<S>,
) -> Vec<Vec<u128>> {
    assert_eq!(ys_orignial.len(), ys_num.len());
    assert_eq!(ys_orignial.len(), trees.len());
    assert_eq!(ys_orignial.len(), veri_info.len());
    assert_eq!(ys_orignial.len(), z_commit.len());

    // start handler for collecting proof from brothers
    let handle = thread::spawn(move || listen_to_receive_proof(self_id, N as usize - 1));

    let self_id_mod_n = self_id % N;
    let query_num = ys_num.len();
    // receiver oprf
    let oprf_info = receiver_multi_oprf(&ys_num, rec_stream, self_id, debug, ys_len_larger);
    let ys = points_from_num(ys_num.get(self_id_mod_n as usize).unwrap().to_vec());
    let ys_ps: Vec<Vec<Fr>> = oprf_info
        .into_par_iter()
        .map(|x| points_from_num(x))
        .collect();

    let c_x_bytes = receive_data_by_stream(rec_stream);
    let c_v_bytes = receive_data_by_stream(rec_stream);

    let commits_x: Vec<Projective<Config>> =
        Vec::<Projective<Config>>::deserialize_uncompressed(&*c_x_bytes).unwrap();
    let commits_v: Vec<Projective<Config>> =
        Vec::<Projective<Config>>::deserialize_uncompressed(&*c_v_bytes).unwrap();

    let mut ys_pps = vec![];
    let mut vs_pps = vec![];
    if self_id_mod_n < query_num as u16 {
        // receive polys from sender
        let (poly_x, poly_v) = receiver_poly(rec_stream);

        // gen_proof
        let tree = trees.get(self_id_mod_n as usize).unwrap();
        let (ys_pp, pi_x) = kzg.open_multi_with_subproduct_tree(&poly_x, &ys, tree);
        let (vs_pp, pi_v) = kzg.open_multi_with_subproduct_tree(&poly_v, &ys, tree);
        // send proof to all brothers
        broadcast_proof(self_id, &ys_pp, pi_x, &vs_pp, pi_v);
        ys_pps.push(ys_pp);
        vs_pps.push(vs_pp);
    }
    // receive proof from all brothers & verify
    let proofs_info = handle.join().expect("thread panicked");
    for (idx, ys_pp, pi_x, vs_pp, pi_v) in proofs_info {
        let _res1 = kzg.fast_verify_multi(
            &ys_pp,
            commits_x.get(idx).unwrap().clone(),
            pi_x,
            veri_info.get(idx).unwrap(),
            z_commit.get(idx).unwrap().clone(),
        );
        let _res2 = kzg.fast_verify_multi(
            &vs_pp,
            commits_v.get(idx).unwrap().clone(),
            pi_v,
            veri_info.get(idx).unwrap(),
            z_commit.get(idx).unwrap().clone(),
        );
        ys_pps.push(ys_pp);
        vs_pps.push(vs_pp);
    }

    let ys_hats: Vec<Vec<u128>> = ys_ps
        .into_par_iter()
        .zip(ys_pps.into_par_iter())
        .map(|(ys_p, ys_pp)| {
            points_to_u128(
                ys_p.into_par_iter()
                    .zip(ys_pp.into_par_iter())
                    .map(|(y_p, y_pp)| fr_xor(&y_p, &y_pp))
                    .collect(),
            )
        })
        .collect();
    let vs_pp_u128s: Vec<Vec<u128>> = vs_pps
        .into_par_iter()
        .map(|vs_pp| points_to_u128(vs_pp))
        .collect();

    let vs_pp_ys_hat: Vec<(Vec<u128>, Vec<u128>)> = ys_num
        .into_par_iter()
        .zip(ys_hats.into_par_iter())
        .zip(vs_pp_u128s.into_par_iter())
        .zip(ys_orignial.par_iter())
        .map(|(((ys_num, ys_hat), vs_pp), ys_orig)| {
            if has_duplicate {
                let mut map = HashMap::new();
                for (i, ele) in ys_num.iter().enumerate() {
                    map.insert(*ele as u32, (vs_pp[i], ys_hat[i]));
                }
                let (new_vs_pp, new_ys_hat) = copy_duplicate::<u128>(ys_orig, &map);
                (new_vs_pp, new_ys_hat)
            } else {
                (vs_pp, ys_hat)
            }
        })
        .collect();

    // run consensus for circuit input
    let bytes = bincode::serialize(&vs_pp_ys_hat).unwrap();
    let dig = digest(Algorithm::SHA256, &bytes);
    if !debug {
        run_consensus(dig, self_id);
    }

    let timer = howlong::ProcessCPUTimer::new();

    // vec![vs_pp; N]; vec![ys_pp; N]; vec![stream, N]
    // assert_eq!(vs_pp_ys_hat.len(), psi_streams.len());
    let anno_share2s: Vec<Vec<u128>> = vs_pp_ys_hat
        .into_iter()
        .map(|(vs_pp, ys_hat)| {
            let res = ev_psi_check_parallel(vs_pp, ys_hat, &mut psi_streams);
            res
        })
        .collect();

    let t = timer.elapsed().real.as_micros() as u64;
    println!("receiver circuit time: {} ms", t / 1000);

    anno_share2s
}

pub fn intra_psi_anno_sender<S: Stream>(
    xs: Vec<u64>, // all xs for one psi
    vs: Vec<u64>, // all anno for one psi
    kzg: &KZG<Bls12_381>,
    send_stream: &mut S, // stream for oprf and sending poly
    xs_com_info: &Vec<G1>,
    tree: &SubProductTree<Fr>, // built over xs
    debug: bool,
    self_id: u16,
    prover_id: u16,
    ys_len_larger: bool,
    receiver_size: usize,
    chunk_size: usize,
) -> Vec<u128> {
    let self_id_mod_n = self_id % N;
    // sender oprf
    let mut xses = vec![xs];
    let mut oprf_info = sender_multi_oprf(&xses, send_stream, self_id, debug, ys_len_larger);
    let xs = xses.remove(0);
    let xs = points_from_num(xs);

    let (xs_p, r) = oprf_info.remove(0);

    let xs_p = points_from_num(xs_p);
    let vs_p = anno_xor_r(vs, r);

    // compute commitment and run consensus
    // C_x
    let commitment_x = kzg.commit_by_pre_info_g1(&xs_p, &xs_com_info);
    // C_v
    let commitment_v = kzg.commit_by_pre_info_g1(&vs_p, &xs_com_info);

    // consensus for C_x and C_v
    let mut c_x_bytes: Vec<u8> = vec![];
    commitment_x.serialize_uncompressed(&mut c_x_bytes).unwrap();
    let mut c_v_bytes: Vec<u8> = vec![];
    commitment_v.serialize_uncompressed(&mut c_v_bytes).unwrap();

    send_data_by_stream(send_stream, &c_x_bytes, true);
    send_data_by_stream(send_stream, &c_v_bytes, true);

    c_x_bytes.append(&mut c_v_bytes);
    let dig = digest(Algorithm::SHA256, &c_x_bytes);
    if !debug {
        run_consensus(dig, self_id);
    }

    // for prover, do interpolation and send to receiver
    if prover_id == self_id_mod_n {
        sender_poly(&xs, &xs_p, &vs_p, tree, send_stream);
    }

    // run circuit
    let mut rng = get_fixed_rng();
    let mut anno_share1 = vec![];
    for _ in 0..receiver_size {
        anno_share1.push(rng.gen::<u128>());
    }

    let data = (&anno_share1, r);
    let bytes = bincode::serialize(&data).unwrap();
    let dig = digest(Algorithm::SHA256, &bytes);
    if !debug {
        run_consensus(dig, self_id);
    }

    let timer3 = howlong::ProcessCPUTimer::new();
    gb_psi_check_fast(chunk_size, anno_share1.clone(), r, send_stream);
    // gb_psi_check_parallel(chunk_size, anno_share1.to_vec(), r, circuit_sen_streams);
    let t = timer3.elapsed().real.as_micros() as u64;
    println!("sender psi circuit time: {} ms", t / 1000);
    return anno_share1;
}

pub fn intra_psi_anno_receiver<S: Stream>(
    ys_orignial: &Vec<u32>, // may contain duplicate
    has_duplicate: bool,
    ys_num: Vec<u64>, // no duplicate
    kzg: &KZG<Bls12_381>,
    rec_stream: &mut S, // stream for oprf and receiving poly
    tree: &SubProductTree<Fr>,  // built over ys
    veri_info: &Vec<Vec<G1>>,
    z_commit: Vec<<Bls12_381 as Pairing>::G2Affine>,
    chunk_size: usize,
    self_id: u16,
    prover_id: u16,
    ys_len_larger: bool,
    debug: bool,
    is_partitioned: bool,
) -> Vec<u128> {
    let timer0 = howlong::ProcessCPUTimer::new();
    let self_id_mod_n = self_id % N;
    let handle = if prover_id != self_id_mod_n {
        thread::spawn(move || listen_to_receive_proof(self_id, 1))
    } else {
        thread::spawn(move || vec![])
    };

    // receiver oprf
    let mut yses = vec![ys_num.clone()];
    let mut oprf_info = receiver_multi_oprf(&yses, rec_stream, self_id, debug, ys_len_larger);
    let ys = points_from_num(yses.remove(0));
    let ys_p = points_from_num(oprf_info.remove(0));

    let c_x_bytes = receive_data_by_stream(rec_stream);
    let c_v_bytes = receive_data_by_stream(rec_stream);

    let commitment_x: Projective<Config> =
        Projective::deserialize_uncompressed(&*c_x_bytes).unwrap();
    let commitment_v: Projective<Config> =
        Projective::deserialize_uncompressed(&*c_v_bytes).unwrap();

    let (ys_pp, vs_pp) = if is_partitioned {
        todo!()
    } else {
        if prover_id == self_id_mod_n {
            let _proofs_info = handle.join().expect("thread panicked");
            let (poly_x, poly_v) = receiver_poly(rec_stream);
            // gen proof
            let timer = howlong::ProcessCPUTimer::new();
            let pool1 = ThreadPoolBuilder::new().num_threads(TEST_THREAD_NUM).build().unwrap();
            let (ys_pp, pi_x) = pool1.install(|| {
                kzg.open_multi_with_subproduct_tree(&poly_x, &ys, tree)
            });
            let pool2 = ThreadPoolBuilder::new().num_threads(TEST_THREAD_NUM).build().unwrap();
            let (vs_pp, pi_v) = pool2.install(|| {
                kzg.open_multi_with_subproduct_tree(&poly_v, &ys, tree)
            });
            let t = timer.elapsed().real.as_micros() as u64;
            println!("proof gen time: {} ms", t / 1000);

            let timer2 = howlong::ProcessCPUTimer::new();
            broadcast_proof(self_id, &ys_pp, pi_x, &vs_pp, pi_v);
            let t = timer2.elapsed().real.as_micros() as u64;
            println!("broadcast proof time: {} ms", t / 1000);
            (ys_pp, vs_pp)
        } else {
            let timer = howlong::ProcessCPUTimer::new();
            let mut proofs_info = handle.join().expect("thread panicked");
            let (_, ys_pp, pi_x, vs_pp, pi_v) = proofs_info.remove(0);
            let t = timer.elapsed().real.as_micros() as u64;
            println!("receive proof time: {} ms", t / 1000);

            let _res1 = kzg.fast_verify_multi(
                &ys_pp,
                commitment_x,
                pi_x,
                veri_info.get(0).unwrap(),        // as not partitioned
                z_commit.get(0).unwrap().clone(), // as not partitioned
            );
            let _res2 = kzg.fast_verify_multi(
                &vs_pp,
                commitment_v,
                pi_v,
                veri_info.get(0).unwrap(),        // as not partitioned
                z_commit.get(0).unwrap().clone(), // as not partitioned
            );
            (ys_pp, vs_pp)
        }
    };

    let ys_hat: Vec<Fr> = ys_p
        .into_iter()
        .zip(ys_pp.iter())
        .map(|(y_p, y_pp)| fr_xor(&y_p, &y_pp))
        .collect();
    let vs_pp_u128 = points_to_u128(vs_pp.clone());
    let ys_hat = points_to_u128(ys_hat);
    let (new_vs_pp, new_ys_hat) = if has_duplicate {
        let mut map = HashMap::new();
        for (i, ele) in ys_num.iter().enumerate() {
            map.insert(*ele as u32, (vs_pp_u128[i], ys_hat[i]));
        }
        let (new_vs_pp, new_ys_hat) = copy_duplicate::<u128>(&ys_orignial, &map);
        (new_vs_pp, new_ys_hat)
    } else {
        (vs_pp_u128, ys_hat)
    };
    // run consensus for circuit input
    let data = (&new_vs_pp, &new_ys_hat);
    let bytes = bincode::serialize(&data).unwrap();
    let dig = digest(Algorithm::SHA256, &bytes);
    if !debug {
        run_consensus(dig, self_id);
    }

    let timer4 = howlong::ProcessCPUTimer::new();

    let anno2 = ev_psi_check_fast(chunk_size, new_vs_pp, new_ys_hat, rec_stream);
    let t = timer4.elapsed().real.as_micros() as u64;
    println!(
        "circuit size: {}, receiver psi circuit time: {} ms",
        anno2.len(),
        t / 1000
    );
    let t = timer0.elapsed().real.as_micros() as u64;
    println!("### receiver total time: {} ms", t / 1000);

    anno2
}

pub fn intra_psi_anno_sender_parallel<S: Stream>(
    xs: Vec<u64>, // all xs for one psi
    vs: Vec<u64>, // all anno for one psi
    kzg: &KZG<Bls12_381>,
    send_stream: &mut S, // stream for oprf and sending poly
    xs_com_info: &Vec<G1>,
    tree: &SubProductTree<Fr>, // built over xs
    debug: bool,
    self_id: u16,
    prover_id: u16,
    ys_len_larger: bool,
    receiver_size: usize,
    mut psi_sen_streams: Vec<S>,
) -> Vec<u128> {
    let self_id_mod_n = self_id % N;
    // sender oprf
    let mut xses = vec![xs];
    let mut oprf_info = sender_multi_oprf(&xses, send_stream, self_id, debug, ys_len_larger);
    let xs = xses.remove(0);
    let xs = points_from_num(xs);

    let (xs_p, r) = oprf_info.remove(0);

    let xs_p = points_from_num(xs_p);
    let vs_p = anno_xor_r(vs, r);

    // compute commitment and run consensus
    // C_x
    let commitment_x = kzg.commit_by_pre_info_g1(&xs_p, &xs_com_info);
    // C_v
    let commitment_v = kzg.commit_by_pre_info_g1(&vs_p, &xs_com_info);

    // consensus for C_x and C_v
    let mut c_x_bytes: Vec<u8> = vec![];
    commitment_x.serialize_uncompressed(&mut c_x_bytes).unwrap();
    let mut c_v_bytes: Vec<u8> = vec![];
    commitment_v.serialize_uncompressed(&mut c_v_bytes).unwrap();

    send_data_by_stream(send_stream, &c_x_bytes, true);
    send_data_by_stream(send_stream, &c_v_bytes, true);

    c_x_bytes.append(&mut c_v_bytes);
    let dig = digest(Algorithm::SHA256, &c_x_bytes);
    if !debug {
        run_consensus(dig, self_id);
    }

    // for prover, do interpolation and send to receiver
    if prover_id == self_id_mod_n {
        sender_poly(&xs, &xs_p, &vs_p, tree, send_stream);
    }

    // run circuit
    let mut rng = get_fixed_rng();
    let mut anno_share1 = vec![];
    for _ in 0..receiver_size {
        anno_share1.push(rng.gen::<u128>());
    }

    let data = (&anno_share1, r);
    let bytes = bincode::serialize(&data).unwrap();
    let dig = digest(Algorithm::SHA256, &bytes);
    if !debug {
        run_consensus(dig, self_id);
    }

    let timer3 = howlong::ProcessCPUTimer::new();

    gb_psi_check_parallel(anno_share1.clone(), r, &mut psi_sen_streams);

    let t = timer3.elapsed().real.as_micros() as u64;
    println!("sender psi circuit time: {} ms", t / 1000);
    return anno_share1;
}

pub fn intra_psi_anno_receiver_parallel<S: Stream>(
    ys_orignial: &Vec<u32>, // may contain duplicate
    has_duplicate: bool,
    ys_num: Vec<u64>, // no duplicate
    kzg: &KZG<Bls12_381>,
    rec_stream: &mut S, // stream for oprf and receiving poly
    tree: &SubProductTree<Fr>,  // built over ys
    veri_info: &Vec<Vec<G1>>,
    z_commit: Vec<<Bls12_381 as Pairing>::G2Affine>,
    self_id: u16,
    prover_id: u16,
    ys_len_larger: bool,
    debug: bool,
    is_partitioned: bool,
    mut psi_rec_streams: Vec<S>,
) -> Vec<u128> {
    let timer0 = howlong::ProcessCPUTimer::new();
    let self_id_mod_n = self_id % N;
    let handle = if prover_id != self_id_mod_n {
        thread::spawn(move || listen_to_receive_proof(self_id, 1))
    } else {
        thread::spawn(move || vec![])
    };

    // receiver oprf
    let mut yses = vec![ys_num.clone()];
    let mut oprf_info = receiver_multi_oprf(&yses, rec_stream, self_id, debug, ys_len_larger);

    let ys = points_from_num(yses.remove(0));
    let ys_p = points_from_num(oprf_info.remove(0));

    let c_x_bytes = receive_data_by_stream(rec_stream);
    let c_v_bytes = receive_data_by_stream(rec_stream);

    let commitment_x: Projective<Config> =
        Projective::deserialize_uncompressed(&*c_x_bytes).unwrap();
    let commitment_v: Projective<Config> =
        Projective::deserialize_uncompressed(&*c_v_bytes).unwrap();

    let (ys_pp, vs_pp) = if is_partitioned {
        todo!()
    } else {
        if prover_id == self_id_mod_n {
            let _proofs_info = handle.join().expect("thread panicked");
            let (poly_x, poly_v) = receiver_poly(rec_stream);
            // gen proof
            let timer = howlong::ProcessCPUTimer::new();
            let pool1 = ThreadPoolBuilder::new().num_threads(TEST_THREAD_NUM).build().unwrap();
            let (ys_pp, pi_x) = pool1.install(||{
                kzg.open_multi_with_subproduct_tree(&poly_x, &ys, tree)
            });
            let pool2 = ThreadPoolBuilder::new().num_threads(TEST_THREAD_NUM).build().unwrap();
            let (vs_pp, pi_v) = pool2.install(|| {
                kzg.open_multi_with_subproduct_tree(&poly_v, &ys, tree)
            });
            let t = timer.elapsed().real.as_micros() as u64;
            println!("proof gen time: {} ms", t / 1000);

            let timer2 = howlong::ProcessCPUTimer::new();
            broadcast_proof(self_id, &ys_pp, pi_x, &vs_pp, pi_v);
            let t = timer2.elapsed().real.as_micros() as u64;
            println!("broadcast proof time: {} ms", t / 1000);
            (ys_pp, vs_pp)
        } else {
            let timer = howlong::ProcessCPUTimer::new();
            let mut proofs_info = handle.join().expect("thread panicked");
            let (_, ys_pp, pi_x, vs_pp, pi_v) = proofs_info.remove(0);
            let t = timer.elapsed().real.as_micros() as u64;
            println!("receive proof time: {} ms", t / 1000);

            let _res1 = kzg.fast_verify_multi(
                &ys_pp,
                commitment_x,
                pi_x,
                veri_info.get(0).unwrap(),        // as not partitioned
                z_commit.get(0).unwrap().clone(), // as not partitioned
            );
            let _res2 = kzg.fast_verify_multi(
                &vs_pp,
                commitment_v,
                pi_v,
                veri_info.get(0).unwrap(),        // as not partitioned
                z_commit.get(0).unwrap().clone(), // as not partitioned
            );
            (ys_pp, vs_pp)
        }
    };

    let ys_hat: Vec<Fr> = ys_p
        .into_par_iter()
        .zip(ys_pp.par_iter())
        .map(|(y_p, y_pp)| fr_xor(&y_p, &y_pp))
        .collect();
    let vs_pp_u128 = points_to_u128(vs_pp.clone());
    let ys_hat = points_to_u128(ys_hat);
    let (new_vs_pp, new_ys_hat) = if has_duplicate {
        let mut map = HashMap::new();
        for (i, ele) in ys_num.iter().enumerate() {
            map.insert(*ele as u32, (vs_pp_u128[i], ys_hat[i]));
        }
        let (new_vs_pp, new_ys_hat) = copy_duplicate::<u128>(&ys_orignial, &map);
        (new_vs_pp, new_ys_hat)
    } else {
        (vs_pp_u128, ys_hat)
    };

    // run consensus for circuit input
    let data = (&new_vs_pp, &new_ys_hat);
    let bytes = bincode::serialize(&data).unwrap();
    let dig = digest(Algorithm::SHA256, &bytes);
    if !debug {
        run_consensus(dig, self_id);
    }

    let timer4 = howlong::ProcessCPUTimer::new();

    let anno2 = ev_psi_check_parallel(new_vs_pp, new_ys_hat, &mut psi_rec_streams);

    let t = timer4.elapsed().real.as_micros() as u64;
    println!(
        "circuit size: {}, receiver psi circuit time: {} ms",
        anno2.len(),
        t / 1000
    );
    let t = timer0.elapsed().real.as_micros() as u64;
    println!("### receiver total time: {} ms", t / 1000);

    anno2
}

pub fn basic_psi_anno_sender<S: Stream>(
    xs: Vec<u64>,
    vs: Vec<u64>,
    tree: &SubProductTree<Fr>,
    stream: &mut S,
    receiver_size: usize,
    chunk_size: usize,
    self_id: u16,
    debug: bool,
    ys_len_larger: bool,
) -> Vec<u128> {
    assert_eq!(xs.len(), vs.len());
    // println!("start sender oprf");
    // oprf to get ({x'_i=F(k, x_i)^r}, r) (Alice is OT receiver)
    let (xs_p, r) = alice_opprf(stream, &xs, ys_len_larger);
    // println!("finish sender oprf");

    // consensus oprf info
    let mut bytes = bincode::serialize(&xs_p).unwrap();
    let mut bytes_r = bincode::serialize(&r).unwrap();
    bytes.append(&mut bytes_r);
    let dig = digest(Algorithm::SHA256, &bytes);
    if !debug {
        run_consensus(dig, self_id);
    }
    // println!("consensus for oprf info");

    let xs = points_from_num(xs);
    let xs_p = points_from_num(xs_p);
    let vs_p = anno_xor_r(vs, r);

    let timer = howlong::ProcessCPUTimer::new();
    // interpolation
    let poly_x = fft_interpolate_with_subproduct_tree(&xs, &xs_p, tree);
    let poly_v = fft_interpolate_with_subproduct_tree(&xs, &vs_p, tree);
    let t = timer.elapsed().real.as_micros() as u64;
    println!("interpolate time: {} ms", t / 1000);

    // send poly_x, poly_v to receiver prover
    let mut poly_x_bytes: Vec<u8> = vec![];
    poly_x.serialize_uncompressed(&mut poly_x_bytes).unwrap();
    let mut poly_v_bytes: Vec<u8> = vec![];
    poly_v.serialize_uncompressed(&mut poly_v_bytes).unwrap();

    // consensus on the polys
    let bytes: Vec<u8> = poly_x_bytes
        .iter()
        .chain(poly_v_bytes.iter())
        .cloned()
        .collect();
    let dig = digest(Algorithm::SHA256, &bytes);
    if !debug {
        run_consensus(dig, self_id);
    }
    // println!("consensus for poly info");

    send_data_by_stream(stream, &poly_x_bytes, false);
    send_data_by_stream(stream, &poly_v_bytes, false);

    // execute garbled circuit
    let mut rng = get_fixed_rng();
    let mut anno_share1 = vec![];
    for _ in 0..receiver_size {
        anno_share1.push(rng.gen::<u128>());
    }

    // consensus on circuit inputs
    let bytes = bincode::serialize(&anno_share1).unwrap();
    let dig = digest(Algorithm::SHA256, &bytes);
    if !debug {
        run_consensus(dig, self_id);
    }

    let timer = howlong::ProcessCPUTimer::new();
    gb_psi_check_fast(chunk_size, anno_share1.clone(), r, stream);
    let t = timer.elapsed().real.as_micros() as u64;
    println!("sender psi circuit time: {} ms", t / 1000);

    anno_share1
}

pub fn basic_psi_anno_sender_parallel<S: Stream>(
    xs: Vec<u64>,
    vs: Vec<u64>,
    tree: &SubProductTree<Fr>,
    stream: &mut S,
    receiver_size: usize,
    self_id: u16,
    debug: bool,
    ys_len_larger: bool,
    mut psi_sen_streams: Vec<S>,
) -> Vec<u128> {
    assert_eq!(xs.len(), vs.len());
    // println!("start sender oprf");
    // oprf to get ({x'_i=F(k, x_i)^r}, r) (Alice is OT receiver)
    let (xs_p, r) = alice_opprf(stream, &xs, ys_len_larger);
    // println!("finish sender oprf");

    // consensus oprf info
    let mut bytes = bincode::serialize(&xs_p).unwrap();
    let mut bytes_r = bincode::serialize(&r).unwrap();
    bytes.append(&mut bytes_r);
    let dig = digest(Algorithm::SHA256, &bytes);
    if !debug {
        run_consensus(dig, self_id);
    }
    // println!("consensus for oprf info");

    let xs = points_from_num(xs);
    let xs_p = points_from_num(xs_p);
    let vs_p = anno_xor_r(vs, r);

    let timer = howlong::ProcessCPUTimer::new();
    // interpolation
    // let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
    // let poly_x = pool.install(|| {
    //     fft_interpolate_with_subproduct_tree(&xs, &xs_p, tree)
    // });
    // let poly_v = pool.install(|| {
    //     fft_interpolate_with_subproduct_tree(&xs, &vs_p, tree)
    // });
    let poly_x = fft_interpolate_with_subproduct_tree(&xs, &xs_p, tree);
    let poly_v = fft_interpolate_with_subproduct_tree(&xs, &vs_p, tree);
    let t = timer.elapsed().real.as_micros() as u64;
    println!("interpolate time: {} ms", t / 1000);

    // send poly_x, poly_v to receiver prover
    let mut poly_x_bytes: Vec<u8> = vec![];
    poly_x.serialize_uncompressed(&mut poly_x_bytes).unwrap();
    let mut poly_v_bytes: Vec<u8> = vec![];
    poly_v.serialize_uncompressed(&mut poly_v_bytes).unwrap();

    // consensus on the polys
    let bytes: Vec<u8> = poly_x_bytes
        .iter()
        .chain(poly_v_bytes.iter())
        .cloned()
        .collect();
    let dig = digest(Algorithm::SHA256, &bytes);
    if !debug {
        run_consensus(dig, self_id);
    }
    // println!("consensus for poly info");

    send_data_by_stream(stream, &poly_x_bytes, false);
    send_data_by_stream(stream, &poly_v_bytes, false);

    // execute garbled circuit
    let mut rng = get_fixed_rng();
    let mut anno_share1 = vec![];
    for _ in 0..receiver_size {
        anno_share1.push(rng.gen::<u128>());
    }

    // consensus on circuit inputs
    let bytes = bincode::serialize(&anno_share1).unwrap();
    let dig = digest(Algorithm::SHA256, &bytes);
    if !debug {
        run_consensus(dig, self_id);
    }

    let timer = howlong::ProcessCPUTimer::new();
    
    // pool.install(|| {
    //     gb_psi_check_parallel(chunk_size, anno_share1.clone(), r, &mut psi_sen_streams);
    // });

    gb_psi_check_parallel(anno_share1.clone(), r, &mut psi_sen_streams);

    let t = timer.elapsed().real.as_micros() as u64;
    println!("sender psi circuit time: {} ms", t / 1000);

    anno_share1
}

pub fn basic_psi_anno_receiver<S: Stream>(
    ys: Vec<u64>,
    stream: &mut S,
    tree: &SubProductTree<Fr>,
    chunk_size: usize,
    self_id: u16,
    debug: bool,
    ys_len_larger: bool,
) -> Vec<u128> {
    // oprf to obtain {y'_i=F(k,y_i)}
    let ys_p = bob_opprf(stream, &ys, ys_len_larger);

    // consensus on oprf res
    let bytes = bincode::serialize(&ys_p).unwrap();
    let dig = digest(Algorithm::SHA256, &bytes);
    if !debug {
        run_consensus(dig, self_id);
    }
    // println!("consensus for oprf info");

    let ys = points_from_num(ys);
    let ys_p = points_from_num(ys_p);

    // get poly_x and poly_v
    let poly_x_bytes = receive_data_by_stream(stream);
    let poly_x: Poly<Fr> = Poly::deserialize_uncompressed(&*poly_x_bytes).unwrap();
    let poly_v_bytes = receive_data_by_stream(stream);
    let poly_v: Poly<Fr> = Poly::deserialize_uncompressed(&*poly_v_bytes).unwrap();

    let timer1 = howlong::ProcessCPUTimer::new();
    let ys_pp = tree.multi_eval_parallel(&ys, &poly_x);
    let vs_pp = tree.multi_eval_parallel(&ys, &poly_v);
    let t = timer1.elapsed().real.as_micros() as u64;
    println!("point eval time: {} ms", t / 1000);
    // let ys_pp = tree.multi_eval_single(&ys, &poly_x);
    // let vs_pp = tree.multi_eval_single(&ys, &poly_v);

    let ys_hat: Vec<Fr> = ys_p
        .into_iter()
        .zip(ys_pp.iter())
        .map(|(y_p, y_pp)| fr_xor(&y_p, &y_pp))
        .collect();

    // input vs_pp and ys_hat to circuit
    let vs_pp_u128 = points_to_u128(vs_pp);
    let ys_hat = points_to_u128(ys_hat);

    // consensus on circuit inputs
    let mut bytes = bincode::serialize(&vs_pp_u128).unwrap();
    let mut bytes_ys_hat = bincode::serialize(&ys_hat).unwrap();
    bytes.append(&mut bytes_ys_hat);

    let dig = digest(Algorithm::SHA256, &bytes);
    if !debug {
        run_consensus(dig, self_id);
    }

    let timer = howlong::ProcessCPUTimer::new();
    let anno2 = ev_psi_check_fast(chunk_size, vs_pp_u128, ys_hat, stream);
    let t = timer.elapsed().real.as_micros() as u64;
    println!(
        "circuit size: {}, receiver psi circuit: {} ms",
        anno2.len(),
        t / 1000
    );

    anno2
}

pub fn basic_psi_anno_receiver_parallel<S: Stream>(
    ys: Vec<u64>,
    stream: &mut S,
    tree: &SubProductTree<Fr>,
    self_id: u16,
    debug: bool,
    ys_len_larger: bool,
    mut psi_rec_streams: Vec<S>,
) -> Vec<u128> {
    // oprf to obtain {y'_i=F(k,y_i)}
    let ys_p = bob_opprf(stream, &ys, ys_len_larger);

    // consensus on oprf res
    let bytes = bincode::serialize(&ys_p).unwrap();
    let dig = digest(Algorithm::SHA256, &bytes);
    if !debug {
        run_consensus(dig, self_id);
    }
    // println!("consensus for oprf info");

    let ys = points_from_num(ys);
    let ys_p = points_from_num(ys_p);

    // get poly_x and poly_v
    let poly_x_bytes = receive_data_by_stream(stream);
    let poly_x: Poly<Fr> = Poly::deserialize_uncompressed(&*poly_x_bytes).unwrap();
    let poly_v_bytes = receive_data_by_stream(stream);
    let poly_v: Poly<Fr> = Poly::deserialize_uncompressed(&*poly_v_bytes).unwrap();

    let timer1 = howlong::ProcessCPUTimer::new();
    // DBG
    // let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap(); 
    // let ys_pp = pool.install(|| {
    //     tree.multi_eval_parallel(&ys, &poly_x)
    // });
    // let vs_pp = pool.install(|| {
    //     tree.multi_eval_parallel(&ys, &poly_v)
    // });

    let ys_pp = tree.multi_eval_parallel(&ys, &poly_x);
    let vs_pp = tree.multi_eval_parallel(&ys, &poly_v);
    let t = timer1.elapsed().real.as_micros() as u64;
    println!("point eval time: {} ms", t / 1000);
    // let ys_pp = tree.multi_eval_single(&ys, &poly_x);
    // let vs_pp = tree.multi_eval_single(&ys, &poly_v);

    let ys_hat: Vec<Fr> = ys_p
        .into_par_iter()
        .zip(ys_pp.par_iter())
        .map(|(y_p, y_pp)| fr_xor(&y_p, &y_pp))
        .collect();

    // input vs_pp and ys_hat to circuit
    let vs_pp_u128 = points_to_u128(vs_pp);
    let ys_hat = points_to_u128(ys_hat);

    // consensus on circuit inputs
    let mut bytes = bincode::serialize(&vs_pp_u128).unwrap();
    let mut bytes_ys_hat = bincode::serialize(&ys_hat).unwrap();
    bytes.append(&mut bytes_ys_hat);

    let dig = digest(Algorithm::SHA256, &bytes);
    if !debug {
        run_consensus(dig, self_id);
    }

    let timer = howlong::ProcessCPUTimer::new();
    // let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap(); 
    // let anno2 = pool.install(|| {
    //     ev_psi_check_parallel(chunk_size, vs_pp_u128, ys_hat, &mut psi_rec_streams)
    // });

    let anno2 = ev_psi_check_parallel(vs_pp_u128, ys_hat, &mut psi_rec_streams);
    let t = timer.elapsed().real.as_micros() as u64;
    println!(
        "circuit size: {}, receiver psi circuit: {} ms",
        anno2.len(),
        t / 1000
    );

    anno2
}

/*
A trick to guarantee correct res: inv_pmt must contain a 0 (means the first pos). However, inv_pmt will serve as annotation for the psi (where 0 means fail to join). To distinguish them, we use a special val to replace 0 during psi, and finally convert it back to 0 when getting ks
*/
pub const ZERO_PLACE_HOLDER: usize = 324234534;

pub fn batch_psi_shared_anno_sender_parallel<S: Stream>(
    xses: Vec<Vec<u64>>,
    vs_1s: Vec<Vec<u32>>,
    kzg: &KZG<Bls12_381>,
    send_stream: &mut S, // stream for oprf and sending poly
    xs_com_infos: &Vec<Vec<G1>>,
    trees: &Vec<SubProductTree<Fr>>, // built over xs
    debug: bool,
    self_id: u16,
    ys_len_larger: bool,  // should be a vec
    receiver_size: usize, // should be a vec
    chunk_size: usize,    // should be a vec
    psi_streams: Vec<S>,
    mut oep_streams: Vec<S>,
) -> Vec<Vec<u32>> {
    assert_eq!(xses.len(), vs_1s.len());
    assert_eq!(xses.len(), xs_com_infos.len());
    assert_eq!(xses.len(), trees.len());

    let mut rng = get_fixed_rng();
    let query_num = vs_1s.len();
    let mut extended_vs_1s = vs_1s;

    extended_vs_1s.par_iter_mut().for_each(|extended_vs_1| {
        extended_vs_1.extend(vec![0; receiver_size]); // n+s elements
    });

    let n = xses.get(0).unwrap().len();
    let new_size = n + receiver_size; // n + s

    let mut pmt1: Vec<usize> = (0..new_size).collect();
    pmt1.shuffle(&mut rng);
    let mut inv_pmt1 = inv_pmt(&pmt1);

    inv_pmt1.par_iter_mut().for_each(|ele| {
        if *ele == 0 {
            *ele = ZERO_PLACE_HOLDER;
        }
    });

    //run consensus for pmt1 and extended_vs_1
    let mut bytes = bincode::serialize(&pmt1).unwrap();
    bytes.append(&mut bincode::serialize(&extended_vs_1s).unwrap());
    let dig = digest(Algorithm::SHA256, &bytes);
    if !debug {
        run_consensus(dig, self_id);
    }

    // step1: run OP to permute two extended_vs shares
    let vs_p_1s: Vec<Vec<u32>> = extended_vs_1s
        .iter()
        .map(|extended_vs_1| permutor_permute(send_stream, &pmt1, extended_vs_1))
        .collect();

    // step2: run PSI to share inv_pmt1 info
    let inv_pmt1_info: Vec<u64> = inv_pmt1[0..n].par_iter().map(|v| *v as u64).collect();


    let inv_pmt1_infos = vec![inv_pmt1_info; query_num];
    let psi_res1s = batch_psi_anno_sender_parallel(
        xses,
        inv_pmt1_infos,
        kzg,
        send_stream,
        xs_com_infos,
        trees,
        debug,
        self_id,
        ys_len_larger,
        receiver_size,
        psi_streams,
    );
    // run OEP circuit
    let inv_pmt_u128: Vec<u128> = inv_pmt1.par_iter().map(|v| *v as u128).collect();

    psi_res1s
        .into_iter()
        .for_each(|psi_res1| {
            gb_oep_check_parallel(chunk_size, psi_res1, &mut oep_streams, inv_pmt_u128[n..].to_vec());
        });

    // step3: run OEP to get correct res
    // vs_p_1.len() = n+s
    vs_p_1s
        .iter()
        .map(|vs_p_1| sender_extended_permute(send_stream, vs_p_1, receiver_size))
        .collect()
}

pub fn batch_psi_shared_anno_receiver_parallel<S: Stream>(
    ys_orignial: &Vec<Vec<u32>>, // may contain duplicate
    has_duplicate: bool,         // only for the target query
    ys_num: Vec<Vec<u64>>,       // no duplicate
    vs_2s: Vec<Vec<u32>>,        // sender anno_2, n ele
    kzg: &KZG<Bls12_381>,
    rec_stream: &mut S,      // stream for oprf and receiving poly
    trees: &Vec<SubProductTree<Fr>>, // built over the target query's ys
    veri_info: &Vec<Vec<G1>>,
    z_commit: Vec<<Bls12_381 as Pairing>::G2Affine>,
    chunk_size: usize,
    self_id: u16,
    ys_len_larger: bool, // should be vec
    debug: bool,
    psi_streams: Vec<S>,
    mut oep_streams: Vec<S>,
) -> Vec<Vec<u32>> {
    assert_eq!(ys_orignial.len(), ys_num.len());
    assert_eq!(ys_orignial.len(), vs_2s.len());
    assert_eq!(ys_orignial.len(), trees.len());
    assert_eq!(ys_orignial.len(), veri_info.len());
    assert_eq!(ys_orignial.len(), z_commit.len());

    let s = ys_num.get(0).unwrap().len();
    let mut extended_vs_2s = vs_2s;
    extended_vs_2s.par_iter_mut().for_each(|extended_vs_2| {
        extended_vs_2.extend(vec![0; s]); // s + n elements
    });

    //run consensus for extended_vs_2
    let bytes = bincode::serialize(&extended_vs_2s).unwrap();
    let dig = digest(Algorithm::SHA256, &bytes);
    if !debug {
        run_consensus(dig, self_id);
    }

    // step1: run OP to permute two extended_vs shares
    let vs_p_2s: Vec<Vec<u32>> = extended_vs_2s
        .iter()
        .map(|extended_vs_2| sender_permute(rec_stream, &extended_vs_2))
        .collect();

    // step2: run PSI to share inv_pmt1 info
    let psi_res2s = batch_psi_anno_receiver_parallel(
        ys_orignial,
        has_duplicate,
        ys_num,
        kzg,
        rec_stream,
        trees,
        veri_info,
        z_commit,
        self_id,
        ys_len_larger,
        debug,
        psi_streams,
    );

    let kses: Vec<Vec<u128>> = psi_res2s
        .into_iter()
        .map(|psi_res2| ev_oep_check_parallel(chunk_size, psi_res2, &mut oep_streams))
        .collect();

    let pmt2s: Vec<Vec<usize>> = kses
        .into_par_iter()
        .map(|ks| {
            ks.into_par_iter()
                .map(|v| {
                    if v == 0 {
                        ZERO_PLACE_HOLDER
                    } else {
                        v as usize
                    }
                })
                .collect()
        })
        .collect();

    // step3: run OEP to get correct res
    // pmt2.len() = s; vs_p_2.len() = n+s
    pmt2s
        .iter()
        .zip(vs_p_2s.iter())
        .map(|(pmt2, vs_p_2)| permutor_extended_permute(rec_stream, pmt2, vs_p_2))
        .collect()
}

pub fn batch_psi_shared_anno_sender<S: Stream>(
    xses: Vec<Vec<u64>>,
    vs_1s: Vec<Vec<u32>>,
    kzg: &KZG<Bls12_381>,
    send_stream: &mut S, // stream for oprf and sending poly
    xs_com_infos: &Vec<Vec<G1>>,
    trees: &Vec<SubProductTree<Fr>>, // built over xs
    debug: bool,
    self_id: u16,
    ys_len_larger: bool,  // should be a vec
    receiver_size: usize, // should be a vec
    chunk_size: usize,    // should be a vec
) -> Vec<Vec<u32>> {
    assert_eq!(xses.len(), vs_1s.len());
    assert_eq!(xses.len(), xs_com_infos.len());
    assert_eq!(xses.len(), trees.len());

    let mut rng = get_fixed_rng();
    let query_num = vs_1s.len();
    let mut extended_vs_1s = vs_1s;

    extended_vs_1s.par_iter_mut().for_each(|extended_vs_1| {
        extended_vs_1.extend(vec![0; receiver_size]); // n+s elements
    });

    let n = xses.get(0).unwrap().len();
    let new_size = n + receiver_size; // n + s

    let mut pmt1: Vec<usize> = (0..new_size).collect();
    pmt1.shuffle(&mut rng);
    let mut inv_pmt1 = inv_pmt(&pmt1);

    inv_pmt1.par_iter_mut().for_each(|ele| {
        if *ele == 0 {
            *ele = ZERO_PLACE_HOLDER;
        }
    });

    //run consensus for pmt1 and extended_vs_1
    let mut bytes = bincode::serialize(&pmt1).unwrap();
    bytes.append(&mut bincode::serialize(&extended_vs_1s).unwrap());
    let dig = digest(Algorithm::SHA256, &bytes);
    if !debug {
        run_consensus(dig, self_id);
    }

    // step1: run OP to permute two extended_vs shares
    let vs_p_1s: Vec<Vec<u32>> = extended_vs_1s
        .iter()
        .map(|extended_vs_1| permutor_permute(send_stream, &pmt1, extended_vs_1))
        .collect();

    // step2: run PSI to share inv_pmt1 info
    let inv_pmt1_info: Vec<u64> = inv_pmt1[0..n].par_iter().map(|v| *v as u64).collect();

    let inv_pmt1_infos = vec![inv_pmt1_info; query_num];
    let psi_res1s = batch_psi_anno_sender(
        xses,
        inv_pmt1_infos,
        kzg,
        send_stream,
        xs_com_infos,
        trees,
        debug,
        self_id,
        ys_len_larger,
        receiver_size,
        chunk_size,
    );
    // run OEP circuit
    let inv_pmt_u128: Vec<u128> = inv_pmt1.par_iter().map(|v| *v as u128).collect();

  
    // If does not work, here use a new stream
    psi_res1s.into_iter().for_each(|psi_res1| {
        gb_oep_check_fast(
            chunk_size,
            psi_res1,
            send_stream.try_clone().unwrap(),
            inv_pmt_u128[n..].to_vec(),
        );
    });

    // step3: run OEP to get correct res
    // vs_p_1.len() = n+s
    vs_p_1s
        .iter()
        .map(|vs_p_1| sender_extended_permute(send_stream, vs_p_1, receiver_size))
        .collect()
}

pub fn batch_psi_shared_anno_receiver<S: Stream>(
    ys_orignial: &Vec<Vec<u32>>, // may contain duplicate
    has_duplicate: bool,         // only for the target query
    ys_num: Vec<Vec<u64>>,       // no duplicate
    vs_2s: Vec<Vec<u32>>,        // sender anno_2, n ele
    kzg: &KZG<Bls12_381>,
    rec_stream: &mut S,      // stream for oprf and receiving poly
    trees: &Vec<SubProductTree<Fr>>, // built over the target query's ys
    veri_info: &Vec<Vec<G1>>,
    z_commit: Vec<<Bls12_381 as Pairing>::G2Affine>,
    chunk_size: usize,
    self_id: u16,
    ys_len_larger: bool, // should be vec
    debug: bool,
) -> Vec<Vec<u32>> {
    assert_eq!(ys_orignial.len(), ys_num.len());
    assert_eq!(ys_orignial.len(), vs_2s.len());
    assert_eq!(ys_orignial.len(), trees.len());
    assert_eq!(ys_orignial.len(), veri_info.len());
    assert_eq!(ys_orignial.len(), z_commit.len());

    let s = ys_num.get(0).unwrap().len();
    let mut extended_vs_2s = vs_2s;
    extended_vs_2s.par_iter_mut().for_each(|extended_vs_2| {
        extended_vs_2.extend(vec![0; s]); // s + n elements
    });

    //run consensus for extended_vs_2
    let bytes = bincode::serialize(&extended_vs_2s).unwrap();
    let dig = digest(Algorithm::SHA256, &bytes);
    if !debug {
        run_consensus(dig, self_id);
    }

    // step1: run OP to permute two extended_vs shares
    let vs_p_2s: Vec<Vec<u32>> = extended_vs_2s
        .iter()
        .map(|extended_vs_2| sender_permute(rec_stream, &extended_vs_2))
        .collect();

    // step2: run PSI to share inv_pmt1 info
    let psi_res2s = batch_psi_anno_receiver(
        ys_orignial,
        has_duplicate,
        ys_num,
        kzg,
        rec_stream,
        trees,
        veri_info,
        z_commit,
        chunk_size,
        self_id,
        ys_len_larger,
        debug,
    );

    let kses: Vec<Vec<u128>> = psi_res2s
        .into_iter()
        .map(|psi_res2| ev_oep_check_fast(chunk_size, psi_res2, rec_stream.try_clone().unwrap()))
        .collect();

    let pmt2s: Vec<Vec<usize>> = kses
        .into_par_iter()
        .map(|ks| {
            ks.into_par_iter()
                .map(|v| {
                    if v == 0 {
                        ZERO_PLACE_HOLDER
                    } else {
                        v as usize
                    }
                })
                .collect()
        })
        .collect();

    // step3: run OEP to get correct res
    // pmt2.len() = s; vs_p_2.len() = n+s
    pmt2s
        .iter()
        .zip(vs_p_2s.iter())
        .map(|(pmt2, vs_p_2)| permutor_extended_permute(rec_stream, pmt2, vs_p_2))
        .collect()
}

pub fn intra_psi_shared_anno_sender<S: Stream>(
    xs: Vec<u64>,   // sender key
    vs_1: Vec<u32>, // sender anno_1
    kzg: &KZG<Bls12_381>,
    tree: &SubProductTree<Fr>,
    xs_com_info: &Vec<G1>,
    receiver_size: usize, // s
    chunk_size: usize,
    stream: &mut S,
    self_id: u16,
    prover_id: u16,
    debug: bool,
    ys_len_larger: bool,
) -> Vec<u32> {
    let mut rng = get_fixed_rng();
    let mut extended_vs_1 = vs_1;
    extended_vs_1.extend(vec![0; receiver_size]); // n+s elements
    let n = xs.len();
    let new_size = n + receiver_size; // n + s

    let mut pmt1: Vec<usize> = (0..new_size).collect();
    pmt1.shuffle(&mut rng);
    let mut inv_pmt1 = inv_pmt(&pmt1);

    for ele in inv_pmt1.iter_mut() {
        if *ele == 0 {
            *ele = ZERO_PLACE_HOLDER;
            break;
        }
    }

    //run consensus for pmt1 and extended_vs_1
    let mut bytes = bincode::serialize(&pmt1).unwrap();
    bytes.append(&mut bincode::serialize(&extended_vs_1).unwrap());
    let dig = digest(Algorithm::SHA256, &bytes);
    if !debug {
        run_consensus(dig, self_id);
    }

    // step1: run OP to permute two extended_vs shares
    let vs_p_1 = permutor_permute(stream, &pmt1, &extended_vs_1);

    // step2: run PSI to share inv_pmt1 info
    let inv_pmt1_info: Vec<u64> = inv_pmt1[0..n].iter().map(|v| *v as u64).collect();
    let psi_res1 = intra_psi_anno_sender(
        xs,
        inv_pmt1_info,
        kzg,
        stream,
        xs_com_info,
        tree,
        debug,
        self_id,
        prover_id,
        ys_len_larger,
        receiver_size,
        chunk_size,
    );
    // run OEP circuit
    let inv_pmt_u128: Vec<u128> = inv_pmt1.iter().map(|v| *v as u128).collect();
    gb_oep_check_fast(
        chunk_size,
        psi_res1,
        stream.try_clone().unwrap(),
        inv_pmt_u128[n..].to_vec(),
    );

    // step3: run OEP to get correct res
    // vs_p_1.len() = n+s
    sender_extended_permute(stream, &vs_p_1, receiver_size)
}

pub fn intra_psi_shared_anno_receiver<S: Stream>(
    ys_orignial: &Vec<u32>, // may contain duplicate
    has_duplicate: bool,
    ys: Vec<u64>, // receiver key, s ele, no duplicate
    kzg: &KZG<Bls12_381>,
    tree: &SubProductTree<Fr>, // built over ys
    veri_info: &Vec<Vec<G1>>,
    z_commit: Vec<<Bls12_381 as Pairing>::G2Affine>,
    vs_2: Vec<u32>, // sender anno_2, n ele
    stream: &mut S,
    chunk_size: usize,
    self_id: u16,
    prover_id: u16,
    debug: bool,
    ys_len_larger: bool,
) -> Vec<u32> {
    let s = ys.len();
    let mut extended_vs_2 = vs_2;
    extended_vs_2.extend(vec![0; s]); // s + n elements

    //run consensus for extended_vs_2
    let bytes = bincode::serialize(&extended_vs_2).unwrap();
    let dig = digest(Algorithm::SHA256, &bytes);
    if !debug {
        run_consensus(dig, self_id);
    }

    // step1: run OP to permute two extended_vs shares
    let vs_p_2 = sender_permute(stream, &extended_vs_2);

    // step2: run PSI to share inv_pmt1 info
    let psi_res2 = intra_psi_anno_receiver(
        ys_orignial,
        has_duplicate,
        ys,
        kzg,
        stream,
        tree,
        veri_info,
        z_commit,
        chunk_size,
        self_id,
        prover_id,
        ys_len_larger,
        debug,
        false,
    );

    // run OEP circuit
    // pmt2 = ks
    let ks = ev_oep_check_fast(chunk_size, psi_res2, stream.try_clone().unwrap());

    // convert ZERO_PLACE_HOLDER back to 0
    let pmt2: Vec<usize> = ks
        .into_iter()
        .map(|v| {
            if v == 0 {
                ZERO_PLACE_HOLDER
            } else {
                v as usize
            }
        })
        .collect();

    // step3: run OEP to get correct res
    // pmt2.len() = s; vs_p_2.len() = n+s
    permutor_extended_permute(stream, &pmt2, &vs_p_2)
}

// assume no duplicate in sender key
pub fn basic_psi_shared_anno_sender<S: Stream>(
    ys: Vec<u64>,   // sender key
    vs_1: Vec<u32>, // sender anno_1
    tree: &SubProductTree<Fr>,
    receiver_size: usize, // s
    chunk_size: usize,
    stream: &mut S,
    self_id: u16,
    debug: bool,
    ys_len_larger: bool,
) -> Vec<u32> {
    let mut rng = get_fixed_rng();
    let mut extended_vs_1 = vs_1;
    extended_vs_1.extend(vec![0; receiver_size]); // n+s elements
    let n = ys.len();
    let new_size = n + receiver_size; // n + s

    let mut pmt1: Vec<usize> = (0..new_size).collect();
    pmt1.shuffle(&mut rng);
    let mut inv_pmt1 = inv_pmt(&pmt1);

    for ele in inv_pmt1.iter_mut() {
        if *ele == 0 {
            *ele = ZERO_PLACE_HOLDER;
            break;
        }
    }

    //run consensus for pmt1 and extended_vs_1
    let mut bytes = bincode::serialize(&pmt1).unwrap();
    bytes.append(&mut bincode::serialize(&extended_vs_1).unwrap());
    let dig = digest(Algorithm::SHA256, &bytes);
    if !debug {
        run_consensus(dig, self_id);
    }
    // println!("consensus for pmt1 and extended_vs_1");

    // step1: run OP to permute two extended_vs shares
    let vs_p_1 = permutor_permute(stream, &pmt1, &extended_vs_1);

    // step2: run PSI to share inv_pmt1 info
    let inv_pmt1_info: Vec<u64> = inv_pmt1[0..n].iter().map(|v| *v as u64).collect();
    let psi_res1 = basic_psi_anno_sender(
        ys,
        inv_pmt1_info,
        tree,
        stream,
        receiver_size,
        chunk_size,
        self_id,
        debug,
        ys_len_larger,
    );

    // run OEP circuit
    let inv_pmt_u128: Vec<u128> = inv_pmt1.iter().map(|v| *v as u128).collect();
    gb_oep_check_fast(
        chunk_size,
        psi_res1,
        stream.try_clone().unwrap(),
        inv_pmt_u128[n..].to_vec(),
    );

    // step3: run OEP to get correct res
    // vs_p_1.len() = n+s
    sender_extended_permute(stream, &vs_p_1, receiver_size)
}

pub fn basic_psi_shared_anno_receiver<S: Stream>(
    zs: Vec<u64>, // receiver key, s ele
    tree: &SubProductTree<Fr>,
    vs_2: Vec<u32>, // sender anno_2, n ele
    stream: &mut S,
    chunk_size: usize,
    self_id: u16,
    debug: bool,
    ys_len_larger: bool,
) -> Vec<u32> {
    let s = zs.len();
    let mut extended_vs_2 = vs_2;
    extended_vs_2.extend(vec![0; s]); // s + n elements

    //run consensus for extended_vs_2
    let bytes = bincode::serialize(&extended_vs_2).unwrap();
    let dig = digest(Algorithm::SHA256, &bytes);
    if !debug {
        run_consensus(dig, self_id);
    }
    // println!("consensus for extended_vs_2");

    // step1: run OP to permute two extended_vs shares
    let vs_p_2 = sender_permute(stream, &extended_vs_2);

    // step2: run PSI to share inv_pmt1 info
    let psi_res2 =
        basic_psi_anno_receiver(zs, stream, tree, chunk_size, self_id, debug, ys_len_larger);

    // run OEP circuit
    // pmt2 = ks
    let ks = ev_oep_check_fast(chunk_size, psi_res2, stream.try_clone().unwrap());

    // convert ZERO_PLACE_HOLDER back to 0
    let pmt2: Vec<usize> = ks
        .into_iter()
        .map(|v| {
            if v == 0 {
                ZERO_PLACE_HOLDER
            } else {
                v as usize
            }
        })
        .collect();
    // step3: run OEP to get correct res
    // pmt2.len() = s; vs_p_2.len() = n+s
    permutor_extended_permute(stream, &pmt2, &vs_p_2)
}

pub fn intra_psi_shared_anno_sender_parallel<S: Stream>(
    xs: Vec<u64>,   // sender key
    vs_1: Vec<u32>, // sender anno_1
    kzg: &KZG<Bls12_381>,
    tree: &SubProductTree<Fr>,
    xs_com_info: &Vec<G1>,
    receiver_size: usize, // s
    chunk_size: usize,
    stream: &mut S,
    self_id: u16,
    prover_id: u16,
    debug: bool,
    ys_len_larger: bool,
    psi_sen_streams: Vec<S>,
    mut oep_sen_streams: Vec<S>,
) -> Vec<u32> {
    let mut rng = get_fixed_rng();
    let mut extended_vs_1 = vs_1;
    extended_vs_1.extend(vec![0; receiver_size]); // n+s elements
    let n = xs.len();
    let new_size = n + receiver_size; // n + s

    let mut pmt1: Vec<usize> = (0..new_size).collect();
    pmt1.shuffle(&mut rng);
    let mut inv_pmt1 = inv_pmt(&pmt1);

    for ele in inv_pmt1.iter_mut() {
        if *ele == 0 {
            *ele = ZERO_PLACE_HOLDER;
            break;
        }
    }

    //run consensus for pmt1 and extended_vs_1
    let mut bytes = bincode::serialize(&pmt1).unwrap();
    bytes.append(&mut bincode::serialize(&extended_vs_1).unwrap());
    let dig = digest(Algorithm::SHA256, &bytes);
    if !debug {
        run_consensus(dig, self_id);
    }

    // step1: run OP to permute two extended_vs shares
    let vs_p_1 = permutor_permute(stream, &pmt1, &extended_vs_1);

    // step2: run PSI to share inv_pmt1 info
    let inv_pmt1_info: Vec<u64> = inv_pmt1[0..n].par_iter().map(|v| *v as u64).collect();
    let psi_res1 = intra_psi_anno_sender_parallel(
        xs,
        inv_pmt1_info,
        kzg,
        stream,
        xs_com_info,
        tree,
        debug,
        self_id,
        prover_id,
        ys_len_larger,
        receiver_size,
        psi_sen_streams,
    );

    // run OEP circuit
    let inv_pmt_u128: Vec<u128> = inv_pmt1.par_iter().map(|v| *v as u128).collect();

    gb_oep_check_parallel(
        chunk_size,
        psi_res1,
        &mut oep_sen_streams,
        inv_pmt_u128[n..].to_vec(),
    );

    // step3: run OEP to get correct res
    // vs_p_1.len() = n+s
    sender_extended_permute(stream, &vs_p_1, receiver_size)
}

pub fn intra_psi_shared_anno_receiver_parallel<S: Stream>(
    ys_orignial: &Vec<u32>, // may contain duplicate
    has_duplicate: bool,
    ys: Vec<u64>, // receiver key, s ele, no duplicate
    kzg: &KZG<Bls12_381>,
    tree: &SubProductTree<Fr>, // built over ys
    veri_info: &Vec<Vec<G1>>,
    z_commit: Vec<<Bls12_381 as Pairing>::G2Affine>,
    vs_2: Vec<u32>, // sender anno_2, n ele
    stream: &mut S,
    chunk_size: usize,
    self_id: u16,
    prover_id: u16,
    debug: bool,
    ys_len_larger: bool,
    psi_rec_streams: Vec<S>,
    mut oep_rec_streams: Vec<S>,
) -> Vec<u32> {
    let s = ys.len();
    let mut extended_vs_2 = vs_2;
    extended_vs_2.extend(vec![0; s]); // s + n elements

    //run consensus for extended_vs_2
    let bytes = bincode::serialize(&extended_vs_2).unwrap();
    let dig = digest(Algorithm::SHA256, &bytes);
    if !debug {
        run_consensus(dig, self_id);
    }

    // step1: run OP to permute two extended_vs shares
    let vs_p_2 = sender_permute(stream, &extended_vs_2);

    // step2: run PSI to share inv_pmt1 info
    let psi_res2 = intra_psi_anno_receiver_parallel(
        ys_orignial,
        has_duplicate,
        ys,
        kzg,
        stream,
        tree,
        veri_info,
        z_commit,
        self_id,
        prover_id,
        ys_len_larger,
        debug,
        false,
        psi_rec_streams,
    );

    let ks = ev_oep_check_parallel(chunk_size, psi_res2, &mut oep_rec_streams);

    // convert ZERO_PLACE_HOLDER back to 0
    let pmt2: Vec<usize> = ks
        .into_par_iter()
        .map(|v| {
            if v == 0 {
                ZERO_PLACE_HOLDER
            } else {
                v as usize
            }
        })
        .collect();

    // step3: run OEP to get correct res
    // pmt2.len() = s; vs_p_2.len() = n+s
    permutor_extended_permute(stream, &pmt2, &vs_p_2)
}

// assume no duplicate in sender key
pub fn basic_psi_shared_anno_sender_parallel<S: Stream>(
    ys: Vec<u64>,   // sender key
    vs_1: Vec<u32>, // sender anno_1
    tree: &SubProductTree<Fr>,
    receiver_size: usize, // s
    chunk_size: usize,
    stream: &mut S,
    self_id: u16,
    debug: bool,
    ys_len_larger: bool,
    psi_sen_streams: Vec<S>,
    mut oep_sen_streams: Vec<S>,
) -> Vec<u32> {
    let mut rng = get_fixed_rng();
    let mut extended_vs_1 = vs_1;
    extended_vs_1.extend(vec![0; receiver_size]); // n+s elements
    let n = ys.len();
    let new_size = n + receiver_size; // n + s

    let mut pmt1: Vec<usize> = (0..new_size).collect();
    pmt1.shuffle(&mut rng);
    let mut inv_pmt1 = inv_pmt(&pmt1);

    for ele in inv_pmt1.iter_mut() {
        if *ele == 0 {
            *ele = ZERO_PLACE_HOLDER;
            break;
        }
    }

    //run consensus for pmt1 and extended_vs_1
    let mut bytes = bincode::serialize(&pmt1).unwrap();
    bytes.append(&mut bincode::serialize(&extended_vs_1).unwrap());
    let dig = digest(Algorithm::SHA256, &bytes);
    if !debug {
        run_consensus(dig, self_id);
    }
    // println!("consensus for pmt1 and extended_vs_1");

    // step1: run OP to permute two extended_vs shares
    let vs_p_1 = permutor_permute(stream, &pmt1, &extended_vs_1);

    // step2: run PSI to share inv_pmt1 info
    let inv_pmt1_info: Vec<u64> = inv_pmt1[0..n].par_iter().map(|v| *v as u64).collect();
    let psi_res1 = basic_psi_anno_sender_parallel(
        ys,
        inv_pmt1_info,
        tree,
        stream,
        receiver_size,
        self_id,
        debug,
        ys_len_larger,
        psi_sen_streams,
    );

    // run OEP circuit
    let inv_pmt_u128: Vec<u128> = inv_pmt1.par_iter().map(|v| *v as u128).collect();

    gb_oep_check_parallel(
        chunk_size,
        psi_res1,
        &mut oep_sen_streams,
        inv_pmt_u128[n..].to_vec(),
    );

    // step3: run OEP to get correct res
    // vs_p_1.len() = n+s
    sender_extended_permute(stream, &vs_p_1, receiver_size)
}

pub fn basic_psi_shared_anno_receiver_parallel<S: Stream>(
    zs: Vec<u64>, // receiver key, s ele
    tree: &SubProductTree<Fr>,
    vs_2: Vec<u32>, // sender anno_2, n ele
    stream: &mut S,
    chunk_size: usize,
    self_id: u16,
    debug: bool,
    ys_len_larger: bool,
    psi_rec_streams: Vec<S>,
    mut oep_rec_streams: Vec<S>,
) -> Vec<u32> {
    let s = zs.len();
    let mut extended_vs_2 = vs_2;
    extended_vs_2.extend(vec![0; s]); // s + n elements

    //run consensus for extended_vs_2
    let bytes = bincode::serialize(&extended_vs_2).unwrap();
    let dig = digest(Algorithm::SHA256, &bytes);
    if !debug {
        run_consensus(dig, self_id);
    }
    // println!("consensus for extended_vs_2");

    // step1: run OP to permute two extended_vs shares
    let vs_p_2 = sender_permute(stream, &extended_vs_2);

    // step2: run PSI to share inv_pmt1 info
    let psi_res2 = basic_psi_anno_receiver_parallel(
        zs,
        stream,
        tree,
        self_id,
        debug,
        ys_len_larger,
        psi_rec_streams,
    );

    // run OEP circuit
    // pmt2 = ks
    let ks = ev_oep_check_parallel(chunk_size, psi_res2, &mut oep_rec_streams);

    // convert ZERO_PLACE_HOLDER back to 0
    let pmt2: Vec<usize> = ks
        .into_par_iter()
        .map(|v| {
            if v == 0 {
                ZERO_PLACE_HOLDER
            } else {
                v as usize
            }
        })
        .collect();
    // step3: run OEP to get correct res
    // pmt2.len() = s; vs_p_2.len() = n+s
    permutor_extended_permute(stream, &pmt2, &vs_p_2)
}

mod tests {

    use ark_bls12_381::Bls12_381;
    use ark_std::cfg_into_iter;
    use oblivious_transfer_protocols::ot_extensions::alsz_ote::{
        OTExtensionReceiverSetup, OTExtensionSenderSetup,
    };

    #[allow(dead_code)]
    fn rand_bool_vec(size: usize) -> Vec<bool> {
        (0..size).map(|_| rand::random::<bool>()).collect()
    }

    use ark_ec::pairing::Pairing;
    use rand::{rngs::StdRng, RngCore};

    #[test]
    fn test_otext_dynamic_size() {
        use super::*;
        use crate::{psi::OT_KEY_SIZE, utils::get_fixed_rng};
        use ark_std::UniformRand;

        let mut rng = get_fixed_rng();
        let b = G1::rand(&mut rng);

        let base_ot_cnt = 64;
        let extended_ot_cnt = 128; // LAMBDA
        let msg_size = 20; // N
        let choices = rand_bool_vec(extended_ot_cnt);
        // let base_ot_config = OTConfig::new_for_alsz_ote(base_ot_cnt).unwrap();
        check::<OT_KEY_SIZE>(
            &mut rng,
            base_ot_cnt,
            extended_ot_cnt,
            choices,
            msg_size,
            &b,
        );
    }

    #[allow(dead_code)]
    fn check<const KEY_SIZE: u16>(
        rng: &mut StdRng,
        base_ot_cnt: u16,
        extended_ot_cnt: usize,
        ot_ext_choices: Vec<bool>,
        msg_size: u32,
        b: &<Bls12_381 as Pairing>::G1Affine,
    ) {
        use crate::psi::do_1_of_2_base_ot;
        use oblivious_transfer_protocols::configs::OTEConfig;

        let msg_size = msg_size as usize;
        // base OT with roles reversed
        let (base_ot_choices, base_ot_sender_keys, base_ot_receiver_keys) =
            do_1_of_2_base_ot::<KEY_SIZE>(rng, base_ot_cnt, b);

        let ote_config = OTEConfig::new(base_ot_cnt, extended_ot_cnt as u32).unwrap();

        // OT extension
        let (ext_receiver_setup, u) =
            OTExtensionReceiverSetup::new(ote_config, ot_ext_choices.clone(), base_ot_sender_keys)
                .unwrap();

        assert_eq!(ext_receiver_setup.ot_extension_choices, ot_ext_choices);

        let base_ot_choices = base_ot_choices
            .into_iter()
            .map(|b| b % 2 != 0)
            .collect::<Vec<bool>>();
        let ext_sender_setup =
            OTExtensionSenderSetup::new(ote_config, u, base_ot_choices, base_ot_receiver_keys)
                .unwrap();

        let msgs = (0..extended_ot_cnt)
            .map(|_| {
                (
                    {
                        let mut bytes = vec![0u8; msg_size];
                        rng.fill_bytes(&mut bytes);
                        bytes
                    },
                    {
                        let mut bytes = vec![0u8; msg_size];
                        rng.fill_bytes(&mut bytes);
                        bytes
                    },
                )
            })
            .collect::<Vec<_>>();

        let timer1 = howlong::ProcessCPUTimer::new();
        let encryptions = ext_sender_setup
            .encrypt(msgs.clone(), msg_size as u32)
            .unwrap();

        let decryptions = ext_receiver_setup
            .decrypt(encryptions, msg_size as u32)
            .unwrap();
        let t = timer1.elapsed().real.as_micros() as u64;
        println!("time: {} ms", t / 1000);
        assert_eq!(decryptions.len(), extended_ot_cnt);

        cfg_into_iter!(decryptions)
            .enumerate()
            .for_each(|(i, dec)| {
                if !ext_receiver_setup.ot_extension_choices[i] {
                    assert_eq!(dec, msgs[i].0);
                } else {
                    assert_eq!(dec, msgs[i].1);
                }
                assert_eq!(dec.len(), msg_size);
            })
    }

    // seems OP only work when ys.len+zs.len is even
    #[test]
    fn test_basic_psi_shared_anno() {
        use super::*;
        use crate::utils::obtain_tcp_stream;
        use std::sync::mpsc;

        // sender key, no duplicate
        let ys = vec![1, 2, 3, 4, 5]; // n = 5
                                      // anno: [11, 12, 13, 14, 15]
        let vs_1 = vec![1, 1, 2, 1, 3];
        let vs_2 = vec![10, 11, 11, 13, 12];

        // let zs = vec![7, 9, 1, 3, 6];
        // let zs = vec![2, 4, 2, 7, 10]; // s = 5
        // let zs = vec![2, 4, 17, 8, 5, 11, 2, 7, 8, 9, 10]; // s = 11
        let zs = vec![2, 4, 7, 10, 11, 13, 21]; // s = 7
        
        let receiver_size = zs.len();
        let chunk_size = 1;
        let (mut stream_1_2, mut stream_2_1) = obtain_tcp_stream();
        let (tx_1, rx_1) = mpsc::channel();
        let (tx_2, rx_2) = mpsc::channel();

        let flag = zs.len() > ys.len();

        let thread_1 = std::thread::spawn(move || {
            let ys_pts = points_from_num(ys.clone());
            let ys_tree = SubProductTree::new_from_points_parallel(&ys_pts);
            let res_1 = basic_psi_shared_anno_sender(
                ys,
                vs_1,
                &ys_tree,
                receiver_size,
                chunk_size,
                &mut stream_1_2,
                0,
                true,
                flag,
            );
            tx_1.send(res_1).unwrap();
        });

        let thread_2 = std::thread::spawn(move || {
            let zs_pts = points_from_num(zs.clone());
            let zs_tree = SubProductTree::new_from_points_parallel(&zs_pts);
            let res_2 = basic_psi_shared_anno_receiver(
                zs,
                &zs_tree,
                vs_2,
                &mut stream_2_1,
                chunk_size,
                0,
                true,
                flag,
            );
            tx_2.send(res_2).unwrap();
        });

        thread_1.join().unwrap();
        thread_2.join().unwrap();
        let share1 = rx_1.recv().unwrap();
        let share2 = rx_2.recv().unwrap();

        let res: Vec<u32> = share1
            .into_iter()
            .zip(share2.into_iter())
            .map(|(a, b)| a.wrapping_add(b))
            .collect();

        println!("{:?}", res);
    }

    #[test]
    fn dbg_psi_anno() {
        use super::*;
        use crate::utils::obtain_tcp_stream;
        use std::sync::mpsc;

        let ys: Vec<u32> = vec![1, 2, 3, 4, 5];
        let anno: Vec<u32> = vec![11, 12, 13, 14, 15];
        // let zs: Vec<u32> = vec![2, 4, 2, 9, 1];
        let zs: Vec<u32> = vec![2, 4, 5, 9, 1, 3, 11, 12, 23, 42];
        // let zs: Vec<u32> = vec![2, 4, 8];
        let flag = zs.len() > ys.len();

        let receiver_size = zs.len();
        let chunk_size = 1;
        let (mut stream_1_2, mut stream_2_1) = obtain_tcp_stream();
        let (tx_1, rx_1) = mpsc::channel();
        let (tx_2, rx_2) = mpsc::channel();

        let debug = true;

        let thread_1 = std::thread::spawn(move || {
            let ys_pts = points_from_num(ys.clone());
            let ys_tree = SubProductTree::new_from_points_parallel(&ys_pts);
            let share1 = basic_psi_anno_sender(
                ys.into_iter().map(|x| x as u64).collect(),
                anno.into_iter().map(|x| x as u64).collect(),
                &ys_tree,
                &mut stream_1_2,
                receiver_size,
                chunk_size,
                0,
                debug,
                flag,
            );
            // println!("share1: {:?}", share1);
            tx_1.send(share1).unwrap();
        });

        let thread_2 = std::thread::spawn(move || {
            let zs_pts = points_from_num(zs.clone());
            let zs_tree = SubProductTree::new_from_points_parallel(&zs_pts);

            let share2 = basic_psi_anno_receiver(
                zs.into_iter().map(|x| x as u64).collect(),
                &mut stream_2_1,
                &zs_tree,
                chunk_size,
                0,
                debug,
                flag,
            );
            // println!("share2: {:?}", share2);
            tx_2.send(share2).unwrap();
        });

        thread_1.join().unwrap();
        thread_2.join().unwrap();
        let share1 = rx_1.recv().unwrap();
        let share2 = rx_2.recv().unwrap();
        let res: Vec<u128> = share1
            .into_iter()
            .zip(share2.into_iter())
            .map(|(a, b)| a.wrapping_add(b))
            .collect();
        println!("{:?}", res);
    }
}
