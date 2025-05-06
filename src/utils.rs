use std::{
    collections::HashSet, fs::File, io::{Read, Write}, net::{TcpListener, TcpStream}, os::unix::net::UnixStream, path::PathBuf
};

use anyhow::{Error, Result};
use ark_bls12_381::{Fr, FrConfig};
use ark_ff::{BigInt, BigInteger, Fp, MontBackend};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use rand::{
    distributions::Standard, prelude::Distribution, rngs::StdRng, thread_rng, Rng, SeedableRng,
};
use rayon::iter::{
    IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, ParallelIterator,
};
use tracing_subscriber::filter::EnvFilter;

use crate::{BASE_PORT, PARALLEL_BASE_PORT, SEED, SEED2};

pub fn points_to_u128(points: Vec<Fr>) -> Vec<u128> {
    points
        .into_par_iter()
        .map(|point| {
            let le_bytes = point.into_bigint().to_bytes_le();
            let u128_le_bytes: [u8; 16] = le_bytes[0..16].try_into().unwrap();
            u128::from_le_bytes(u128_le_bytes)
        })
        .collect()
}

pub fn points_from_num<T: Copy + Send + Sync>(vals: Vec<T>) -> Vec<Fr>
where
    Fp<MontBackend<FrConfig, 4>, 4>: From<T>,
{
    vals.par_iter().map(|val| Fr::from(*val)).collect()
}

pub fn init_tracing_subscriber(directives: &str) -> Result<()> {
    let filter = EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new(directives));

    tracing_subscriber::fmt()
        .with_env_filter(filter)
        .try_init()
        .map_err(Error::msg)
}

pub fn gen_random<T: Eq + Ord + std::hash::Hash>(n: usize) -> Vec<T>
where
    Standard: Distribution<T>,
{
    let mut rng = get_fixed_rng();
    (0..n).map(|_| rng.gen::<T>()).collect()
}
pub fn gen_unique_random_sorted<T: Eq + Ord + std::hash::Hash>(n: usize) -> Vec<T>
where
    Standard: Distribution<T>,
{
    let mut res = gen_unique_random_unsorted(n);
    res.sort();
    res
}

pub fn gen_unique_random_unsorted<T: Eq + std::hash::Hash>(n: usize) -> Vec<T>
where
    Standard: Distribution<T>,
{
    let mut rng = thread_rng();
    let mut nums = HashSet::new();
    while nums.len() < n {
        nums.insert(rng.gen::<T>());
    }
    let res: Vec<T> = nums.into_iter().collect();
    res
}

pub fn get_fixed_rng() -> StdRng {
    let seed = SEED;
    let rng: StdRng = SeedableRng::seed_from_u64(seed);
    rng
}

pub fn get_fixed_rng2() -> StdRng {
    let seed = SEED2;
    let rng: StdRng = SeedableRng::seed_from_u64(seed);
    rng
}

pub(crate) fn combine_share(a: Vec<u128>, b: Vec<u128>) -> Vec<u128> {
    a.into_par_iter()
        .zip(b.into_par_iter())
        .map(|(a, b)| a.wrapping_add(b))
        .collect()
}

pub(crate) fn combine_share_u32(a: Vec<u32>, b: Vec<u32>) -> Vec<u32> {
    a.into_par_iter()
        .zip(b.into_par_iter())
        .map(|(a, b)| a.wrapping_add(b))
        .collect()
}

pub fn rand_bool_vec_with_fixed_seed(size: usize) -> Vec<bool> {
    let mut rng = get_fixed_rng();
    (0..size).map(|_| rng.gen::<bool>()).collect()
}

pub fn lazy_sk_from_u128(num: u128) -> Vec<bool> {
    let mut bits = Vec::new();
    for i in (0..128).rev() {
        bits.push((num >> i) & 1 == 1);
    }
    bits
}

pub fn bytes_to_fr(bytes: Vec<u8>) -> Fr {
    let byte_slice: [u8; 16] = bytes.try_into().unwrap();
    let val = u128::from_le_bytes(byte_slice);
    Fr::from(val)
}

pub fn gen_data(n: usize, path: &PathBuf) {
    let data: Vec<u64> = gen_unique_random_unsorted(n);
    let json_data = serde_json::to_string(&data).unwrap();

    let mut file = File::create(path).unwrap();
    file.write_all(json_data.as_bytes()).unwrap();
}

pub fn read_data(path: &PathBuf) -> Vec<u64> {
    let mut file = File::open(path).unwrap();
    let mut json_string = String::new();
    file.read_to_string(&mut json_string).unwrap();

    let data: Vec<u64> = serde_json::from_str(&json_string).unwrap();
    data
}

// ~3x slower than fr_xor
use ark_ff::PrimeField;
pub fn fr_xor2(fr1: &Fr, fr2: &Fr) -> Fr {
    let bits1 = fr1.into_bigint().to_bits_be();
    let bits2 = fr2.into_bigint().to_bits_be();
    let mut res_bits = Vec::with_capacity(bits1.len().max(bits2.len()));

    for (bit1, bit2) in bits1.iter().zip(bits2.iter()) {
        res_bits.push(bit1 ^ bit2);
    }

    Fr::from(BigInt::<4>::from_bits_be(&res_bits))
}

// ~3x faster than fr_xor2
pub fn fr_xor(fr1: &Fr, fr2: &Fr) -> Fr {
    let mut fr1_bytes: Vec<u8> = vec![];
    fr1.serialize_uncompressed(&mut fr1_bytes).unwrap();

    let mut fr2_bytes: Vec<u8> = vec![];
    fr2.serialize_uncompressed(&mut fr2_bytes).unwrap();

    let mut res_bytes = vec![0u8; fr1_bytes.len()];
    for i in 0..32 {
        res_bytes[i] = fr1_bytes[i] ^ fr2_bytes[i];
    }

    Fr::deserialize_uncompressed(&*res_bytes).unwrap()
}

pub fn gen_rand_from_fixed_seed<T>() -> T
where
    Standard: Distribution<T>,
{
    let mut rng = get_fixed_rng();
    rng.gen::<T>()
}

pub fn combine_shares_xor(share1: &Vec<u128>, share2: &Vec<u128>) -> Vec<u128> {
    assert_eq!(share1.len(), share2.len());
    share1
        .iter()
        .zip(share2.iter())
        .map(|(a, b)| a ^ b)
        .collect()
}

pub fn strict_split<T>(vec: Vec<T>, chunk_size: usize) -> Vec<Vec<T>> {
    let size = vec.len();
    if size % chunk_size != 0 {
        panic!("invalid chunk size");
    }

    let mut vec_iter = vec.into_iter().peekable();
    let mut chunks = vec![];
    while vec_iter.peek().is_some() {
        let chunk: Vec<T> = vec_iter.by_ref().take(chunk_size).collect();
        chunks.push(chunk);
    }
    chunks
}

pub fn split_by_chunk_size<T>(vec: Vec<T>, chunk_size: usize) -> Vec<Vec<T>> {
    let mut vec_iter = vec.into_iter().peekable();
    let mut chunks = vec![];
    while vec_iter.peek().is_some() {
        let chunk: Vec<T> = vec_iter.by_ref().take(chunk_size).collect();
        chunks.push(chunk);
    }
    chunks
}


pub fn split_by<T: Clone>(vec: Vec<T>, n: usize) -> Vec<Vec<T>> {
    if n == 0 {
        return vec![];
    }

    let chunk_size = (vec.len() as f64 / n as f64).ceil() as usize;
    vec.chunks(chunk_size).map(|chunk| chunk.to_vec()).collect()
}

pub fn run_consensus(info: Vec<u8>, self_id: u16) {
    crate::increase_consensus();
    let addr = format!("127.0.0.1:{}", BASE_PORT + self_id);
    let mut stream = std::net::TcpStream::connect(addr).unwrap();
    std::io::Write::write_all(&mut stream, &info).unwrap();
    let mut buf = vec![0u8; 1024];
    let len = stream.read(&mut buf).unwrap();
    let _response: u8 = bincode::deserialize(&buf[..len]).unwrap();

    // if response != OK {
    // println!("Consensus not reached!!!")
    // } else {
    // println!("Consensus!!!")
    // }
}

pub fn obtain_tcp_stream() -> (TcpStream, TcpStream) {
    let thread1 = std::thread::spawn(move || tcp_listeners(1, 200));
    let thread2 = std::thread::spawn(move || tcp_connectors(1, 200));

    let sen = thread2.join().unwrap().remove(0);
    let rec = thread1.join().unwrap().remove(0);
    (sen, rec)
}

pub(crate) fn obtain_unix_streams(
    target_cnt: usize,
) -> (Vec<UnixStream>, Vec<UnixStream>) {

    let mut senders = vec![];
    let mut receivers = vec![];
    for _ in 0..target_cnt {
        let (s, r) = UnixStream::pair().unwrap();
        senders.push(s);
        receivers.push(r);
    }
    (senders, receivers)
}

pub(crate) fn obtain_tcp_streams(
    target_cnt: usize,
    self_id: u16,
) -> (Vec<TcpStream>, Vec<TcpStream>) {
    let thread1 = std::thread::spawn(move || tcp_listeners(target_cnt, self_id));
    let thread2 = std::thread::spawn(move || tcp_connectors(target_cnt, self_id));

    let sends = thread2.join().unwrap();
    let recvs = thread1.join().unwrap();
    (sends, recvs)
}

fn tcp_connectors(target_cnt: usize, self_id: u16) -> Vec<TcpStream> {
    let mut streams = vec![];
    let port = PARALLEL_BASE_PORT + self_id;
    loop {
        let stream = TcpStream::connect(format!("127.0.0.1:{}", port));
        match stream {
            Ok(stream) => {
                streams.push(stream);
            }
            Err(_) => {}
        }
        if streams.len() >= target_cnt {
            break;
        }
    }
    streams
}

fn tcp_listeners(target_cnt: usize, self_id: u16) -> Vec<TcpStream> {
    let port = PARALLEL_BASE_PORT + self_id;
    let mut streams = vec![];
    let listener = TcpListener::bind(format!("127.0.0.1:{}", port)).unwrap();
    for stream in listener.incoming() {
        match stream {
            Ok(stream) => {
                streams.push(stream);
            }
            Err(e) => {
                eprintln!("err accepting connection: {}", e);
            }
        }
        if streams.len() >= target_cnt {
            break;
        }
    }
    streams
}

mod tests {

    #[test]
    fn test_sk_gen() {
        use crate::utils::lazy_sk_from_u128;
        use rand::prelude::*;

        let mut rng = rand::thread_rng();
        let num: u128 = rng.gen();

        println!("{}", num);
        let sk = lazy_sk_from_u128(num);
        println!("{:?}", sk);

        for _ in 0..10 {
            let bit: bool = rng.gen();
            println!("{}", bit);
        }
    }

    #[test]
    fn test_ark_serialize() {
        use super::*;
        use crate::psi::poly::Poly;
        use ark_bls12_381::Fr;
        use ark_poly::DenseUVPolynomial;
        use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

        let eles = vec![Fr::from(2), Fr::from(3)];
        let mut bytes: Vec<u8> = vec![];
        eles.serialize_uncompressed(&mut bytes).unwrap();
        let ele_prim: Vec<Fr> = Vec::deserialize_uncompressed(&*bytes).unwrap();
        assert_eq!(eles, ele_prim);

        let poly = Poly::from_coefficients_vec(points_from_num(vec![1, 2, 1, 3]));

        let mut bytes: Vec<u8> = vec![];
        poly.serialize_uncompressed(&mut bytes).unwrap();
        let poly_prim: Poly<Fr> = Poly::deserialize_uncompressed(&*bytes).unwrap();

        assert_eq!(poly, poly_prim);
    }

    #[test]
    fn test_xor() {
        use super::{fr_xor, fr_xor2};
        use ark_bls12_381::Fr;

        let a = 13u64;
        let b = 25u64;
        let c = a ^ b;
        let fr_a = Fr::from(a);
        let fr_b = Fr::from(b);
        let fr_c = fr_xor(&fr_a, &fr_b);
        let fr_c2 = fr_xor2(&fr_a, &fr_b);
        assert_eq!(Fr::from(c), fr_c);
        assert_eq!(fr_c2, fr_c);

        let a = Fr::from(24);
        let b = Fr::from(434);
        let c = fr_xor(&a, &b);
        let d = fr_xor(&c, &b);
        assert_eq!(a, d);
        let c = fr_xor2(&a, &b);
        let d = fr_xor2(&c, &b);
        assert_eq!(a, d);
    }

    // xor is about 3x faster than xor2
    #[test]
    fn test_xor_performance() {
        use crate::utils::{fr_xor, fr_xor2, gen_unique_random_unsorted, points_from_num};

        let size = 10000;
        let xs = points_from_num(gen_unique_random_unsorted::<u64>(size));
        let ys = points_from_num(gen_unique_random_unsorted::<u64>(size));

        let mut res1 = vec![];
        let mut res2 = vec![];
        let timer1 = howlong::ProcessCPUTimer::new();
        for i in 0..size {
            res1.push(fr_xor(&xs[i], &ys[i]));
        }
        let t = timer1.elapsed().real.as_micros() as u64;
        println!("time for xor: {} ms", t / 1000);

        let timer2 = howlong::ProcessCPUTimer::new();
        for i in 0..size {
            res2.push(fr_xor2(&xs[i], &ys[i]));
        }
        let t = timer2.elapsed().real.as_micros() as u64;
        println!("time for xor2: {} ms", t / 1000);
    }

    #[test]
    fn test_fr_u128() {
        use super::*;
        use ark_bls12_381::Fr;
        use rand::Rng;

        let mut rng = rand::thread_rng();
        let mut pts = vec![];
        let mut u128s = vec![];
        for _ in 0..1000 {
            let r: u128 = rng.gen();
            u128s.push(r);
            pts.push(Fr::from(r));
        }
        let pts_u128 = points_to_u128(pts);
        assert_eq!(u128s, pts_u128);
    }

    #[test]
    fn test_run_con() {
        use super::*;

        let thread_1 = std::thread::spawn(move || {
            let info = vec![1; 32];
            run_consensus(info, 0);
        });
        let thread_2 = std::thread::spawn(move || {
            let info = vec![1; 32];
            run_consensus(info, 1);
        });

        let thread_3 = std::thread::spawn(move || {
            let info = vec![1; 32];
            run_consensus(info, 2);
        });
        let thread_4 = std::thread::spawn(move || {
            let info = vec![1; 32];
            run_consensus(info, 3);
        });

        thread_1.join().unwrap();
        thread_2.join().unwrap();
        thread_3.join().unwrap();
        thread_4.join().unwrap();
    }
}
