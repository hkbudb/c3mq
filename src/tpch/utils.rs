use std::{
    hash::{DefaultHasher, Hash, Hasher},
    net::{TcpListener, TcpStream},
};

use rand::Rng;
use rayon::iter::{
    IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, ParallelIterator,
};

use crate::{
    psi::utils::{receive_data_by_stream, send_data_by_stream},
    utils::{combine_share, combine_share_u32, gen_random, get_fixed_rng},
    N, PARALLEL_BASE_PORT,
};

use super::{Stream, MACHINE_ADDRS};

pub fn string_to_hash_u32(s: &str) -> u32 {
    let mut hasher = DefaultHasher::new();
    s.hash(&mut hasher);
    (hasher.finish() & 0xFFFFFFFF) as u32
}

pub(crate) fn gen_shared_anno(anno: Vec<u128>) -> (Vec<u128>, Vec<u128>) {
    let size = anno.len();
    let share1: Vec<u128> = gen_random::<u128>(size);
    let share2: Vec<u128> = anno
        .par_iter()
        .zip(share1.par_iter())
        .map(|(a, b)| a.wrapping_sub(*b))
        .collect();
    (share1, share2)
}

pub(crate) fn share_128_to_32(s1: Vec<u128>, s2: Vec<u128>) -> (Vec<u32>, Vec<u32>) {
    let combine = combine_share(s1, s2);
    let size = combine.len();
    let mut rng = get_fixed_rng();
    let s1: Vec<u32> = (0..size).map(|_| rng.gen::<u32>()).collect();
    let s2 = combine
        .into_par_iter()
        .zip(s1.par_iter())
        .map(|(a, b)| (a as u32).wrapping_sub(*b))
        .collect();

    (s1, s2)
}

pub(crate) fn share_32_to_128(s1: Vec<u32>, s2: Vec<u32>) -> (Vec<u128>, Vec<u128>) {
    let combine = combine_share_u32(s1, s2);
    let size = combine.len();
    let mut rng = get_fixed_rng();
    let s1: Vec<u128> = (0..size).map(|_| rng.gen::<u128>()).collect();
    let s2 = combine
        .into_par_iter()
        .zip(s1.par_iter())
        .map(|(a, b)| (a as u128).wrapping_sub(*b))
        .collect();

    (s1, s2)
}

// this unsafe converting is caused by the fact we use different secret-sharing (u128 share and u32 share), the convert can be avoided by using the same data type sharing, which would be implemented in the future
pub(crate) fn sen_u128_to_u32<S: Stream>(
    sender_share: Vec<u128>,
    rx: &mut S,
    tx: &mut S,
) -> Vec<u32> {
    let bytes = receive_data_by_stream(rx);
    let rec_share: Vec<u128> = bincode::deserialize(&bytes).unwrap();
    let (s1, s2) = share_128_to_32(sender_share, rec_share);
    let sen_bytes = bincode::serialize(&s1).unwrap();
    send_data_by_stream(tx, &sen_bytes, true);
    s2
}

pub(crate) fn rec_u128_to_u32<S: Stream>(
    rec_share: Vec<u128>,
    tx: &mut S,
    rx: &mut S,
) -> Vec<u32> {
    let bytes = bincode::serialize(&rec_share).unwrap();
    send_data_by_stream(tx, &bytes, true);
    let rec_bytes = receive_data_by_stream(rx);
    let s1: Vec<u32> = bincode::deserialize(&rec_bytes).unwrap();
    s1
}

pub(crate) fn batch_sen_u128_to_u32<S: Stream>(
    sen_shares: Vec<Vec<u128>>,
    rx: &mut S,
    tx: &mut S,
) -> Vec<Vec<u32>> {
    let bytes = receive_data_by_stream(rx);
    let rec_shares: Vec<Vec<u128>> = bincode::deserialize(&bytes).unwrap();
    let mut s1s = vec![];
    let mut s2s = vec![];
    for (sen_share, rec_share) in sen_shares.into_iter().zip(rec_shares.into_iter()) {
        let (s1, s2) = share_128_to_32(sen_share, rec_share);
        s1s.push(s1);
        s2s.push(s2);
    }

    let sen_bytes = bincode::serialize(&s1s).unwrap();
    send_data_by_stream(tx, &sen_bytes, true);
    s2s
}

pub(crate) fn batch_rec_u128_to_u32<S: Stream>(
    rec_shares: Vec<Vec<u128>>,
    tx: &mut S,
    rx: &mut S,
) -> Vec<Vec<u32>> {
    let bytes = bincode::serialize(&rec_shares).unwrap();
    send_data_by_stream(tx, &bytes, true);
    let rec_bytes = receive_data_by_stream(rx);
    bincode::deserialize(&rec_bytes).unwrap()
}

pub(crate) fn batch_sen_u32_to_u128<S: Stream>(
    sen_shares: Vec<Vec<u32>>,
    rx: &mut S,
    tx: &mut S,
) -> Vec<Vec<u128>> {
    let bytes = receive_data_by_stream(rx);
    let rec_shares: Vec<Vec<u32>> = bincode::deserialize(&bytes).unwrap();
    let mut s1s = vec![];
    let mut s2s = vec![];
    for (sen_share, rec_share) in sen_shares.into_iter().zip(rec_shares.into_iter()) {
        let (s1, s2) = share_32_to_128(sen_share, rec_share);
        s1s.push(s1);
        s2s.push(s2);
    }
    let sen_bytes = bincode::serialize(&s1s).unwrap();
    send_data_by_stream(tx, &sen_bytes, true);
    s2s
}

pub(crate) fn sen_u32_to_u128<S: Stream>(
    sender_share: Vec<u32>,
    rx: &mut S,
    tx: &mut S,
) -> Vec<u128> {
    let bytes = receive_data_by_stream(rx);
    let rec_share: Vec<u32> = bincode::deserialize(&bytes).unwrap();
    let (s1, s2) = share_32_to_128(sender_share, rec_share);
    let sen_bytes = bincode::serialize(&s1).unwrap();
    send_data_by_stream(tx, &sen_bytes, true);
    s2
}

pub(crate) fn batch_rec_u32_to_u128<S: Stream>(
    rec_shares: Vec<Vec<u32>>,
    tx: &mut S,
    rx: &mut S,
) -> Vec<Vec<u128>> {
    let bytes = bincode::serialize(&rec_shares).unwrap();
    send_data_by_stream(tx, &bytes, true);
    let rec_bytes = receive_data_by_stream(rx);
    bincode::deserialize(&rec_bytes).unwrap()
}

pub(crate) fn rec_u32_to_u128<S: Stream>(
    rec_share: Vec<u32>,
    tx: &mut S,
    rx: &mut S,
) -> Vec<u128> {
    let bytes = bincode::serialize(&rec_share).unwrap();
    send_data_by_stream(tx, &bytes, true);
    let rec_bytes = receive_data_by_stream(rx);
    bincode::deserialize(&rec_bytes).unwrap()
}

pub(crate) fn split_vec_evenly<T: Clone>(input: &Vec<T>) -> Vec<Vec<T>> {
    let chunk_size = (input.len() + N as usize - 1) / (N as usize);
    input
        .chunks(chunk_size)
        .map(|chunk| chunk.to_vec())
        .collect()
}

pub fn multi_machine_connectors(
    target_cnt: usize,
    self_id: u16,
    machine: &str,
) -> Vec<TcpStream> {
    let mut streams = vec![];
    let port = PARALLEL_BASE_PORT + self_id;
    let addr = MACHINE_ADDRS.get(machine).unwrap();
    loop {
        let stream = TcpStream::connect(format!("{}:{}", addr, port));
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

pub fn multi_machine_listeners(target_cnt: usize, self_id: u16) -> Vec<TcpStream> {
    let port = PARALLEL_BASE_PORT + self_id;
    let mut streams = vec![];
    let listener = TcpListener::bind(format!("0.0.0.0:{}", port)).unwrap();
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
    fn test_string_u32() {
        use super::*;

        let str = "abcde";
        let val = string_to_hash_u32(str);
        println!("{}", val);
    }

    #[test]
    fn test_gen_share() {
        use super::*;
        let anno = vec![1, 2, 3, 2, 3, 2];
        let (s1, s2) = gen_shared_anno(anno.clone());
        let res = crate::utils::combine_share(s1, s2);
        assert_eq!(anno, res);
    }

    #[test]
    fn test_split() {
        use super::*;
        let vec = vec![1, 2, 3, 4, 5, 6, 7, 8, 9];
        let vecs = split_vec_evenly(&vec);
        println!("{:?}", vecs);
    }
}
