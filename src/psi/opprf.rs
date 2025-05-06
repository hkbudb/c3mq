use std::{
    collections::HashSet,
    io::{Read, Write},
};

use crypto_hash::{digest, Algorithm};
use oblivious_transfer_protocols::{
    base_ot::simplest_ot::{OneOfTwoROTSenderKeys, ROTReceiverKeys},
    configs::OTEConfig,
    ot_extensions::alsz_ote::{OTExtensionReceiverSetup, OTExtensionSenderSetup},
    BitMatrix,
};
use rand::prelude::*;
use rayon::iter::{IntoParallelIterator, IntoParallelRefIterator, ParallelIterator};

use crate::{
    utils::{get_fixed_rng2, lazy_sk_from_u128},
    ValType,
};

use super::{
    base_ot_setup,
    utils::{receive_data_by_stream, send_data_by_stream},
};

pub const LAMBDA: usize = 128;

// Should generate the sk on-the-fly
pub const LAZY_SK: u128 = 31789938986303995450111839370617466219;

#[derive(PartialEq, Debug)]
pub struct Matrix {
    pub height: usize,
    pub width: usize,
    pub vals: Vec<bool>, // 1D matrix to represent 2D height*width matrix
}

impl Matrix {
    pub fn new(height: usize, width: usize) -> Self {
        Self {
            height,
            width,
            vals: vec![false; height * width],
        }
    }

    pub fn get_col_as_u8(&self, col: usize) -> Vec<u8> {
        let mut res = vec![];
        for i in 0..self.height {
            res.push(self.vals[i * self.width + col] as u8)
        }
        res
    }

    pub fn from_u8_vec(data: &Vec<Vec<u8>>) -> Self {
        let width = data.len();
        let height = data[0].len();

        let transposed: Vec<Vec<u8>> = (0..height)
            .map(|i| data.iter().map(|row| row[i]).collect())
            .collect();
        let vals: Vec<bool> = transposed
            .iter()
            .flat_map(|col| col.iter())
            .map(|v| if *v == 0 { false } else { true })
            .collect();

        Self {
            height,
            width,
            vals,
        }
    }

    pub fn gen_r0(height: usize, width: usize) -> Self {
        let mut rng = get_fixed_rng2();
        Self {
            height,
            width,
            vals: (0..height * width).map(|_| rng.gen()).collect(),
        }
    }

    // a pesudorandom function implementation using simple hash
    // return the chosen positions of 2D matrix in the 1D vector
    fn prf(&self, num: &ValType) -> Vec<usize> {
        let mut pos = vec![];
        for i in 0..self.width {
            let data = if let Some(sum) = num.checked_add(i as u64) {
                sum.to_le_bytes()
            } else {
                (num - i as u64).to_le_bytes()
            };
            let dig_bytes: [u8; 16] = digest(Algorithm::MD5, &data).try_into().unwrap();
            let idx = u128::from_le_bytes(dig_bytes) as usize % self.height;
            pos.push(idx * self.width + i);
        }
        pos
    }

    pub fn gen_r1(&self, inputs: &Vec<ValType>) -> Self {
        let mut r1 = Self::new(self.height, self.width);
        let mut visited_pos = HashSet::<usize>::new();
        for input in inputs {
            let idxs = self.prf(input);
            for idx in idxs.into_iter() {
                // copy corresponding values from r0
                r1.vals[idx] = self.vals[idx];
                visited_pos.insert(idx);
            }
        }
        for (i, val) in r1.vals.iter_mut().enumerate() {
            if !visited_pos.contains(&i) {
                *val = !self.vals[i];
            }
        }
        r1
    }

    #[allow(dead_code)]
    pub(crate) fn cal_dig(&self) -> String {
        let mut bytes = vec![];
        for val in &self.vals {
            bytes.push(*val as u8);
        }

        crypto_hash::hex_digest(crypto_hash::Algorithm::SHA256, &bytes)
    }
}

// debug version
#[allow(dead_code)]
pub(crate) fn dbg_gen_alice_matrix(s: Vec<bool>, r0: &Matrix, r1: &Matrix) -> Matrix {
    let mut res = Matrix::new(r0.height, r0.width);
    for (pos, bit) in s.iter().enumerate() {
        for i in 0..r0.height {
            let idx = pos + i * r0.width;
            res.vals[idx] = if *bit { r1.vals[idx] } else { r0.vals[idx] };
        }
    }

    res
}

pub fn sender_gen_alice_matrix<T: Read + Write>(
    msgs: Vec<(Vec<u8>, Vec<u8>)>,
    msg_size: usize,
    stream: &mut T,
    base_ot_choices: Vec<u16>,
    ote_config: OTEConfig,
    base_ot_receiver_keys: ROTReceiverKeys,
) {
    let data = receive_data_by_stream(stream);
    let u: BitMatrix = bincode::deserialize(&data).expect("failed to deserialize");
    let base_ot_choices: Vec<bool> = base_ot_choices
        .into_par_iter()
        .map(|b| b % 2 != 0)
        .collect();
    let ext_sender_setup =
        OTExtensionSenderSetup::new(ote_config, u, base_ot_choices, base_ot_receiver_keys).unwrap();

    let encryptions = ext_sender_setup.encrypt(msgs, msg_size as u32).unwrap();

    send_data_by_stream(
        stream,
        &bincode::serialize(&encryptions).expect("Failed to serialize encryption"),
        true
    );
}

pub fn receiver_gen_alice_matrix<T: Read + Write>(
    choices: Vec<bool>,
    stream: &mut T,
    ote_config: OTEConfig,
    base_ot_sender_keys: OneOfTwoROTSenderKeys,
    msg_size: usize,
) -> Matrix {
    let (ext_receiver_setup, u) =
        OTExtensionReceiverSetup::new(ote_config, choices, base_ot_sender_keys).unwrap();
    send_data_by_stream(
        stream,
        &bincode::serialize(&u).expect("Failed to serialize u"),
        true
    );
    let data = receive_data_by_stream(stream);
    let encryptions: Vec<(Vec<u8>, Vec<u8>)> =
        bincode::deserialize(&data).expect("failed to deserialize");

    let decryptions = ext_receiver_setup
        .decrypt(encryptions, msg_size as u32)
        .unwrap();

    Matrix::from_u8_vec(&decryptions)
}

// difference: bob has r1, which is only valid for bob's input Y
// alice has alice_matrix, which is valid for any input
pub fn oprf(matrix: &Matrix, num: &ValType) -> Vec<u8> {
    let mut bytes = Vec::<u8>::new();
    let idxs = matrix.prf(num);

    for idx in idxs {
        if matrix.vals[idx] {
            bytes.push(1);
        } else {
            bytes.push(0);
        }
    }
    digest(Algorithm::MD5, &bytes)
}

// input: {x_i}, output: ({x'_i=F(k,x_i)^y_star}, y_star)
pub fn alice_opprf<T: Read + Write>(
    stream: &mut T,
    xs: &Vec<u64>,
    ys_len_larger: bool,
) -> (Vec<u128>, u128) {
    let base_ot_cnt = 64;
    let ext_ot_cnt = LAMBDA;
    let msg_size = xs.len();

    // todo: base ot setup can be done off-line
    // constant, 10ms, no need to be off-line
    let (_, base_ot_sender_keys, _) = base_ot_setup(base_ot_cnt);

    let ote_config = OTEConfig::new(base_ot_cnt, ext_ot_cnt as u32).unwrap();

    let s = lazy_sk_from_u128(LAZY_SK);

    let alice_matrix =
        receiver_gen_alice_matrix(s, stream, ote_config, base_ot_sender_keys, msg_size);

    let y_star = get_fixed_rng2().gen::<u128>();
    // let mut xs_prim = vec![];
    // for x in xs {
    //     let val = oprf(&alice_matrix, x);
    //     let f_x = u128::from_le_bytes(val.try_into().unwrap());
    //     xs_prim.push(f_x ^ y_star)
    // }
    let xs_prim: Vec<u128> = xs
        .par_iter()
        .map(|x| {
            let val = oprf(&alice_matrix, x);
            let f_x = u128::from_le_bytes(val.try_into().unwrap());
            f_x ^ y_star
        })
        .collect();
    if ys_len_larger {
        safe_alice_oprf(xs)
    } else {
        (xs_prim, y_star)
    }
}

pub fn bob_opprf<T: Read + Write>(stream: &mut T, ys: &Vec<u64>, ys_len_larger: bool) -> Vec<u128> {
    let base_ot_cnt = 64;
    let ext_ot_cnt = LAMBDA;
    let msg_size = ys.len();

    let (base_ot_choices, _, base_ot_receiver_keys) = base_ot_setup(base_ot_cnt);

    let ote_config = OTEConfig::new(base_ot_cnt, ext_ot_cnt as u32).unwrap();

    let r0 = Matrix::gen_r0(ys.len(), LAMBDA);
    let r1 = r0.gen_r1(&ys);
    let mut msgs = vec![];
    for i in 0..r0.width {
        let m0 = r0.get_col_as_u8(i);
        let m1 = r1.get_col_as_u8(i);
        msgs.push((m0, m1));
    }

    sender_gen_alice_matrix(
        msgs,
        msg_size,
        stream,
        base_ot_choices,
        ote_config,
        base_ot_receiver_keys,
    );

    let mut f_ys = vec![];
    for y in ys {
        let val = oprf(&r1, y);
        f_ys.push(u128::from_le_bytes(val.try_into().unwrap()));
    }
    if ys_len_larger {
        return safe_bob_oprf(ys);
    } else {
        f_ys
    }
}

// when ys.len() > xs.len(), the original function will produce incorrect res
// here we use sk to do local prf to guarantee the correct res after the oblivious operation, the secure performance can only be better than our simulation
fn safe_alice_oprf(xs: &Vec<u64>) -> (Vec<u128>, u128) {
    let r = crate::utils::get_fixed_rng2().gen::<u128>();

    let k_bytes = LAZY_SK.to_le_bytes();

    // x'_i=F(k,x_i)^r
    // let mut res = vec![];
    // for x in xs {
    //     let bytes = [(*x as u128).to_le_bytes(), k_bytes].concat();
    //     let dig_bytes = digest(Algorithm::MD5, &bytes);
    //     res.push(u128::from_le_bytes(dig_bytes.try_into().unwrap()) ^ r);
    // }
    let res: Vec<u128> = xs
        .par_iter()
        .map(|x| {
            let bytes = [(*x as u128).to_le_bytes(), k_bytes].concat();
            let dig_bytes = digest(Algorithm::MD5, &bytes);
            u128::from_le_bytes(dig_bytes.try_into().unwrap()) ^ r
        })
        .collect();
    (res, r)
}

pub(crate) fn safe_bob_oprf(ys: &Vec<u64>) -> Vec<u128> {
    let k_bytes = LAZY_SK.to_le_bytes();

    // y'_i=F(k,y_i)
    // let mut res = vec![];
    // for y in ys {
    //     let bytes = [(*y as u128).to_le_bytes(), k_bytes].concat();
    //     let dig_bytes = digest(Algorithm::MD5, &bytes);
    //     res.push(u128::from_le_bytes(dig_bytes.try_into().unwrap()));
    // }
    let res: Vec<u128> = ys
        .par_iter()
        .map(|y| {
            let bytes = [(*y as u128).to_le_bytes(), k_bytes].concat();
            let dig_bytes = digest(Algorithm::MD5, &bytes);
            u128::from_le_bytes(dig_bytes.try_into().unwrap())
        })
        .collect();
    res
}

mod tests {
    


    #[test]
    fn test_matrix() {
        use crate::psi::opprf::Matrix;

        let width = 5;
        let height = 4;
        let vals: Vec<u8> = vec![0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0];

        let mut vals_bool = vec![];
        for val in vals {
            if val == 0 {
                vals_bool.push(false);
            } else {
                vals_bool.push(true);
            }
        }
        let matrix1 = Matrix {
            height,
            width,
            vals: vals_bool,
        };

        let vec1 = vec![0, 1, 0, 1];
        let vec2 = vec![0, 1, 1, 0];
        let vec3 = vec![1, 1, 0, 1];
        let vec4 = vec![0, 0, 1, 1];
        let vec5 = vec![1, 0, 1, 0];
        let matrix2 = Matrix::from_u8_vec(&vec![vec1, vec2, vec3, vec4, vec5]);

        assert_eq!(matrix1, matrix2);
    }

    // it seems that OPRF does NOT work well when receiver has more data than sender
    #[test]
    fn test_oprf() {
        use super::*;
        use crate::psi::opprf::LAZY_SK;
        use crate::utils::lazy_sk_from_u128;

        let ys = vec![1, 2, 3, 5, 7, 8, 9, 11, 13];

        let r0 = Matrix::gen_r0(ys.len(), LAMBDA);

        let r1 = r0.gen_r1(&ys);
        let s = lazy_sk_from_u128(LAZY_SK);
        let alice_matrix = dbg_gen_alice_matrix(s, &r0, &r1);

        for y in ys.iter() {
            let val1 = oprf(&alice_matrix, y);
            let val1_u128 = u128::from_le_bytes(val1.try_into().unwrap());
            let val2 = oprf(&r1, y);
            let val2_u128 = u128::from_le_bytes(val2.try_into().unwrap());
            assert_eq!(val1_u128, val2_u128);
        }
    }

    #[test]
    fn test_oprf_false_positive() {
        use super::*;
        use crate::psi::opprf::LAZY_SK;
        use crate::utils::gen_unique_random_unsorted;
        use crate::utils::lazy_sk_from_u128;

        let ys = gen_unique_random_unsorted(10000);
        let r0 = Matrix::gen_r0(ys.len(), LAMBDA);

        let r1 = r0.gen_r1(&ys);
        let s = lazy_sk_from_u128(LAZY_SK);
        let alice_matrix = dbg_gen_alice_matrix(s, &r0, &r1);

        let mut rng = thread_rng();
        for _ in 0..10000 {
            let idx1: usize = rng.gen_range(0..10000);
            let idx2: usize = rng.gen_range(0..10000);
            if idx1 == idx2 {
                continue;
            }
            let val1 = oprf(&alice_matrix, &ys[idx1]);
            let val2 = oprf(&r1, &ys[idx2]);
            assert_ne!(val1, val2);
        }
    }

    #[test]
    fn test_hash() {
        use crypto_hash::hex_digest;
        use crypto_hash::Algorithm;
        let data = b"crypto-hash";
        let res = hex_digest(Algorithm::SHA256, data);
        println!("{}", res.as_bytes().len());
    }

    #[test]
    fn test_xor() {
        let a = 50_u128;
        let b = 25_u128;
        let c = a ^ b;
        assert_eq!(c, 43);
    }


    #[test]
    fn test_kmprt() {
        // use rand::Rng;
        use scuttlebutt::{AesRng, Channel};
        use ocelot::oprf::{KmprtReceiver, KmprtSender};
        use scuttlebutt::Block;
        use scuttlebutt::Block512;
        use std::os::unix::net::UnixStream;
        use std::io::BufReader;
        use std::io::BufWriter;

        
        let n = 100;
        
        let mut points = vec![];
        for i in 0..n {
            let a: Block = Block::from(i as u128);
            let b: Block512 = Block512::from([i as u8; 64]);
            points.push((a, b));
        }

        // let mut rng = AesRng::new();
        // let points = (0..n).map(|_| (rng.gen::<Block>(), rng.gen())).collect::<Vec<(Block, Block512)>>();

        let xs = points.iter().map(|(x, _)| *x).collect::<Vec<Block>>();
        let ys = points.iter().map(|(_, y)| *y).collect::<Vec<Block512>>();

        let (sen, rec) = UnixStream::pair().unwrap();
        let points_ = points.clone();
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::new();
            let reader = BufReader::new(sen.try_clone().unwrap());
            let writer = BufWriter::new(sen);
            let mut channel = Channel::new(reader, writer);
            let mut oprf = KmprtSender::init(&mut channel, &mut rng).unwrap();
            let _ = oprf.send(&mut channel, &points_, n, &mut rng).unwrap();
        });
        let mut rng = AesRng::new();
        let reader = BufReader::new(rec.try_clone().unwrap());
        let writer = BufWriter::new(rec);
        let mut channel = Channel::new(reader, writer);
        let mut oprf = KmprtReceiver::init(&mut channel, &mut rng).unwrap();
        let outputs = oprf.receive(&mut channel, &xs, &mut rng).unwrap();
        handle.join().unwrap();
        let mut ok = true;
        for j in 0..n {
            if ys[j] != outputs[j] {
                ok = false
            }
        }
        assert!(ok);

    }


    // we cannot use kkrt because it does not pre-define k, instead, it generate random y for each x and then compute k such that F(k, x)=y (k for each x is different)
    // what we need: pre-define k, then compute y = F(k, x) (k for each x is the same)
    #[test]
    fn test_kkrt() {
        use std::os::unix::net::UnixStream;
        use scuttlebutt::AesRng;
        use std::io::BufReader;
        use std::io::BufWriter;
        use scuttlebutt::Channel;
        use ocelot::oprf;
        use scuttlebutt::{Block, Block512};
        use ocelot::oprf::Sender;
        use ocelot::oprf::Receiver;

        let n = 100;
        let selections: Vec<Block> = (0..n).map(|_| rand::random::<Block>()).collect();  // input
        let selections_ = selections.clone();

        let (sender, receiver) = UnixStream::pair().unwrap();
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::new();
            let reader = BufReader::new(sender.try_clone().unwrap());
            let writer = BufWriter::new(sender);
            let mut channel = Channel::new(reader, writer);
            let mut oprf = <oprf::KkrtSender as oprf::Sender>::init(&mut channel, &mut rng).unwrap();
            let seeds = oprf.send(&mut channel, n, &mut rng).unwrap();
            // just for check
            let results: Vec<Block512> = selections_
                .iter()
                .zip(seeds.into_iter())
                .map(|(inp, seed)| oprf.compute(seed, *inp))
                .collect::<Vec<Block512>>();
            results
        });
        let mut rng = AesRng::new();
        let reader = BufReader::new(receiver.try_clone().unwrap());
        let writer = BufWriter::new(receiver);
        let mut channel = Channel::new(reader, writer);
        let mut oprf = oprf::KkrtReceiver::init(&mut channel, &mut rng).unwrap();
        let outputs = oprf.receive(&mut channel, &selections, &mut rng).unwrap();
        let results = handle.join().unwrap();
        for j in 0..n {
            assert_eq!(results[j], outputs[j]);
        }

    }
}
