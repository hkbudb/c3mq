use core::panic;
use std::{
    fs::{self, File},
    io::{self, Read, Write},
    os::unix::net::{UnixListener, UnixStream},
    path::Path, thread, time::Duration,
};

use rand::Rng;
use rayon::iter::{IndexedParallelIterator, IntoParallelRefIterator, ParallelIterator};
use serde::{Deserialize, Serialize};

use crate::{tpch::Stream, LAN_BANDWIDTH_MBPS, LAN_RTT_MS, WAN_BANDWIDTH_MBPS, WAN_RTT_MS};

use super::YES_FLAG;

pub fn server_net_setup() -> UnixStream {
    let socket_path = Path::new("/tmp/hxwang/my_socket.sock");
    let _ = fs::remove_file(&socket_path);
    let listener = UnixListener::bind(&socket_path).unwrap();
    let (stream, _) = listener
        .accept()
        .expect("failed to accept client connection");
    println!("Connection established");
    stream
}

pub fn cli_net_setup() -> UnixStream {
    let socket_path = Path::new("/tmp/hxwang/my_socket.sock");

    loop {
        match UnixStream::connect(socket_path) {
            Ok(stream) => {
                println!("Connection established");
                return stream;
            }
            Err(_) => continue,
        }
    }
}

pub fn send_data_by_stream<T: Read + Write>(stream: &mut T, data: &Vec<u8>, is_lan: bool) {

    let len = data.len();
    let simulate_latency = if is_lan {
        compute_lan_time(len)
    } else {
        compute_wan_time(len)
    };
    thread::sleep(Duration::from_millis(simulate_latency));
    
    if is_lan {
        crate::add_intra_shard(len as u64);
    } else {
        crate::add_cross_shard(len as u64);
    }
    
    stream
        .write(&len.to_le_bytes())
        .expect("failed to send len");
    let mut buf = [0; 1024];
    stream.read(&mut buf).expect("failed to read signal");
    let flag = bincode::deserialize::<u8>(&buf).unwrap();
    if flag == YES_FLAG {
        stream.write(data).expect("Failed to send data");
    } else {
        panic!("invalid signal for data sending");
    }
}

fn compute_lan_time(len: usize) -> u64 {
    let bytes_per_ms = 1000 * LAN_BANDWIDTH_MBPS / 8;
    let transmit_time_ms = len as u64 / bytes_per_ms;
    let total_time_ms = transmit_time_ms + LAN_RTT_MS;
    return total_time_ms
}

fn compute_wan_time(len: usize) -> u64 {
    let bytes_per_ms = 1000 * WAN_BANDWIDTH_MBPS / 8;
    let transmit_time_ms = len as u64 / bytes_per_ms;
    let total_time_ms = transmit_time_ms + WAN_RTT_MS;
    return total_time_ms
}

pub fn receive_data_by_stream<T: Read + Write>(stream: &mut T) -> Vec<u8> {
    // read data size
    let mut buf = [0u8; 1024];
    stream.read(&mut buf).expect("failed to read data len");
    let size = bincode::deserialize::<u32>(&buf).expect("failed to deserialize data size");

    // write response
    stream
        .write(&YES_FLAG.to_le_bytes())
        .expect("failed to write signal");

    let mut data = vec![0u8; size as usize];
    stream.read_exact(&mut data).expect("failed to read data");

    data
}

const RAND_BOUND: u128 = 10000;
const FIXED_LEN: usize = 10000;
pub const BEAVER_TRIPLES: &str = "./data/beaver_triples.json";

// Beaver triple c1 + c2 = (a1 + a2) * (b1 + b2)
// For security, this should be done by MPC (OT-based solution), here we just use plaintext because it can be done offline
// tricks: to avoid overflow, use small numbers
pub fn gen_beaver_triples(
    n: usize,
) -> (
    Vec<u128>,
    Vec<u128>,
    Vec<u128>,
    Vec<u128>,
    Vec<u128>,
    Vec<u128>,
) {
    let mut rng = rand::thread_rng();
    let a1: Vec<u128> = (0..n).map(|_| rng.gen_range(1..RAND_BOUND)).collect();
    let a2: Vec<u128> = (0..n).map(|_| rng.gen_range(1..RAND_BOUND)).collect();
    let b1: Vec<u128> = (0..n).map(|_| rng.gen_range(1..RAND_BOUND)).collect();
    let b2: Vec<u128> = (0..n).map(|_| rng.gen_range(1..RAND_BOUND)).collect();
    let c1: Vec<u128> = (0..n).map(|_| rng.gen_range(1..RAND_BOUND)).collect();

    let c2: Vec<u128> = (0..n)
        .map(|i| {
            (a1[i].wrapping_add(a2[i]))
                .wrapping_mul(b1[i].wrapping_add(b2[i]))
                .wrapping_sub(c1[i])
        })
        .collect();

    (a1, a2, b1, b2, c1, c2)
}

#[derive(Clone, Serialize, Deserialize)]
pub struct BeaverTriples {
    a1: Vec<u128>,
    a2: Vec<u128>,
    b1: Vec<u128>,
    b2: Vec<u128>,
    c1: Vec<u128>,
    c2: Vec<u128>,
}

pub fn write_beaver_triples() {
    let (a1, a2, b1, b2, c1, c2) = gen_beaver_triples(FIXED_LEN);
    let beaver_triples = BeaverTriples {
        a1,
        a2,
        b1,
        b2,
        c1,
        c2,
    };
    let bytes = bincode::serialize(&beaver_triples).unwrap();

    let file_path = Path::new(BEAVER_TRIPLES);
    if std::fs::metadata(file_path).is_ok() {
        std::fs::remove_file(&file_path).unwrap();
    }

    let mut file = File::create(&file_path).unwrap();
    file.write_all(&bytes).unwrap();
}

pub fn load_beaver_truples() -> BeaverTriples {
    let file_path = Path::new(BEAVER_TRIPLES);
    let mut file = File::open(file_path).unwrap();
    let mut buffer: Vec<u8> = Vec::new();
    io::Read::read_to_end(&mut file, &mut buffer).unwrap();
    let beaver_triples: BeaverTriples = bincode::deserialize(&buffer).unwrap();
    beaver_triples
}

pub fn obtain_beaver_tripes_by(
    n: usize,
    beaver_triples: BeaverTriples,
) -> (
    Vec<u128>,
    Vec<u128>,
    Vec<u128>,
    Vec<u128>,
    Vec<u128>,
    Vec<u128>,
) {
    let len = beaver_triples.a1.len();
    let a1 = beaver_triples.a1;
    let a2 = beaver_triples.a2;
    let b1 = beaver_triples.b1;
    let b2 = beaver_triples.b2;
    let c1 = beaver_triples.c1;
    let c2 = beaver_triples.c2;

    if n <= len {
        let a1 = a1.into_iter().take(n).collect();
        let a2 = a2.into_iter().take(n).collect();
        let b1 = b1.into_iter().take(n).collect();
        let b2 = b2.into_iter().take(n).collect();
        let c1 = c1.into_iter().take(n).collect();
        let c2 = c2.into_iter().take(n).collect();
        return (a1, a2, b1, b2, c1, c2);
    } else {
        let copy_cnt = n / len;
        let remaining_ele = n % len;
        let mut new_a1 = Vec::with_capacity(n);
        for _ in 0..copy_cnt {
            new_a1.extend_from_slice(&a1);
        }
        let extra_ele = &a1[0..remaining_ele];
        new_a1.extend_from_slice(extra_ele);

        let mut new_a2 = Vec::with_capacity(n);
        for _ in 0..copy_cnt {
            new_a2.extend_from_slice(&a2);
        }
        let extra_ele = &a2[0..remaining_ele];
        new_a2.extend_from_slice(extra_ele);

        let mut new_b1 = Vec::with_capacity(n);
        for _ in 0..copy_cnt {
            new_b1.extend_from_slice(&b1);
        }
        let extra_ele = &b1[0..remaining_ele];
        new_b1.extend_from_slice(extra_ele);

        let mut new_b2 = Vec::with_capacity(n);
        for _ in 0..copy_cnt {
            new_b2.extend_from_slice(&b2);
        }
        let extra_ele = &b2[0..remaining_ele];
        new_b2.extend_from_slice(extra_ele);

        let mut new_c1 = Vec::with_capacity(n);
        for _ in 0..copy_cnt {
            new_c1.extend_from_slice(&c1);
        }
        let extra_ele = &c1[0..remaining_ele];
        new_c1.extend_from_slice(extra_ele);

        let mut new_c2 = Vec::with_capacity(n);
        for _ in 0..copy_cnt {
            new_c2.extend_from_slice(&c2);
        }
        let extra_ele = &c2[0..remaining_ele];
        new_c2.extend_from_slice(extra_ele);

        return (new_a1, new_a2, new_b1, new_b2, new_c1, new_c2);
    }
}

// z_i = -(i-1) * e * f + f * x_i + e * y_i + c_i, where i \in {1, 2}
pub fn vec_mul_1<S: Stream>(
    x1: &Vec<u128>,
    y1: &Vec<u128>,
    a1: &Vec<u128>,
    b1: &Vec<u128>,
    c1: &Vec<u128>,
    stream: &mut S,
) -> Vec<u128> {
    let e1: Vec<u128> = x1
        .par_iter()
        .zip(a1.par_iter())
        .map(|(x, a)| x.wrapping_sub(*a))
        .collect();
    let f1: Vec<u128> = y1
        .par_iter()
        .zip(b1.par_iter())
        .map(|(y, b)| y.wrapping_sub(*b))
        .collect();
    // println!("1: e1: {:?}, f1: {:?}", e1, f1);
    let data = (e1, f1);
    let bytes = bincode::serialize(&data).unwrap();
    send_data_by_stream(stream, &bytes, false);
    let received_bytes = receive_data_by_stream(stream);
    let (e2, f2): (Vec<u128>, Vec<u128>) = bincode::deserialize(&received_bytes).unwrap();
    let e: Vec<u128> = data
        .0
        .par_iter()
        .zip(e2.par_iter())
        .map(|(x, y)| x.wrapping_add(*y))
        .collect();
    let f: Vec<u128> = data
        .1
        .par_iter()
        .zip(f2.par_iter())
        .map(|(x, y)| x.wrapping_add(*y))
        .collect();

    // z_1 = f * x_1 + e * y_1 + c_1
    let f_mul_x1: Vec<u128> = f
        .par_iter()
        .zip(x1.par_iter())
        .map(|(x, y)| x.wrapping_mul(*y))
        .collect();
    let e_mul_y1: Vec<u128> = e
        .par_iter()
        .zip(y1.par_iter())
        .map(|(x, y)| x.wrapping_mul(*y))
        .collect();

    let res: Vec<u128> = c1
        .par_iter()
        .zip(f_mul_x1.par_iter())
        .zip(e_mul_y1.par_iter())
        .map(|((a, b), c)| a.wrapping_add(*b).wrapping_add(*c))
        .collect();

    res
}

// z_i = -(i-1) * e * f + f * x_i + e * y_i + c_i, where i \in {1, 2}
pub fn vec_mul_2<S: Stream>(
    x2: &Vec<u128>,
    y2: &Vec<u128>,
    a2: &Vec<u128>,
    b2: &Vec<u128>,
    c2: &Vec<u128>,
    stream: &mut S,
) -> Vec<u128> {
    let e2: Vec<u128> = x2
        .par_iter()
        .zip(a2.par_iter())
        .map(|(x, a)| x.wrapping_sub(*a))
        .collect();
    let f2: Vec<u128> = y2
        .par_iter()
        .zip(b2.par_iter())
        .map(|(y, b)| y.wrapping_sub(*b))
        .collect();
    let data = (e2, f2);
    let received_bytes = receive_data_by_stream(stream);
    let (e1, f1): (Vec<u128>, Vec<u128>) = bincode::deserialize(&received_bytes).unwrap();
    let bytes = bincode::serialize(&data).unwrap();
    send_data_by_stream(stream, &bytes, false);

    let e: Vec<u128> = data
        .0
        .par_iter()
        .zip(e1.par_iter())
        .map(|(x, y)| x.wrapping_add(*y))
        .collect();
    let f: Vec<u128> = data
        .1
        .par_iter()
        .zip(f1.par_iter())
        .map(|(x, y)| x.wrapping_add(*y))
        .collect();

    // z_2 = -e*f + f*x_2 + e*y_2 + c_2
    let f_mul_x2: Vec<u128> = f
        .par_iter()
        .zip(x2.par_iter())
        .map(|(x, y)| x.wrapping_mul(*y))
        .collect();
    let e_mul_y2: Vec<u128> = e
        .par_iter()
        .zip(y2.par_iter())
        .map(|(x, y)| x.wrapping_mul(*y))
        .collect();
    let e_mul_f: Vec<u128> = e
        .par_iter()
        .zip(f.par_iter())
        .map(|(x, y)| x.wrapping_mul(*y))
        .collect();

    let res: Vec<u128> = c2
        .par_iter()
        .zip(f_mul_x2.par_iter())
        .zip(e_mul_y2.par_iter())
        .zip(e_mul_f.par_iter())
        .map(|(((a, b), c), d)| a.wrapping_add(*b).wrapping_add(*c).wrapping_sub(*d))
        .collect();

    res
}

mod test {

    #[allow(dead_code)]
    fn check_beaver_triples(
        a1: Vec<u128>,
        a2: Vec<u128>,
        b1: Vec<u128>,
        b2: Vec<u128>,
        c1: Vec<u128>,
        c2: Vec<u128>,
    ) {
        // check Beaver triple gen
        let a: Vec<u128> = a1
            .iter()
            .zip(a2.iter())
            .map(|(a, b)| a.wrapping_add(*b))
            .collect();
        let b: Vec<u128> = b1
            .iter()
            .zip(b2.iter())
            .map(|(a, b)| a.wrapping_add(*b))
            .collect();
        let c: Vec<u128> = c1
            .iter()
            .zip(c2.iter())
            .map(|(a, b)| a.wrapping_add(*b))
            .collect();
        let ab: Vec<u128> = a
            .iter()
            .zip(b.iter())
            .map(|(a, b)| a.wrapping_mul(*b))
            .collect();
        assert_eq!(ab, c);
    }
    // Beaver triple for additive secret sharing
    #[test]
    fn test_vec_mul() {
        use super::*;
        use crate::utils::gen_unique_random_unsorted;
        use crate::utils::obtain_tcp_stream;
        use std::sync::mpsc;

        let n = 100;
        let x1 = gen_unique_random_unsorted::<u128>(n);
        let x2 = gen_unique_random_unsorted::<u128>(n);

        let y1 = gen_unique_random_unsorted::<u128>(n);
        let y2 = gen_unique_random_unsorted::<u128>(n);

        let x: Vec<u128> = x1
            .iter()
            .zip(x2.iter())
            .map(|(a, b)| a.wrapping_add(*b))
            .collect();
        let y: Vec<u128> = y1
            .iter()
            .zip(y2.iter())
            .map(|(a, b)| a.wrapping_add(*b))
            .collect();
        let exp_res: Vec<u128> = x
            .iter()
            .zip(y.iter())
            .map(|(a, b)| a.wrapping_mul(*b))
            .collect();

        let (a1, a2, b1, b2, c1, c2) = gen_beaver_triples(n);
        // println!("a1: {:?}, a2: {:?}, b1: {:?}, b2: {:?}, c1: {:?}, c2: {:?}", a1, a2, b1, b2, c1, c2);

        let (mut sender, mut receiver) = obtain_tcp_stream();
        let (tx_1, rx_1) = mpsc::channel();
        let (tx_2, rx_2) = mpsc::channel();

        let thread_1 = std::thread::spawn(move || {
            let z1 = vec_mul_1(&x1, &y1, &a1, &b1, &c1, &mut sender);
            tx_1.send(z1).unwrap();
        });
        let thread_2 = std::thread::spawn(move || {
            let z2 = vec_mul_2(&x2, &y2, &a2, &b2, &c2, &mut receiver);
            tx_2.send(z2).unwrap();
        });

        thread_1.join().unwrap();
        thread_2.join().unwrap();
        let z1 = rx_1.recv().unwrap();
        let z2 = rx_2.recv().unwrap();
        let z: Vec<u128> = z1
            .iter()
            .zip(z2.iter())
            .map(|(a, b)| a.wrapping_add(*b))
            .collect();

        assert_eq!(z, exp_res);
    }

    #[test]
    fn test_beaver_triples_read_write() {
        use super::*;
        write_beaver_triples();
        let triples = load_beaver_truples();
        let (a1, a2, b1, b2, c1, c2) = obtain_beaver_tripes_by(15600, triples);
        check_beaver_triples(a1, a2, b1, b2, c1, c2);
    }
}
