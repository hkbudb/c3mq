pub mod garbled_circuit;
pub mod graph;
pub mod oep;
pub mod ot;
pub mod psi;
pub mod relation;
pub mod tpch;
pub mod traits;
pub mod utils;

type ValType = u64;

pub const DATA_PATH: &str = "./data";
pub const SEED: u64 = 1413265736543;
pub const SEED2: u64 = 18446744073709;
pub const BASE_PORT: u16 = 8200;
pub const PARALLEL_BASE_PORT: u16 = 8500;
pub const OK: u8 = 1;
pub const ERR: u8 = 0;
pub const N: u16 = 20;
pub const CONSENSUS_INFO_LEN: usize = 150;
pub const THREAD_NUM: usize = 4;
// simulate LAN bandwidth = 1000 Mbps, WAN bandwidth = 100 Mbps
pub const LAN_BANDWIDTH_MBPS: u64 = 1000;
pub const WAN_BANDWIDTH_MBPS: u64 = 100;
// simulate LAN RTT = 2 ms, WAN RTT = 20 ms
pub const LAN_RTT_MS: u64 = 2;
pub const WAN_RTT_MS: u64 = 20;


use lazy_static::lazy_static;
use std::sync::Mutex;

lazy_static! {
    pub static ref INTRA_SHARD_COMM: Mutex<u64> = Mutex::new(0);
}

lazy_static! {
    pub static ref CROSS_SHARD_COMM: Mutex<u64> = Mutex::new(0);
}

lazy_static! {
    pub static ref CONSENSUS_NUM: Mutex<u64> = Mutex::new(0);
}

pub fn add_intra_shard(bytes_num: u64) {
    let mut comm = INTRA_SHARD_COMM.lock().unwrap();
    * comm += bytes_num;
}

pub fn add_cross_shard(bytes_num: u64) {
    let mut comm = CROSS_SHARD_COMM.lock().unwrap();
    * comm += bytes_num;
}

pub fn increase_consensus() {
    let mut comm = CONSENSUS_NUM.lock().unwrap();
    * comm += 1;
}

