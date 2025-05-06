use once_cell::sync::Lazy;
use std::{collections::HashMap, io::{self, Read, Write}, net::TcpStream, os::unix::net::UnixStream};

use ark_bls12_381::Bls12_381;
use ark_ec::pairing::Pairing;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

use crate::N;

pub mod q3;
pub mod q4;
pub mod q8;
pub mod q10;
pub mod q14;
pub mod q18;
pub mod utils;

pub const PRE_INFO: &str = "pre_compute_info.json";
pub const PRE_INFO_PARTITION: &str = "pre_compute_info_partition.json";
pub const SIGNAL: usize = 19;
pub const OK_SIGNAL: usize = 25;

pub static MACHINE_ADDRS: Lazy<HashMap<&'static str, &'static str>> = Lazy::new(|| {
    let mut map = HashMap::new();
    map.insert("csr64", "158.182.9.54");
    map.insert("csr65", "158.182.9.55");
    map.insert("csr68", "158.182.9.58");
    map.insert("csr69", "158.182.9.59");
    map.insert("csr35", "158.182.9.65");
    map.insert("csr34", "158.182.9.64");
    map.insert("csr36", "158.182.9.66");
    map.insert("csr37", "158.182.9.67");
    map.insert("csr38", "158.182.9.68");
    map.insert("csr39", "158.182.9.69");

    map
});

#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub(crate) struct PreInfo {
    pub xs_info: Vec<<Bls12_381 as Pairing>::G1Affine>,
    pub veri_info: Vec<<Bls12_381 as Pairing>::G1Affine>,
    pub z_commit: ark_ec::short_weierstrass::Affine<ark_bls12_381::g2::Config>,
}


pub trait Stream: Read + Write + Send + Sync{
    type Cloned: Stream;
    // fn try_clone(&self) -> io::Result<Box<dyn Stream>>;
    fn try_clone(&self) -> io::Result<Self::Cloned>;
}

impl Stream for TcpStream {
    type Cloned = TcpStream;
    // fn try_clone(&self) -> io::Result<Box<dyn Stream>> {
    //     TcpStream::try_clone(self).map(|s| Box::new(s) as Box<dyn Stream>)
    // }
    fn try_clone(&self) -> io::Result<Self::Cloned> {
        TcpStream::try_clone(self)
    }
}

impl Stream for UnixStream {
    type Cloned = UnixStream;
    // fn try_clone(&self) -> io::Result<Box<dyn Stream>> {
    //     UnixStream::try_clone(self).map(|s| Box::new(s) as Box<dyn Stream>)
    // }
    fn try_clone(&self) -> io::Result<Self::Cloned> {
        UnixStream::try_clone(self)
    }
}


pub(crate) fn show_comm_cost(intra_comm: u64, cross_comm: u64, consen_num: u64) {
    let consensus_bytes = consen_num * 150 * N as u64 * N as u64;
    let intra_bytes = intra_comm + consensus_bytes;
    let intra_mb = intra_bytes / 1048576;
    println!("====== intra_comm: {} MB", intra_mb);
    let cross_mb = cross_comm / 1048576;
    println!("====== cross_comm: {} MB", cross_mb);
}