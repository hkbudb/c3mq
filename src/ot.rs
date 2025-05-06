use std::io::{BufReader, BufWriter};

use ocelot::ot::{Receiver, Sender};
use rand::SeedableRng;
use scuttlebutt::{AesRng, Block, Channel};

use crate::{tpch::Stream, SEED};

pub fn ot_sender<OTSender: Sender<Msg = Block>, S: Stream>(
    msg0: Vec<Block>,
    msg1: Vec<Block>,
    sender: &mut S,
) {
    let mut rng = AesRng::from_seed((SEED as u128).into());
    let reader = BufReader::new(sender.try_clone().unwrap());
    let writer = BufWriter::new(sender);
    let mut channel = Channel::new(reader, writer);
    let mut ot = OTSender::init(&mut channel, &mut rng).unwrap();
    let ms = msg0
        .into_iter()
        .zip(msg1.into_iter())
        .collect::<Vec<(Block, Block)>>();
    ot.send(&mut channel, &ms, &mut rng).unwrap();
}

pub fn ot_receiver<OTReceiver: Receiver<Msg = Block>, S: Stream>(
    selections: &Vec<bool>,
    receiver: &mut S,
) -> Vec<Block> {
    let mut rng = AesRng::from_seed((SEED as u128).into());
    let reader = BufReader::new(receiver.try_clone().unwrap());
    let writer = BufWriter::new(receiver);
    let mut channel = Channel::new(reader, writer);
    let mut ot = OTReceiver::init(&mut channel, &mut rng).unwrap();
    let res = ot.receive(&mut channel, selections, &mut rng).unwrap();

    res
}
