use std::{fs::File, io::{BufRead, BufReader}, path::Path};

use crate::relation::Relation;



pub mod q1;
pub mod q2;

const BTC_DATA_PATH: &str = "./data/btc";
const P2P_DATA_PATH: &str = "./data/p2p";
const WIKI_DATA_PATH: &str = "./data/wiki";
const GRQC_DATA_PATH: &str = "./data/grqc";


fn load_btc_data() -> (Relation, Vec<u32>) {
    let path = Path::new(BTC_DATA_PATH).join("btc.csv");
    let file = File::open(&path).unwrap();

    let reader = BufReader::new(file);
    let lines = reader.lines();
    let mut from = vec![];
    let mut to = vec![];
    for line in lines {
        let line = line.unwrap();
        let fields: Vec<&str> = line.split(',').collect();
        from.push(fields[0].parse::<u32>().unwrap());
        to.push(fields[1].parse::<u32>().unwrap());
    }
    let len = from.len();
    let anno = vec![1; len];

    let table = Relation::new(vec![from, to]);

    (table, anno)
}

fn load_other_data(which_dataset: u8) -> (Relation, Vec<u32>) {
    let path = match which_dataset {
        0 => { Path::new(GRQC_DATA_PATH).join("GrQc.txt") }
        2 => { Path::new(P2P_DATA_PATH).join("p2p-Gnutella24.txt") }
        3 => { Path::new(WIKI_DATA_PATH).join("Wiki-Vote.txt") }
        _ => { panic!("invalid path") }
    };

    let file = File::open(&path).unwrap();
    let reader = BufReader::new(file);

    let mut from = vec![];
    let mut to = vec![];
    for line in reader.lines() {
        let line = line.unwrap();
        let fields: Vec<&str> = line.split_whitespace().collect();
        from.push(fields[0].parse::<u32>().unwrap());
        to.push(fields[1].parse::<u32>().unwrap());
    }

    let len = from.len();
    let anno = vec![1; len];

    let table = Relation::new(vec![from, to]);

    (table, anno)
}

pub(crate) fn load_data(which_dataset: u8) -> (Relation, Vec<u32>) {
    match which_dataset {
        1 => {
            return load_btc_data();
        },
        i => {
            return load_other_data(i);
        }
    }
}