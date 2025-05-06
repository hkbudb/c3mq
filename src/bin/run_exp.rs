use std::{
    fs::{self, create_dir_all},
    path::Path,
    time::Duration,
};

use ark_bls12_381::Fr;
use ark_std::UniformRand;

use rayon::ThreadPoolBuilder;
use c3mq::{graph::{q1::{exe_graph_q1_batch, exe_graph_q1_single}, q2::{exe_graph_q2_batch, exe_graph_q2_single}}, N, THREAD_NUM};
#[allow(unused_imports)]
use c3mq::{
    tpch::{
        q10::{exe_q10_batch, exe_q10_single},
        q14::{exe_q14_batch, exe_q14_single},
        q18::{exe_q18_batch, exe_q18_single},
        q3::{
            exe_q3_batch, exe_q3_single,
        },
        q4::{exe_q4_batch, exe_q4_single},
        q8::{exe_q8_batch, exe_q8_single},
    },
    utils::{gen_data, get_fixed_rng, read_data},
    DATA_PATH,
};

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() != 2 {
        panic!("incorrect num of input");
    }

    let input = &args[1];
    let self_id = match input.parse::<u16>() {
        Ok(num) => num,
        Err(_) => panic!("Invalid input. Please input a valid usize."),
    };

    // let path = Path::new(&args[2]);

    let path = Path::new("./data/1MB");
    let debug = true;
    let chunk_size = 80;
    let query_num = N as usize;

    let which_dataset = 0;

    
    //====================================
    exe_q3_single(path, chunk_size, self_id, debug, false);
    println!("################################");
    // std::thread::sleep(Duration::from_secs(2));
    // exe_q3_single(path, chunk_size, self_id, debug, true);
    // println!("################################");
    // std::thread::sleep(Duration::from_secs(5));
    // exe_q3_batch(path, chunk_size, query_num, self_id, debug);
    // println!("################################");
    // std::thread::sleep(Duration::from_secs(5));

    // exe_q4_single(path, chunk_size, self_id, debug, false);
    // println!("################################");
    // std::thread::sleep(Duration::from_secs(5));
    // exe_q4_single(path, chunk_size, self_id, debug, true);
    // println!("################################");
    // std::thread::sleep(Duration::from_secs(5));
    // exe_q4_batch(path, chunk_size, query_num, self_id, debug);
    // println!("################################");
    // std::thread::sleep(Duration::from_secs(5));

    // exe_q8_single(path, chunk_size, self_id, debug, false);
    // println!("################################");
    // std::thread::sleep(Duration::from_secs(2));
    // exe_q8_single(path, chunk_size, self_id, debug, true);
    // println!("################################");
    // std::thread::sleep(Duration::from_secs(5));
    // exe_q8_batch(path, chunk_size, query_num, self_id, debug);
    // println!("################################");
    // std::thread::sleep(Duration::from_secs(5));

    // exe_q10_single(path, chunk_size, self_id, debug, false);
    // println!("################################");
    // std::thread::sleep(Duration::from_secs(2));
    // exe_q10_single(path, chunk_size, self_id, debug, true);
    // println!("################################");
    // std::thread::sleep(Duration::from_secs(5));
    // exe_q10_batch(path, chunk_size, query_num, self_id, debug);
    // println!("################################");
    // std::thread::sleep(Duration::from_secs(5));

    // exe_q14_single(path, chunk_size, self_id, debug, false);
    // println!("################################");
    // std::thread::sleep(Duration::from_secs(5));
    // exe_q14_single(path, chunk_size, self_id, debug, true);
    // println!("################################");
    // std::thread::sleep(Duration::from_secs(5));
    // exe_q14_batch(path, chunk_size, query_num, self_id, debug);
    // println!("################################");
    // std::thread::sleep(Duration::from_secs(5));

    // exe_q18_single(path, chunk_size, self_id, debug, false);
    // println!("################################");
    // std::thread::sleep(Duration::from_secs(2));
    // exe_q18_single(path, chunk_size, self_id, debug, true);
    // println!("################################");
    // std::thread::sleep(Duration::from_secs(5));
    // exe_q18_batch(path, chunk_size, query_num, self_id, debug);
    // println!("################################");

    // exe_graph_q1_single(self_id, debug, false, which_dataset);
    // println!("################################");
    // exe_graph_q1_single(self_id, debug, true, which_dataset);
    // println!("################################");
    // exe_graph_q1_batch(self_id, debug, query_num, which_dataset);
    // println!("################################");

    // exe_graph_q2_single(self_id, debug, false, which_dataset);
    // println!("################################");
    // exe_graph_q2_single(self_id, debug, true, which_dataset);
    // println!("################################");
    // exe_graph_q2_batch(self_id, debug, query_num, which_dataset);
    // println!("################################");
}



#[allow(dead_code)]
fn gen_source_data() {
    let n = 1000; // data set size
    let path = Path::new(DATA_PATH).join(format!("{}", n));
    if path.exists() {
        fs::remove_dir_all(&path).unwrap();
    }
    create_dir_all(&path).unwrap();
    let x_path = path.join("xs.json");

    gen_data(n, &x_path);

    let y_path = path.join("ys.json");

    gen_data(n, &y_path);
}

#[allow(dead_code)]
fn check_correctness() {
    let n = 1000;
    let path = Path::new(DATA_PATH).join(format!("{}", n));
    let y_path = path.join("ys.json");
    let x_path = path.join("xs.json");
    let ys = read_data(&y_path);
    let xs = read_data(&x_path);

    let mut res = vec![];
    for y in ys {
        if xs.contains(&y) {
            res.push(1);
        } else {
            res.push(0);
        }
    }

    println!("{:?}", res);
}
