use std::{
    fs::File, io::{self, BufRead, Write}, os::unix::net::UnixStream, path::Path
};

use ark_bls12_381::{Bls12_381, Fr};
use ark_ec::pairing::Pairing;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use crypto_hash::{digest, Algorithm};
use rayon::ThreadPoolBuilder;

use crate::{
    psi::{
        setup_kzg,
        subproduct_tree::SubProductTree,
        utils::{
            load_beaver_truples, obtain_beaver_tripes_by, receive_data_by_stream,
            send_data_by_stream, vec_mul_1, vec_mul_2,
        },
        *,
    },
    relation::Relation,
    tpch::{utils::gen_shared_anno, PRE_INFO},
    utils::{get_fixed_rng, obtain_unix_streams, points_from_num, run_consensus},
    N, THREAD_NUM,
};

use super::PreInfo;

// e.g., path: ./data/1MB
pub fn load_q14_tables(
    path: &Path,
    chunk_size: usize,
) -> ((Relation, Vec<u32>), (Relation, Vec<u32>, Vec<u32>)) {
    let lineitem_path = path.join("lineitem.tbl");
    let part_path = path.join("part.tbl");

    // lineitem
    let f_lineitem = File::open(&lineitem_path).unwrap();
    let reader = io::BufReader::new(f_lineitem);
    let lines = reader.lines().skip(2);

    let mut l_partkey = vec![];
    let mut l_anno = vec![];

    let (lower_bound, upper_bound) = (19950901, 19951001);

    for line in lines {
        let line = line.unwrap();
        let fields: Vec<&str> = line.split('|').collect();
        l_partkey.push(fields[1].parse::<u32>().unwrap());
        let l_extendedprice = fields[5].parse::<f32>().unwrap();
        let l_discount = fields[6].parse::<f32>().unwrap();
        let non_zero_anno = (l_extendedprice * (1. - l_discount)) as u32;
        let date_info: Vec<&str> = fields[10].split('-').collect();
        let date_num = date_info[0].parse::<u32>().unwrap() * 10000
            + date_info[1].parse::<u32>().unwrap() * 100
            + date_info[2].parse::<u32>().unwrap();
        if date_num > lower_bound && date_num < upper_bound {
            l_anno.push(non_zero_anno);
        } else {
            l_anno.push(0);
        }
    }
    let lineitem = Relation::new(vec![l_partkey]);
    // println!("{:?}", lineitem);
    // println!("{:?}", l_anno);

    // part
    let f_part = File::open(&part_path).unwrap();
    let reader = io::BufReader::new(f_part);
    let lines = reader.lines().skip(2);

    let mut p_partkey = vec![];
    let mut p_anno1 = vec![];
    let mut p_anno2 = vec![];

    for line in lines {
        let line = line.unwrap();
        let fields: Vec<&str> = line.split('|').collect();
        p_partkey.push(fields[0].parse::<u32>().unwrap());
        let p_type = fields[4];
        if p_type.starts_with("PROMO") {
            p_anno1.push(1);
        } else {
            p_anno1.push(0);
        }
        p_anno2.push(1);
    }
    let mut part = Relation::new(vec![p_partkey]);
    let pruned_size = part.get_size() % chunk_size;
    part.prune(pruned_size);
    p_anno1.truncate(p_anno1.len() - pruned_size);
    p_anno2.truncate(p_anno1.len() - pruned_size);

    // println!("{:?}", part);
    // println!("{:?}", p_anno1);
    // println!("{:?}", p_anno2);

    ((lineitem, l_anno), (part, p_anno1, p_anno2))
}

pub fn wirte_q14_pre_compute_info(
    path: &Path,
    secret: <Bls12_381 as Pairing>::ScalarField,
    chunk_size: usize,
) {
    let ((lineitem, l_anno), (part, _p_anno1, _p_anno2)) = load_q14_tables(path, chunk_size);

    let mut l_partkey = lineitem.get_col(0); // xs: has duplicate
    let p_partkey = part.get_col(0); // ys: unique

    let mut rng = get_fixed_rng();
    let _l_anno_sorted = Relation::local_add_agg(&mut l_partkey, &l_anno, &mut rng);
    let n_psi = l_partkey.len();
    let max_deg = n_psi - 1;
    let mut kzg = setup_kzg(max_deg);
    kzg.setup(secret);
    let xs_pts = points_from_num(l_partkey);
    let xs_info = kzg.pre_compute_g1(&xs_pts, secret);
    let ys_pts = points_from_num(p_partkey);
    let veri_info = kzg.pre_compute_g1(&ys_pts, secret);
    let z_commit = kzg.pre_compute_z_commitment(&ys_pts, secret);
    let pre_info = PreInfo {
        xs_info: xs_info,
        veri_info: veri_info,
        z_commit: z_commit,
    };

    let mut data_bytes: Vec<u8> = vec![];
    pre_info.serialize_uncompressed(&mut data_bytes).unwrap();

    println!("writing pre-computed info to files...");
    let dir_path = path.join("q14");
    if !std::fs::metadata(dir_path.clone()).is_ok() {
        std::fs::create_dir(dir_path.clone()).unwrap();
    }
    let file_path = dir_path.join(PRE_INFO);
    if std::fs::metadata(file_path.clone()).is_ok() {
        std::fs::remove_file(&file_path).unwrap();
    }
    let mut file = File::create(&file_path).unwrap();
    file.write_all(&data_bytes).unwrap();
}

pub(crate) fn read_q14_pre_compute_info(path: &Path) -> Vec<u8> {
    let file_path = path.join("q14").join(PRE_INFO);
    let mut file = File::open(file_path).unwrap();
    let mut buffer = Vec::new();
    io::Read::read_to_end(&mut file, &mut buffer).unwrap();
    buffer
}

pub fn exe_q14_batch(
    path: &Path,
    chunk_size: usize,
    query_num: usize,
    process_id: u16,
    debug: bool,
) {
    println!("loading dataset...");

    let ((lineitem, l_anno), (part, p_anno1, p_anno2)) = load_q14_tables(path, chunk_size);

    let mut l_partkey = lineitem.get_col(0);
    let p_partkey = part.get_col(0);

    let out_len = p_anno1.len();
    let ys_len_larger = p_anno1.len() > l_anno.len();

    let triples = load_beaver_truples();
    let (a1, a2, b1, b2, c1, c2) = obtain_beaver_tripes_by(out_len, triples);

    println!("loading pre-computed information...");
    let bytes = read_q14_pre_compute_info(path);
    let pre_info: PreInfo = PreInfo::deserialize_uncompressed(&*bytes).unwrap();
    let xs_info = pre_info.xs_info;
    let veri_info = pre_info.veri_info;
    let z_commit = pre_info.z_commit;

    // pre-compute sub_product trees
    println!("pre-computing some info...");
    let ys_pts = points_from_num(p_partkey.clone());
    let ys_tree = SubProductTree::new_from_points_parallel(&ys_pts);

    // setup
    println!("doing setup...");
    let (sen_streams, rec_streams) = obtain_unix_streams(THREAD_NUM);

    let mut rng = get_fixed_rng();
    let secret = Fr::rand(&mut rng);
    let n_psi = l_partkey.len();
    let max_deg = n_psi - 1;
    // thread_l
    let mut kzg_l = setup_kzg(max_deg);
    kzg_l.setup(secret);
    // thread_p
    let mut kzg_p = setup_kzg(max_deg);
    kzg_p.setup(secret);

    let timer = howlong::ProcessCPUTimer::new();
    let (mut stream_l_p, mut stream_p_l) = UnixStream::pair().unwrap();
    let (mut tx_o_l, mut rx_o_l) = UnixStream::pair().unwrap();
    let (mut tx_o_l2, mut rx_o_l2) =UnixStream::pair().unwrap();

    let thread_l = std::thread::spawn(move || {
        let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
        pool.install(|| {
        let self_id = process_id;
        let mut rng = get_fixed_rng();

        // lineitem local group by
        let (l_anno_sorted, _) = Relation::local_add_agg(&mut l_partkey, &l_anno, &mut rng);
        let xs_pts = points_from_num(l_partkey.clone());
        let xs_tree = SubProductTree::new_from_points_parallel(&xs_pts);

        let share1s = batch_psi_anno_sender_parallel(
            vec![l_partkey.into_iter().map(|x| x as u64).collect(); query_num],
            vec![l_anno_sorted.into_iter().map(|x| x as u64).collect(); query_num],
            &kzg_l,
            &mut stream_l_p,
            &vec![xs_info; query_num],
            &vec![xs_tree; query_num],
            debug,
            self_id,
            ys_len_larger,
            out_len,
            sen_streams,
        );

        // consensus on share1_first before sending to thread_c
        let bytes = bincode::serialize(&share1s).unwrap();
        let dig = digest(Algorithm::SHA256, &bytes);
        if !debug {
            run_consensus(dig, self_id);
        }
        let bytes1 = receive_data_by_stream(&mut rx_o_l);
        let bytes2 = receive_data_by_stream(&mut rx_o_l);
        let p_anno1_share1s: Vec<Vec<u128>> = bincode::deserialize(&bytes1).unwrap();
        let p_anno2_share1s: Vec<Vec<u128>> = bincode::deserialize(&bytes2).unwrap();

        let res1_share1s: Vec<Vec<u128>> = p_anno1_share1s
            .iter()
            .zip(share1s.iter())
            .map(|(p_anno1_share1, share1)| {
                vec_mul_1(&p_anno1_share1, &share1, &a1, &b1, &c1, &mut stream_l_p)
            })
            .collect();

        let res1_share1_sums: Vec<u128> = res1_share1s
            .into_iter()
            .map(|res1_share1| {
                res1_share1
                    .into_iter()
                    .fold(0_u128, |acc, x| acc.wrapping_add(x))
            })
            .collect();

        let res2_share1s: Vec<Vec<u128>> = p_anno2_share1s
            .iter()
            .zip(share1s.iter())
            .map(|(p_anno2_share1, share1)| {
                vec_mul_1(&p_anno2_share1, &share1, &a1, &b1, &c1, &mut stream_l_p)
            })
            .collect();

        let res2_share1_sums: Vec<u128> = res2_share1s
            .into_iter()
            .map(|res2_share1| {
                res2_share1
                    .into_iter()
                    .fold(0_u128, |acc, x| acc.wrapping_add(x))
            })
            .collect();

        let bytes = bincode::serialize(&(res1_share1_sums, res2_share1_sums)).unwrap();
        send_data_by_stream(&mut tx_o_l2, &bytes, false);
        });
    });

    let thread_p = std::thread::spawn(move || {
        let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
        pool.install(|| {
        let self_id = process_id + N * 1;

        let share2s = batch_psi_anno_receiver_parallel(
            &vec![p_partkey.clone(); query_num],
            false,
            vec![p_partkey.clone().into_iter().map(|x| x as u64).collect(); query_num],
            &kzg_p,
            &mut stream_p_l,
            &vec![ys_tree; query_num],
            &vec![veri_info; query_num],
            vec![z_commit; query_num],
            self_id,
            ys_len_larger,
            debug,
            rec_streams,
        );

        // consensus on share2_first before sending to thread_c
        let bytes = bincode::serialize(&share2s).unwrap();
        let dig = digest(Algorithm::SHA256, &bytes);
        if !debug {
            run_consensus(dig, self_id);
        }
        let (p_anno1_share1, p_anno1_share2) =
            gen_shared_anno(p_anno1.into_iter().map(|x| x as u128).collect());
        let (p_anno2_share1, p_anno2_share2) =
            gen_shared_anno(p_anno2.into_iter().map(|x| x as u128).collect());

        let p_anno1_share1s = vec![p_anno1_share1; query_num];
        let p_anno2_share1s = vec![p_anno2_share1; query_num];

        let p_anno1_share2s = vec![p_anno1_share2; query_num];
        let p_anno2_share2s = vec![p_anno2_share2; query_num];

        let bytes1 = bincode::serialize(&p_anno1_share1s).unwrap();
        let bytes2 = bincode::serialize(&p_anno2_share1s).unwrap();
        send_data_by_stream(&mut tx_o_l, &bytes1, false);
        send_data_by_stream(&mut tx_o_l, &bytes2, false);

        let res1_share2s: Vec<Vec<u128>> = share2s
            .iter()
            .zip(p_anno1_share2s.iter())
            .map(|(share2, p_anno1_share2)| {
                vec_mul_2(&p_anno1_share2, &share2, &a2, &b2, &c2, &mut stream_p_l)
            })
            .collect();
        let res1_share2_sums: Vec<u128> = res1_share2s
            .into_iter()
            .map(|res1_share2| {
                res1_share2
                    .into_iter()
                    .fold(0_u128, |acc, x| acc.wrapping_add(x))
            })
            .collect();

        let res2_share2s: Vec<Vec<u128>> = share2s
            .iter()
            .zip(p_anno2_share2s.iter())
            .map(|(share2, p_anno2_share2)| {
                vec_mul_2(&p_anno2_share2, &share2, &a2, &b2, &c2, &mut stream_p_l)
            })
            .collect();
        let res2_share2_sums: Vec<u128> = res2_share2s
            .into_iter()
            .map(|res2_share2| {
                res2_share2
                    .into_iter()
                    .fold(0_u128, |acc, x| acc.wrapping_add(x))
            })
            .collect();
        let bytes = receive_data_by_stream(&mut rx_o_l2);
        let (res1_share1_sums, res2_share1_sums): (Vec<u128>, Vec<u128>) =
            bincode::deserialize(&bytes).unwrap();
        let res1s: Vec<u128> = res1_share1_sums
            .iter()
            .zip(res1_share2_sums.iter())
            .map(|(res1_share1_sum, res1_share2_sum)| {
                res1_share1_sum.wrapping_add(*res1_share2_sum)
            })
            .collect();

        let res2s: Vec<u128> = res2_share1_sums
            .iter()
            .zip(res2_share2_sums.iter())
            .map(|(res2_share1_sum, res2_share2_sum)| {
                res2_share1_sum.wrapping_add(*res2_share2_sum)
            })
            .collect();

        for (res1, res2) in res1s.into_iter().zip(res2s.into_iter()) {
            let res = 100. * (res1 as f64) / (res2 as f64);
            println!("{}", res);
            break;
        }
    });
    });

    thread_l.join().unwrap();
    thread_p.join().unwrap();
    let t = timer.elapsed().real.as_micros() as u64;
    println!("baseline query processing time: {} ms", t / 1000);
    let intra_comm = crate::INTRA_SHARD_COMM.lock().unwrap();
    let cross_comm = crate::CROSS_SHARD_COMM.lock().unwrap();
    let consen_num = crate::CONSENSUS_NUM.lock().unwrap();
    crate::tpch::show_comm_cost(*intra_comm, *cross_comm, *consen_num);
}

pub fn exe_q14_single(path: &Path, chunk_size: usize, process_id: u16, debug: bool, intra: bool) {
    println!("loading dataset...");

    let ((lineitem, l_anno), (part, p_anno1, p_anno2)) = load_q14_tables(path, chunk_size);

    let mut l_partkey = lineitem.get_col(0);
    let p_partkey = part.get_col(0);

    let out_len = p_anno1.len();
    let ys_len_larger = p_anno1.len() > l_anno.len();

    let triples = load_beaver_truples();
    let (a1, a2, b1, b2, c1, c2) = obtain_beaver_tripes_by(out_len, triples);

    println!("loading pre-computed information...");
    let bytes = read_q14_pre_compute_info(path);
    let pre_info: PreInfo = PreInfo::deserialize_uncompressed(&*bytes).unwrap();
    let xs_info = pre_info.xs_info;
    let veri_info = pre_info.veri_info;
    let z_commit = pre_info.z_commit;

    // pre-compute sub_product trees
    println!("pre-computing some info...");
    let ys_pts = points_from_num(p_partkey.clone());
    let ys_tree = SubProductTree::new_from_points_parallel(&ys_pts);

    // setup
    println!("doing setup...");
    // let num_chunks = out_len / chunk_size;
    // let (sen_streams, rec_streams) = obtain_tcp_streams(num_chunks, process_id);
    let (sen_streams, rec_streams) = obtain_unix_streams(THREAD_NUM);

    let mut rng = get_fixed_rng();
    let secret = Fr::rand(&mut rng);
    let n_psi = l_partkey.len();
    let max_deg = n_psi - 1;
    // thread_l
    let mut kzg_l = setup_kzg(max_deg);
    kzg_l.setup(secret);
    // thread_p
    let mut kzg_p = setup_kzg(max_deg);
    kzg_p.setup(secret);

    
    let (mut stream_l_p, mut stream_p_l) = UnixStream::pair().unwrap();
    let (mut tx_o_l, mut rx_o_l) = UnixStream::pair().unwrap();
    let (mut tx_o_l2, mut rx_o_l2) = UnixStream::pair().unwrap();

    let timer = howlong::ProcessCPUTimer::new();
    // l: sender
    let thread_l = std::thread::spawn(move || {
        let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
        pool.install(|| {
        let self_id = process_id;
        let mut rng = get_fixed_rng();
        println!("thread l: first PSI...");

        // lineitem local group by
        let (l_anno_sorted, _) = Relation::local_add_agg(&mut l_partkey, &l_anno, &mut rng);
        let xs_pts = points_from_num(l_partkey.clone());
        let xs_tree = SubProductTree::new_from_points_parallel(&xs_pts);

        let share1 = if intra {
            intra_psi_anno_sender_parallel(
                l_partkey.into_iter().map(|x| x as u64).collect(),
                l_anno_sorted.into_iter().map(|x| x as u64).collect(),
                &kzg_l,
                &mut stream_l_p,
                &xs_info,
                &xs_tree,
                debug,
                self_id,
                0,
                ys_len_larger,
                out_len,
                sen_streams,
            )
        } else {
            basic_psi_anno_sender_parallel(
                l_partkey.into_iter().map(|x| x as u64).collect(),
                l_anno_sorted.into_iter().map(|x| x as u64).collect(),
                &xs_tree,
                &mut stream_l_p,
                out_len,
                self_id,
                debug,
                ys_len_larger,
                sen_streams,
            )
        };
        // consensus on share1_first before sending to thread_c
        let bytes = bincode::serialize(&share1).unwrap();
        let dig = digest(Algorithm::SHA256, &bytes);
        if !debug {
            run_consensus(dig, self_id);
        }
        println!("consensus for share1");

        let bytes1 = receive_data_by_stream(&mut rx_o_l);
        let bytes2 = receive_data_by_stream(&mut rx_o_l);
        let p_anno1_share1: Vec<u128> = bincode::deserialize(&bytes1).unwrap();
        let p_anno2_share1: Vec<u128> = bincode::deserialize(&bytes2).unwrap();

        let res1_share1 = vec_mul_1(&p_anno1_share1, &share1, &a1, &b1, &c1, &mut stream_l_p);
        let res1_share1_sum = res1_share1
            .into_iter()
            .fold(0_u128, |acc, x| acc.wrapping_add(x));
        let res2_share1 = vec_mul_1(&p_anno2_share1, &share1, &a1, &b1, &c1, &mut stream_l_p);
        let res2_share1_sum = res2_share1
            .into_iter()
            .fold(0_u128, |acc, x| acc.wrapping_add(x));

        let bytes = bincode::serialize(&(res1_share1_sum, res2_share1_sum)).unwrap();
        send_data_by_stream(&mut tx_o_l2, &bytes, false);
    });
    });

    // p: receiver
    let thread_p = std::thread::spawn(move || {
        let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
        pool.install(|| {
        let self_id = process_id + N * 1;
        println!("thread o: first PSI...");
        let share2 = if intra {
            intra_psi_anno_receiver_parallel(
                &p_partkey,
                false,
                p_partkey.clone().into_iter().map(|x| x as u64).collect(),
                &kzg_p,
                &mut stream_p_l,
                &ys_tree,
                &vec![veri_info],
                vec![z_commit],
                self_id,
                0,
                ys_len_larger,
                debug,
                false,
                rec_streams,
            )
        } else {
            basic_psi_anno_receiver_parallel(
                p_partkey.clone().into_iter().map(|x| x as u64).collect(),
                &mut stream_p_l,
                &ys_tree,
                self_id,
                debug,
                ys_len_larger,
                rec_streams,
            )
        };
        // consensus on share2_first before sending to thread_c
        let bytes = bincode::serialize(&share2).unwrap();
        let dig = digest(Algorithm::SHA256, &bytes);
        if !debug {
            run_consensus(dig, self_id);
        }
        println!("consensus for share2");

        let (p_anno1_share1, p_anno1_share2) =
            gen_shared_anno(p_anno1.into_iter().map(|x| x as u128).collect());
        let (p_anno2_share1, p_anno2_share2) =
            gen_shared_anno(p_anno2.into_iter().map(|x| x as u128).collect());
        let bytes1 = bincode::serialize(&p_anno1_share1).unwrap();
        let bytes2 = bincode::serialize(&p_anno2_share1).unwrap();
        send_data_by_stream(&mut tx_o_l, &bytes1, false);
        send_data_by_stream(&mut tx_o_l, &bytes2, false);

        let res1_share2 = vec_mul_2(&p_anno1_share2, &share2, &a2, &b2, &c2, &mut stream_p_l);
        let res1_share2_sum = res1_share2
            .into_iter()
            .fold(0_u128, |acc, x| acc.wrapping_add(x));
        let res2_share2 = vec_mul_2(&p_anno2_share2, &share2, &a2, &b2, &c2, &mut stream_p_l);
        let res2_share2_sum = res2_share2
            .into_iter()
            .fold(0_u128, |acc, x| acc.wrapping_add(x));
        let bytes = receive_data_by_stream(&mut rx_o_l2);
        let (res1_share1_sum, res2_share1_sum): (u128, u128) =
            bincode::deserialize(&bytes).unwrap();

        let res1 = res1_share1_sum.wrapping_add(res1_share2_sum);
        let res2 = res2_share1_sum.wrapping_add(res2_share2_sum);

        let res = 100. * (res1 as f64) / (res2 as f64);
        println!("{}", res);
    });
    });

    thread_l.join().unwrap();
    thread_p.join().unwrap();
    let t = timer.elapsed().real.as_micros() as u64;
    println!("query processing time: {} ms", t / 1000);
    let intra_comm = crate::INTRA_SHARD_COMM.lock().unwrap();
    let cross_comm = crate::CROSS_SHARD_COMM.lock().unwrap();
    let consen_num = crate::CONSENSUS_NUM.lock().unwrap();
    crate::tpch::show_comm_cost(*intra_comm, *cross_comm, *consen_num);
}
