use std::{
    fs::File, io::{self, BufRead, Write}, os::unix::net::UnixStream, path::Path
};

use ark_bls12_381::{Bls12_381, Fr};
use ark_ec::pairing::Pairing;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use crypto_hash::{digest, Algorithm};
use rayon::{iter::{IndexedParallelIterator, IntoParallelIterator, IntoParallelRefMutIterator, ParallelIterator}, ThreadPoolBuilder};

use crate::{
    garbled_circuit::aggregate::{ev_agg_entire, gb_agg_entire, AggType},
    oep::{permutor_permute, sender_permute},
    psi::{
        subproduct_tree::SubProductTree,
        utils::{
            load_beaver_truples, obtain_beaver_tripes_by, receive_data_by_stream,
            send_data_by_stream, vec_mul_1, vec_mul_2,
        },
        *,
    },
    relation::{get_ind, get_sort_pmt, sort_by_pmt, Relation},
    tpch::{
        utils::{
            batch_rec_u128_to_u32, batch_sen_u128_to_u32, gen_shared_anno, rec_u128_to_u32, sen_u128_to_u32,
        },
        PreInfo, PRE_INFO,
    },
    utils::{
        combine_share, gen_random, get_fixed_rng, obtain_unix_streams, points_from_num, run_consensus
    },
    N, THREAD_NUM,
};

// e.g., path: ./data/1MB
pub fn load_q4_tables(
    path: &Path,
    chunk_size: usize,
) -> ((Relation, Vec<u32>), (Relation, Vec<u32>)) {
    let orders_path = path.join("orders.tbl");
    let lineitem_path = path.join("lineitem.tbl");

    // orders
    let f_orders = File::open(&orders_path).unwrap();
    let reader = io::BufReader::new(f_orders);
    let lines = reader.lines().skip(2);

    let mut o_orderkey = vec![];
    let mut o_orderpriority = vec![];
    let mut o_anno = vec![];

    let (lower_bound, upper_bound) = (19930107, 19930407);
    for line in lines {
        let line = line.unwrap();
        let fields: Vec<&str> = line.split('|').collect();
        o_orderkey.push(fields[0].parse::<u32>().unwrap());
        let priority_info: Vec<&str> = fields[5].split('-').collect();
        o_orderpriority.push(priority_info[0].parse::<u32>().unwrap());
        let date_info: Vec<&str> = fields[4].split('-').collect();
        let date_num = date_info[0].parse::<u32>().unwrap() * 10000
            + date_info[1].parse::<u32>().unwrap() * 100
            + date_info[2].parse::<u32>().unwrap();
        if date_num > lower_bound && date_num < upper_bound {
            o_anno.push(1);
        } else {
            o_anno.push(0);
        }
    }

    let mut orders = Relation::new(vec![o_orderkey, o_orderpriority]);

    let pruned_size = orders.get_size() % chunk_size;
    orders.prune(pruned_size);
    o_anno.truncate(o_anno.len() - pruned_size);

    // println!("{:?}", orders);
    // println!("{:?}", o_anno);

    // lineitem
    let f_lineitem = File::open(&lineitem_path).unwrap();
    let reader = io::BufReader::new(f_lineitem);
    let lines = reader.lines().skip(2);

    let mut l_orderkey = vec![];
    let mut l_anno = vec![];

    for line in lines {
        let line = line.unwrap();
        let fields: Vec<&str> = line.split('|').collect();
        l_orderkey.push(fields[0].parse::<u32>().unwrap());
        let com_date_info: Vec<&str> = fields[10].split('-').collect();
        let com_date_num = com_date_info[0].parse::<u32>().unwrap() * 10000
            + com_date_info[1].parse::<u32>().unwrap() * 100
            + com_date_info[2].parse::<u32>().unwrap();
        let rec_date_info: Vec<&str> = fields[11].split('-').collect();
        let rec_date_num = rec_date_info[0].parse::<u32>().unwrap() * 10000
            + rec_date_info[1].parse::<u32>().unwrap() * 100
            + rec_date_info[2].parse::<u32>().unwrap();
        if com_date_num < rec_date_num {
            l_anno.push(1);
        } else {
            l_anno.push(0);
        }
    }
    let lineitem = Relation::new(vec![l_orderkey]);

    // println!("{:?}", lineitem);
    // println!("{:?}", l_anno);

    ((orders, o_anno), (lineitem, l_anno))
}

pub fn wirte_q4_pre_compute_info(
    path: &Path,
    secret: <Bls12_381 as Pairing>::ScalarField,
    chunk_size: usize,
) {
    let ((orders, _o_anno), (lineitem, l_anno)) = load_q4_tables(path, chunk_size);

    // obtain xs and ys
    let mut l_orderkey = lineitem.get_col(0);
    let o_orderkey = orders.get_col(0);

    // local group by for lineitem
    let mut rng = get_fixed_rng();
    let _ = Relation::local_add_agg(&mut l_orderkey, &l_anno, &mut rng);

    let n_psi = lineitem.get_size();
    let max_deg = n_psi - 1;

    let mut kzg = setup_kzg(max_deg);
    kzg.setup(secret);

    // ys has no duplicate, no need to dedeuplicate
    let xs_pts = points_from_num(l_orderkey);
    let xs_info = kzg.pre_compute_g1(&xs_pts, secret);
    let ys_pts = points_from_num(o_orderkey);
    let veri_info = kzg.pre_compute_g1(&ys_pts, secret);
    let z_commit = kzg.pre_compute_z_commitment(&ys_pts, secret);

    // write to file
    let data = PreInfo {
        xs_info: xs_info,
        veri_info: veri_info,
        z_commit: z_commit,
    };

    let mut data_bytes: Vec<u8> = vec![];
    data.serialize_uncompressed(&mut data_bytes).unwrap();

    println!("writing pre-computed info to files...");
    let dir_path = path.join("q4");
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

pub(crate) fn read_q4_pre_compute_info(path: &Path) -> Vec<u8> {
    let file_path = path.join("q4").join(PRE_INFO);
    let mut file = File::open(file_path).unwrap();
    let mut buffer = Vec::new();
    io::Read::read_to_end(&mut file, &mut buffer).unwrap();
    buffer
}

pub fn exe_q4_batch(
    path: &Path,
    chunk_size: usize,
    query_num: usize,
    process_id: u16,
    debug: bool,
) {
    println!("loading dataset...");
    let ((orders, o_anno), (lineitem, l_anno)) = load_q4_tables(path, chunk_size);
    let o_orderkey = orders.get_col(0);
    let o_orderpriority = orders.get_col(1);

    let mut l_orderkey = lineitem.get_col(0);

    let out_len = o_anno.len();
    let ys_len_larger = o_anno.len() > l_anno.len();

    let triples = load_beaver_truples();
    let (a1, a2, b1, b2, c1, c2) = obtain_beaver_tripes_by(out_len, triples);

    // load pre_info for q4
    println!("loading pre-computed information...");
    let bytes = read_q4_pre_compute_info(path);
    let pre_info: PreInfo = PreInfo::deserialize_uncompressed(&*bytes).unwrap();
    let xs_info = pre_info.xs_info;
    let veri_info = pre_info.veri_info;
    let z_commit = pre_info.z_commit;

    // pre-compute subproduct_tree
    let ys_pts = points_from_num(o_orderkey.clone());
    let ys_tree = SubProductTree::new_from_points_parallel(&ys_pts);

    // setup
    let (sen_streams, rec_streams) = obtain_unix_streams(THREAD_NUM);
    let (mut stream_l_o, mut stream_o_l) = UnixStream::pair().unwrap();

    let (mut stream_l_o2s, mut stream_o_l2s) = obtain_unix_streams(THREAD_NUM);
    let (mut tx_o_l, mut rx_o_l) = UnixStream::pair().unwrap();
    let (mut tx_l_o, mut rx_l_o) = UnixStream::pair().unwrap();
    let (mut tx_l_o2, mut rx_l_o2) = UnixStream::pair().unwrap();
    let group_size = query_num/THREAD_NUM;

    println!("doing setup...");
    let mut rng = get_fixed_rng();
    let secret = Fr::rand(&mut rng);
    let n_psi = lineitem.get_size();
    let max_deg_1st = n_psi - 1;
    // kzg setup is time consuming, but can be done off-line
    let mut kzg_l = setup_kzg(max_deg_1st);
    kzg_l.setup(secret);
    let mut kzg_o = setup_kzg(max_deg_1st);
    kzg_o.setup(secret);

    let timer = howlong::ProcessCPUTimer::new();
    let thread_l = std::thread::spawn(move || {
        let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
        pool.install(|| {
        let self_id = process_id;
        let mut rng = get_fixed_rng();
        let (l_anno_sorted, _) = Relation::local_add_agg(&mut l_orderkey, &l_anno, &mut rng);
        let xs_pts = points_from_num(l_orderkey.clone());
        let xs_tree = SubProductTree::new_from_points_parallel(&xs_pts);
        let share1s = batch_psi_anno_sender_parallel(
            vec![l_orderkey.into_iter().map(|x| x as u64).collect(); query_num],
            vec![l_anno_sorted.into_iter().map(|x| x as u64).collect(); query_num],
            &kzg_l,
            &mut stream_l_o,
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
        // receive o_anno_1 from o
        let bytes = receive_data_by_stream(&mut rx_o_l);
        let o_anno_1s: Vec<Vec<u128>> = bincode::deserialize(&bytes).unwrap();

        // do vec mul using beaver triple
        let mut res_share1s = vec![];
        for (o_anno_1, share1) in o_anno_1s.iter().zip(share1s.iter()) {
            res_share1s.push(vec_mul_1(o_anno_1, share1, &a1, &b1, &c1, &mut stream_l_o));
        }
        let res_anno1s = batch_sen_u128_to_u32(res_share1s, &mut rx_o_l, &mut tx_l_o);

        let mut sorted_anno1s = vec![];
        for res_anno1 in res_anno1s.iter() {
            sorted_anno1s.push(sender_permute(&mut stream_l_o, &res_anno1));
        }

        // let mut agg_add_res2s = vec![];
        // for sorted_anno1 in sorted_anno1s {
        //     agg_add_res2s.push(ev_agg_fast(
        //         chunk_size,
        //         sorted_anno1.into_iter().map(|x| x as u128).collect(),
        //         stream_l_o2.try_clone().unwrap(),
        //         AggType::Add,
        //     ));
        // }

        let mut agg_add_res2s: Vec<Vec<u128>> = vec![];
        for i in 0..group_size {
            let mut sub_res: Vec<Vec<u128>> = stream_l_o2s.par_iter_mut().zip(sorted_anno1s[i*group_size..(i+1)*group_size].into_par_iter()).map(|(stream, data)| {
                ev_agg_entire(
                    &data.iter().map(|x| *x as u128).collect(),
                    stream,
                    AggType::Add,
                )
            }).collect();
            agg_add_res2s.append(&mut sub_res);
        }

        // let agg_add_res2s: Vec<Vec<u128>> = sorted_anno1s
        //     .into_par_iter()
        //     .zip(stream_l_o2s.into_par_iter())
        //     .map(|(sorted_anno1, mut stream_l_o2)| {
        //         ev_agg_entire(
        //             &sorted_anno1.into_iter().map(|x| x as u128).collect(),
        //             &mut stream_l_o2,
        //             AggType::Add,
        //         )
        //     })
        //     .collect();

        // send agg_add_res2 to o
        let bytes = bincode::serialize(&agg_add_res2s).unwrap();
        send_data_by_stream(&mut tx_l_o2, &bytes, false);
        });
    });

    let thread_o = std::thread::spawn(move || {
        let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
        pool.install(|| {
        let self_id = process_id + N * 1;
        let share2s = batch_psi_anno_receiver_parallel(
            &vec![o_orderkey.clone(); query_num],
            false,
            vec![o_orderkey.clone().into_iter().map(|x| x as u64).collect(); query_num],
            &kzg_o,
            &mut stream_o_l,
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
        let (o_anno_1, o_anno_2) = gen_shared_anno(o_anno.into_iter().map(|x| x as u128).collect());
        let o_anno_1s = vec![o_anno_1; query_num];
        let o_anno_2s = vec![o_anno_2; query_num];
        let bytes = bincode::serialize(&o_anno_1s).unwrap();
        send_data_by_stream(&mut tx_o_l, &bytes, false);

        let mut res_share2s = vec![];
        for (o_anno_2, share2) in o_anno_2s.iter().zip(share2s.iter()) {
            res_share2s.push(vec_mul_2(o_anno_2, share2, &a2, &b2, &c2, &mut stream_o_l));
        }

        // convert u128 share to u32 share (for later OP)
        let res_anno2s = batch_rec_u128_to_u32(res_share2s, &mut tx_o_l, &mut rx_l_o);

        let sort_pmt = get_sort_pmt(&o_orderpriority);
        let sorted_orderpriority = sort_by_pmt(&o_orderpriority, &sort_pmt);
        let mut sorted_anno2s = vec![];
        for res_anno2 in res_anno2s.iter() {
            sorted_anno2s.push(permutor_permute(&mut stream_o_l, &sort_pmt, res_anno2));
        }
        // circuit to do oblivious add_agg
        let ind = get_ind(&sorted_orderpriority);
        let agg_add_res1 = gen_random::<u128>(out_len);

        for i in 0..group_size {
            stream_o_l2s.par_iter_mut().zip(sorted_anno2s[i*group_size..(i+1)*group_size].into_par_iter()).for_each(|(stream, data)| {
                gb_agg_entire(
                    &ind,
                    &data.iter().map(|v| *v as u128).collect(),
                    stream,
                    AggType::Add,
                    &agg_add_res1,
                );
            });
        }

        // sorted_anno2s
        //     .into_par_iter()
        //     .zip(stream_o_l2s.into_par_iter())
        //     .for_each(|(sorted_anno2, mut stream_o_l2)| {
        //         gb_agg_entire(
        //             &ind,
        //             &sorted_anno2.iter().map(|v| *v as u128).collect(),
        //             &mut stream_o_l2,
        //             AggType::Add,
        //             &agg_add_res1,
        //         );
        //     });

        // for sorted_anno2 in sorted_anno2s.into_iter() {
        //     gb_agg_fast(
        //         chunk_size,
        //         ind.clone(),
        //         sorted_anno2.iter().map(|v| *v as u128).collect(),
        //         stream_o_l2.try_clone().unwrap(),
        //         AggType::Add,
        //         agg_add_res1.clone(),
        //     );
        // }
        let bytes = receive_data_by_stream(&mut rx_l_o2);
        let agg_add_res2s: Vec<Vec<u128>> = bincode::deserialize(&bytes).unwrap();
        let mut res_annos = vec![];
        for agg_add_res2 in agg_add_res2s.into_iter() {
            res_annos.push(combine_share(agg_add_res1.clone(), agg_add_res2));
        }

        // keep non-zero-anno tuples from o
        for res_anno in res_annos {
            let mut col_o_orderpriority = vec![];
            let mut col_anno = vec![];
            for i in 0..res_anno.len() {
                if res_anno[i] != 0 {
                    col_o_orderpriority.push(sorted_orderpriority[i]);
                    col_anno.push(res_anno[i] as u32);
                }
            }
            // the clean result relation
            let res_relation = Relation::new(vec![col_o_orderpriority, col_anno]);
            if process_id == 0 {
                println!("{:?}", res_relation);
            }
        }
    });
    });

    thread_l.join().unwrap();
    thread_o.join().unwrap();
    let t = timer.elapsed().real.as_micros() as u64;
    println!("query processing time: {} ms", t / 1000);
    let intra_comm = crate::INTRA_SHARD_COMM.lock().unwrap();
    let cross_comm = crate::CROSS_SHARD_COMM.lock().unwrap();
    let consen_num = crate::CONSENSUS_NUM.lock().unwrap();
    crate::tpch::show_comm_cost(*intra_comm, *cross_comm, *consen_num);
}

pub fn exe_q4_single(path: &Path, chunk_size: usize, process_id: u16, debug: bool, intra: bool) {
    println!("loading dataset...");
    let ((orders, o_anno), (lineitem, l_anno)) = load_q4_tables(path, chunk_size);
    let o_orderkey = orders.get_col(0);
    let o_orderpriority = orders.get_col(1);

    let mut l_orderkey = lineitem.get_col(0);

    let out_len = o_anno.len();
    let ys_len_larger = o_anno.len() > l_anno.len();

    let triples = load_beaver_truples();
    let (a1, a2, b1, b2, c1, c2) = obtain_beaver_tripes_by(out_len, triples);

    // load pre_info for q4
    println!("loading pre-computed information...");
    let bytes = read_q4_pre_compute_info(path);
    let pre_info: PreInfo = PreInfo::deserialize_uncompressed(&*bytes).unwrap();
    let xs_info = pre_info.xs_info;
    let veri_info = pre_info.veri_info;
    let z_commit = pre_info.z_commit;

    // pre-compute subproduct_tree
    let ys_pts = points_from_num(o_orderkey.clone());
    let ys_tree = SubProductTree::new_from_points_parallel(&ys_pts);

    // setup
    let (sen_streams, rec_streams) = obtain_unix_streams(THREAD_NUM);

    println!("doing setup...");
    let mut rng = get_fixed_rng();
    let secret = Fr::rand(&mut rng);
    let n_psi = lineitem.get_size();
    let max_deg_1st = n_psi - 1;
    // kzg setup is time consuming, but can be done off-line
    let mut kzg_l = setup_kzg(max_deg_1st);
    kzg_l.setup(secret);
    let mut kzg_o = setup_kzg(max_deg_1st);
    kzg_o.setup(secret);

    
    let (mut stream_l_o, mut stream_o_l) = UnixStream::pair().unwrap();
    let (mut stream_l_o2, mut stream_o_l2) = UnixStream::pair().unwrap();
    let (mut tx_o_l, mut rx_o_l) = UnixStream::pair().unwrap();
    let (mut tx_l_o, mut rx_l_o) = UnixStream::pair().unwrap();
    let (mut tx_l_o2, mut rx_l_o2) = UnixStream::pair().unwrap();

    let timer = howlong::ProcessCPUTimer::new();
    let thread_l = std::thread::spawn(move || {
        let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
        pool.install(|| {
        let self_id = process_id;
        let mut rng = get_fixed_rng();
        let (l_anno_sorted, _) = Relation::local_add_agg(&mut l_orderkey, &l_anno, &mut rng);
        let xs_pts = points_from_num(l_orderkey.clone());
        let xs_tree = SubProductTree::new_from_points_parallel(&xs_pts);
        let share1 = if intra {
            intra_psi_anno_sender_parallel(
                l_orderkey.into_iter().map(|x| x as u64).collect(),
                l_anno_sorted.into_iter().map(|x| x as u64).collect(),
                &kzg_l,
                &mut stream_l_o,
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
                l_orderkey.into_iter().map(|x| x as u64).collect(),
                l_anno_sorted.into_iter().map(|x| x as u64).collect(),
                &xs_tree,
                &mut stream_l_o,
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
        // receive o_anno_1 from o
        let bytes = receive_data_by_stream(&mut rx_o_l);
        let o_anno_1: Vec<u128> = bincode::deserialize(&bytes).unwrap();
        // let o_anno_1 = rx_o_l.recv().unwrap();

        // do vec mul using beaver triple
        let res_share1 = vec_mul_1(&o_anno_1, &share1, &a1, &b1, &c1, &mut stream_l_o);
        let res_anno1 = sen_u128_to_u32(res_share1, &mut rx_o_l, &mut tx_l_o);

        let sorted_anno1 = sender_permute(&mut stream_l_o, &res_anno1);

        let agg_add_res2 = ev_agg_entire(
            &sorted_anno1.iter().map(|x| *x as u128).collect(),
            &mut stream_l_o2,
            AggType::Add,
        );

        // send agg_add_res2 to o
        let bytes = bincode::serialize(&agg_add_res2).unwrap();
        send_data_by_stream(&mut tx_l_o2, &bytes, false);
    });
    });

    let thread_o = std::thread::spawn(move || {
        let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
        pool.install(|| {
        let self_id = process_id + N * 1;
        let share2 = if intra {
            intra_psi_anno_receiver_parallel(
                &o_orderkey,
                false,
                o_orderkey.clone().into_iter().map(|x| x as u64).collect(),
                &kzg_o,
                &mut stream_o_l,
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
                o_orderkey.clone().into_iter().map(|x| x as u64).collect(),
                &mut stream_o_l,
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
        // println!("consensus for share2");
        let (o_anno_1, o_anno_2) = gen_shared_anno(o_anno.into_iter().map(|x| x as u128).collect());
        let bytes = bincode::serialize(&o_anno_1).unwrap();
        send_data_by_stream(&mut tx_o_l, &bytes, false);

        let res_share2 = vec_mul_2(&o_anno_2, &share2, &a2, &b2, &c2, &mut stream_o_l);

        // convert u128 share to u32 share (for later OP)
        let res_anno2 = rec_u128_to_u32(res_share2, &mut tx_o_l, &mut rx_l_o);

        let sort_pmt = get_sort_pmt(&o_orderpriority);
        let sorted_orderpriority = sort_by_pmt(&o_orderpriority, &sort_pmt);
        let sorted_anno2 = permutor_permute(&mut stream_o_l, &sort_pmt, &res_anno2);

        // circuit to do oblivious add_agg
        let ind = get_ind(&sorted_orderpriority);
        let agg_add_res1 = gen_random::<u128>(out_len);
        gb_agg_entire(
            &ind,
            &sorted_anno2.iter().map(|v| *v as u128).collect(),
            &mut stream_o_l2,
            AggType::Add,
            &agg_add_res1,
        );

        let bytes = receive_data_by_stream(&mut rx_l_o2);
        let agg_add_res2: Vec<u128> = bincode::deserialize(&bytes).unwrap();
        let res_anno = combine_share(agg_add_res1, agg_add_res2);
        // keep non-zero-anno tuples from o
        let mut col_o_orderpriority = vec![];
        let mut col_anno = vec![];
        for i in 0..res_anno.len() {
            if res_anno[i] != 0 {
                col_o_orderpriority.push(sorted_orderpriority[i]);
                col_anno.push(res_anno[i] as u32);
            }
        }

        // the clean result relation
        let _res_relation = Relation::new(vec![col_o_orderpriority, col_anno]);
        // println!("{:?}", res_relation);
    });
    });
    thread_l.join().unwrap();
    thread_o.join().unwrap();
    let t = timer.elapsed().real.as_micros() as u64;
    println!("query processing time: {} ms", t / 1000);
    let intra_comm = crate::INTRA_SHARD_COMM.lock().unwrap();
    let cross_comm = crate::CROSS_SHARD_COMM.lock().unwrap();
    let consen_num = crate::CONSENSUS_NUM.lock().unwrap();
    crate::tpch::show_comm_cost(*intra_comm, *cross_comm, *consen_num);
}

mod test {
    #[test]
    fn test_load_data() {
        use super::*;
        let path = Path::new("./data/1MB");
        load_q4_tables(path, 5);
    }
}
