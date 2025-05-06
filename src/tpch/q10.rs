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
        setup_kzg,
        subproduct_tree::SubProductTree,
        utils::{
            load_beaver_truples, obtain_beaver_tripes_by, receive_data_by_stream,
            send_data_by_stream, vec_mul_1, vec_mul_2,
        },
        *,
    },
    relation::{get_ind, get_sort_pmt, local_group_by_with_dummy, sort_by_pmt, Relation},
    tpch::utils::{
        batch_rec_u128_to_u32, batch_rec_u32_to_u128, batch_sen_u128_to_u32, batch_sen_u32_to_u128,
        gen_shared_anno, rec_u128_to_u32,
        rec_u32_to_u128, sen_u128_to_u32, sen_u32_to_u128,
    },
    utils::{
        combine_share, gen_random, get_fixed_rng, obtain_unix_streams, points_from_num, run_consensus
    },
    N, THREAD_NUM,
};

use super::{PreInfo, PRE_INFO};

// e.g., path: ./data/1MB
pub fn load_q10_tables(
    path: &Path,
    chunk_size: usize,
) -> (
    (Relation, Vec<u32>),
    (Relation, Vec<u32>),
    (Relation, Vec<u32>),
) {
    let customer_path = path.join("customer.tbl");
    let orders_path = path.join("orders.tbl");
    let lineitem_path = path.join("lineitem.tbl");

    // customer
    let f_customer = File::open(&customer_path).unwrap();
    let reader = io::BufReader::new(f_customer);
    let lines = reader.lines().skip(2);
    let mut c_custkey = vec![];
    let mut c_name = vec![];
    let mut c_nationkey = vec![];
    let mut c_anno = vec![];
    for line in lines {
        let line = line.unwrap();
        let fields: Vec<&str> = line.split('|').collect();
        c_custkey.push(fields[0].parse::<u32>().unwrap());
        // name and custkey are identical
        c_name.push(fields[0].parse::<u32>().unwrap());
        c_nationkey.push(fields[3].parse::<u32>().unwrap());
        c_anno.push(fields[9].parse::<u32>().unwrap());
    }

    let mut customer = Relation::new(vec![c_custkey, c_name, c_nationkey]);
    let pruned_size = customer.get_size() % chunk_size;
    customer.prune(pruned_size);
    c_anno.truncate(c_anno.len() - pruned_size);

    // println!("{:?}", customer);
    // println!("{:?}", c_anno);

    // orders
    let f_orders = File::open(&orders_path).unwrap();
    let reader = io::BufReader::new(f_orders);
    let lines = reader.lines().skip(2);
    let mut o_orderkey = vec![];
    let mut o_custkey = vec![];
    let mut o_anno = vec![];

    for line in lines {
        let line = line.unwrap();
        let fields: Vec<&str> = line.split('|').collect();
        o_orderkey.push(fields[0].parse::<u32>().unwrap());
        o_custkey.push(fields[1].parse::<u32>().unwrap());
        o_anno.push(fields[11].parse::<u32>().unwrap());
    }

    let mut orders = Relation::new(vec![o_orderkey, o_custkey]);

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
        l_anno.push(fields[17].parse::<u32>().unwrap());
    }

    let lineitem = Relation::new(vec![l_orderkey]);

    // println!("{:?}", lineitem);
    // println!("{:?}", l_anno);

    ((customer, c_anno), (orders, o_anno), (lineitem, l_anno))
}

pub fn wirte_q10_pre_compute_info(
    path: &Path,
    secret: <Bls12_381 as Pairing>::ScalarField,
    chunk_size: usize,
) {
    let ((customer, _c_anno), (orders, _o_anno), (lineitem, l_anno)) =
        load_q10_tables(path, chunk_size);

    let mut pre_infos = vec![];

    // first psi
    let mut l_orderkey = lineitem.get_col(0); // xs: has duplicate
    let o_orderkey = orders.get_col(0); // ys: unique
    let mut rng = get_fixed_rng();
    let _l_anno_sorted = Relation::local_add_agg(&mut l_orderkey, &l_anno, &mut rng);
    let n_psi = l_orderkey.len();
    let max_deg = n_psi - 1;
    let mut kzg = setup_kzg(max_deg);
    kzg.setup(secret);
    let xs_pts = points_from_num(l_orderkey);
    let xs_info = kzg.pre_compute_g1(&xs_pts, secret);
    let ys_pts = points_from_num(o_orderkey);
    let veri_info = kzg.pre_compute_g1(&ys_pts, secret);
    let z_commit = kzg.pre_compute_z_commitment(&ys_pts, secret);
    let pre_info_1 = PreInfo {
        xs_info: xs_info,
        veri_info: veri_info,
        z_commit: z_commit,
    };
    pre_infos.push(pre_info_1);

    // second psi
    let o_custkey = orders.get_col(1); // xs has duplicate
    let c_custkey = customer.get_col(0); // ys: unique
    let sort_pmt = get_sort_pmt(&o_custkey);
    let sorted_o_custkey = sort_by_pmt(&o_custkey, &sort_pmt);
    let dummyed_o_custkey = local_group_by_with_dummy(&sorted_o_custkey);

    let n_psi = o_custkey.len();
    let max_deg = n_psi - 1;
    let mut kzg = setup_kzg(max_deg);
    kzg.setup(secret);
    let xs_pts = points_from_num(dummyed_o_custkey);
    let xs_info = kzg.pre_compute_g1(&xs_pts, secret);
    let ys_pts = points_from_num(c_custkey);
    let veri_info = kzg.pre_compute_g1(&ys_pts, secret);
    let z_commit = kzg.pre_compute_z_commitment(&ys_pts, secret);
    let pre_info_2 = PreInfo {
        xs_info: xs_info,
        veri_info: veri_info,
        z_commit: z_commit,
    };
    pre_infos.push(pre_info_2);

    let mut data_bytes: Vec<u8> = vec![];
    pre_infos.serialize_uncompressed(&mut data_bytes).unwrap();

    println!("writing pre-computed info to files...");
    let dir_path = path.join("q10");
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

pub(crate) fn read_q10_pre_compute_info(path: &Path) -> Vec<u8> {
    let file_path = path.join("q10").join(PRE_INFO);
    let mut file = File::open(file_path).unwrap();
    let mut buffer = Vec::new();
    io::Read::read_to_end(&mut file, &mut buffer).unwrap();
    buffer
}


pub fn exe_q10_batch(
    path: &Path,
    chunk_size: usize,
    query_num: usize,
    process_id: u16,
    debug: bool,
) {
    println!("loading dataset...");

    let ((customer, c_anno), (orders, o_anno), (lineitem, l_anno)) =
        load_q10_tables(path, chunk_size);
    let c_custkey = customer.get_col(0);
    let c_name = customer.get_col(1);
    let c_nationkey = customer.get_col(2);
    let o_orderkey = orders.get_col(0);
    let o_custkey = orders.get_col(1);
    let mut l_orderkey = lineitem.get_col(0);

    let out_len_1st = o_anno.len();
    let out_len_2nd = c_anno.len();

    let ys_len_larger_1st = o_anno.len() > l_anno.len();
    let ys_len_larger_2nd = c_anno.len() > o_anno.len();

    let triples = load_beaver_truples();
    let (a1_1st, a2_1st, b1_1st, b2_1st, c1_1st, c2_1st) =
        obtain_beaver_tripes_by(out_len_1st, triples.clone());
    let (a1_2nd, a2_2nd, b1_2nd, b2_2nd, c1_2nd, c2_2nd) =
        obtain_beaver_tripes_by(out_len_2nd, triples);

    println!("loading pre-computed information...");
    let bytes = read_q10_pre_compute_info(path);
    let mut pre_infos: Vec<PreInfo> = Vec::<PreInfo>::deserialize_uncompressed(&*bytes).unwrap();
    // order matters
    let pre_info_2 = pre_infos.remove(1);
    let xs_info_2 = pre_info_2.xs_info;
    let veri_info_2 = pre_info_2.veri_info;
    let z_commit_2 = pre_info_2.z_commit;
    let pre_info_1 = pre_infos.remove(0);
    let xs_info_1 = pre_info_1.xs_info;
    let veri_info_1 = pre_info_1.veri_info;
    let z_commit_1 = pre_info_1.z_commit;

    // pre-compute sub_product trees
    println!("pre-computing some info...");
    let ys_pts_1st = points_from_num(o_orderkey.clone());
    let ys_tree_first = SubProductTree::new_from_points_parallel(&ys_pts_1st);
    let ys_pts_2nd = points_from_num(c_custkey.clone());
    let ys_tree_2nd = SubProductTree::new_from_points_parallel(&ys_pts_2nd);

    // setup
    println!("doing setup...");
    let (sen_streams_1st, rec_streams_1st) = obtain_unix_streams(THREAD_NUM);
    let (sen_streams_2nd, rec_streams_2nd) = obtain_unix_streams(THREAD_NUM);
    let (sen_streams_2nd_oep, rec_streams_2nd_oep) = obtain_unix_streams(THREAD_NUM);
    let (mut stream_l_o2s, mut stream_o_l2s) = obtain_unix_streams(THREAD_NUM);

    let mut rng = get_fixed_rng();
    let secret = Fr::rand(&mut rng);
    let n_1st_psi = l_orderkey.len();
    let max_deg_1st = n_1st_psi - 1;
    let n_2nd_psi = o_custkey.len();
    let max_deg_2nd = n_2nd_psi - 1;

    // thread_l
    let mut kzg_l_1st = setup_kzg(max_deg_1st);
    kzg_l_1st.setup(secret);
    // thread_o
    let mut kzg_o_1st = setup_kzg(max_deg_1st);
    kzg_o_1st.setup(secret);
    let mut kzg_o_2nd = setup_kzg(max_deg_2nd);
    kzg_o_2nd.setup(secret);
    // thread_c
    let mut kzg_c_2nd = setup_kzg(max_deg_2nd);
    kzg_c_2nd.setup(secret);

    let (mut stream_l_o, mut stream_o_l) = UnixStream::pair().unwrap();
    
    // IMPORTANT: should not re-use stream_l_o for obliAgg, because stream_l_o has been updated (mut ref), while obliAgg requires immutable ref
    let (mut stream_o_c, mut stream_c_o) = UnixStream::pair().unwrap();
    let (mut tx_o_l, mut rx_o_l) = UnixStream::pair().unwrap();
    let (mut tx_o_l2, mut rx_o_l2) = UnixStream::pair().unwrap();
    let (mut tx_o_c, mut rx_o_c) = UnixStream::pair().unwrap();
    let (mut tx_o_c2, mut rx_o_c2) = UnixStream::pair().unwrap();
    let (mut tx_l_o, mut rx_l_o) = UnixStream::pair().unwrap();
    let (mut tx_l_o2, mut rx_l_o2) = UnixStream::pair().unwrap();
    let (mut tx_l_c, mut rx_l_c) = UnixStream::pair().unwrap();
    let (mut tx_c_o, mut rx_c_o) = UnixStream::pair().unwrap();
    let group_size = query_num/THREAD_NUM;

    let timer = howlong::ProcessCPUTimer::new();
    let thread_l = std::thread::spawn(move || {
        let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
        pool.install(|| {
        let self_id = process_id;
        //### step 1: O.semijoin(L), L as sender
        let mut rng = get_fixed_rng();
        // lineitem local group by
        let (l_anno_sorted, _) = Relation::local_add_agg(&mut l_orderkey, &l_anno, &mut rng);
        let xs_pts = points_from_num(l_orderkey.clone());
        let xs_tree = SubProductTree::new_from_points_parallel(&xs_pts);

        let share1_firsts = batch_psi_anno_sender_parallel(
            vec![l_orderkey.into_iter().map(|x| x as u64).collect(); query_num],
            vec![l_anno_sorted.into_iter().map(|x| x as u64).collect(); query_num],
            &kzg_l_1st,
            &mut stream_l_o,
            &vec![xs_info_1; query_num],
            &vec![xs_tree; query_num],
            debug,
            self_id,
            ys_len_larger_1st,
            out_len_1st,
            sen_streams_1st,
        );

        // consensus on share1_first before sending to thread_c
        let bytes = bincode::serialize(&share1_firsts).unwrap();
        let dig = digest(Algorithm::SHA256, &bytes);
        if !debug {
            run_consensus(dig, self_id);
        }
        // receive o_anno_1 from o
        let bytes = receive_data_by_stream(&mut rx_o_l);
        let o_anno_1s: Vec<Vec<u128>> = bincode::deserialize(&bytes).unwrap();

        // do vec mul using beaver triple
        let res1_share1s: Vec<Vec<u128>> = o_anno_1s
            .iter()
            .zip(share1_firsts.iter())
            .map(|(o_anno_1, share1_first)| {
                vec_mul_1(
                    &o_anno_1,
                    &share1_first,
                    &a1_1st,
                    &b1_1st,
                    &c1_1st,
                    &mut stream_l_o,
                )
            })
            .collect();
        let res1_anno1s = batch_sen_u128_to_u32(res1_share1s, &mut rx_o_l, &mut tx_l_o);
        let sorted_anno1s: Vec<Vec<u32>> = res1_anno1s
            .iter()
            .map(|res1_anno1| sender_permute(&mut stream_l_o, &res1_anno1))
            .collect();


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

        // step1 finished
        let agg_add_res2s = batch_rec_u128_to_u32(agg_add_res2s, &mut tx_l_o2, &mut rx_o_l2);
        // send agg_or_res2 to thread_c
        let bytes = bincode::serialize(&agg_add_res2s).unwrap();
        send_data_by_stream(&mut tx_l_c, &bytes, false);
        // finish for thread_l
    });
    });

    let thread_o = std::thread::spawn(move || {
        let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
        pool.install(|| {
        let self_id = process_id + N * 1;
        //### step 1: O.semijoin(L), O as receiver
        let share2_firsts = batch_psi_anno_receiver_parallel(
            &vec![o_orderkey.clone(); query_num],
            false,
            vec![o_orderkey.clone().into_iter().map(|x| x as u64).collect(); query_num],
            &kzg_o_1st,
            &mut stream_o_l,
            &vec![ys_tree_first; query_num],
            &vec![veri_info_1; query_num],
            vec![z_commit_1; query_num],
            self_id,
            ys_len_larger_1st,
            debug,
            rec_streams_1st,
        );

        // consensus on share2_first before sending to thread_c
        let bytes = bincode::serialize(&share2_firsts).unwrap();
        let dig = digest(Algorithm::SHA256, &bytes);
        if !debug {
            run_consensus(dig, self_id);
        }
        let (o_anno_1, o_anno_2) = gen_shared_anno(o_anno.into_iter().map(|x| x as u128).collect());
        let o_anno_1s = vec![o_anno_1; query_num];
        let o_anno_2s = vec![o_anno_2; query_num];
        let bytes = bincode::serialize(&o_anno_1s).unwrap();
        send_data_by_stream(&mut tx_o_l, &bytes, false);

        let res1_share2s: Vec<Vec<u128>> = o_anno_2s
            .iter()
            .zip(share2_firsts.iter())
            .map(|(o_anno_2, share2_first)| {
                vec_mul_2(
                    o_anno_2,
                    share2_first,
                    &a2_1st,
                    &b2_1st,
                    &c2_1st,
                    &mut stream_o_l,
                )
            })
            .collect();

        // convert u128 share to u32 share (for later OP)
        let res1_anno2s = batch_rec_u128_to_u32(res1_share2s, &mut tx_o_l, &mut rx_l_o);

        // get sort pmt & sort key, use OP to sort shared anno (u32 share)
        let sort_pmt = get_sort_pmt(&o_custkey);
        let sorted_o_custkey = sort_by_pmt(&o_custkey, &sort_pmt);

        let sorted_anno2s: Vec<Vec<u32>> = res1_anno2s
            .iter()
            .map(|res1_anno2| permutor_permute(&mut stream_o_l, &sort_pmt, &res1_anno2))
            .collect();

        // circuit to do oblivious add_agg
        let ind = get_ind(&sorted_o_custkey);
        let agg_add_res1 = gen_random::<u128>(out_len_1st);

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

        let dummyed_o_custkey = local_group_by_with_dummy(&sorted_o_custkey);

        //### step2: C.semijoin(O), O as sender
        let agg_add_res1s =
            batch_sen_u128_to_u32(vec![agg_add_res1; query_num], &mut rx_l_o2, &mut tx_o_l2);

        let xs_pts = points_from_num(dummyed_o_custkey.clone());
        let xs_tree = SubProductTree::new_from_points_parallel(&xs_pts);

        let share1_seconds = batch_psi_shared_anno_sender_parallel(
            vec![dummyed_o_custkey.into_iter().map(|v| v as u64).collect(); query_num],
            agg_add_res1s,
            &kzg_o_2nd,
            &mut stream_o_c,
            &vec![xs_info_2; query_num],
            &vec![xs_tree; query_num],
            debug,
            self_id,
            ys_len_larger_2nd,
            out_len_2nd,
            chunk_size,
            sen_streams_2nd,
            sen_streams_2nd_oep,
        );

        // col_mul using beaver_triple
        let bytes = receive_data_by_stream(&mut rx_c_o);
        let c_anno1s: Vec<Vec<u128>> = bincode::deserialize(&bytes).unwrap();
        let share1_seconds = batch_rec_u32_to_u128(share1_seconds, &mut tx_o_c, &mut rx_c_o);

        let res2_share1s: Vec<Vec<u128>> = c_anno1s
            .iter()
            .zip(share1_seconds.iter())
            .map(|(c_anno1, share1_second)| {
                vec_mul_1(
                    c_anno1,
                    share1_second,
                    &a1_2nd,
                    &b1_2nd,
                    &c1_2nd,
                    &mut stream_o_c,
                )
            })
            .collect();

        // reveal res2_share1 to thread_c
        let bytes = bincode::serialize(&res2_share1s).unwrap();
        send_data_by_stream(&mut tx_o_c2, &bytes, false);
        // thread_o finish
        });
    });

    let thread_c = std::thread::spawn(move || {
        let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
        pool.install(|| {
        let self_id = process_id + N * 2;

        //### step2: C.semijoin(O), C as receiver
        let bytes = receive_data_by_stream(&mut rx_l_c);
        let agg_add_res2s: Vec<Vec<u32>> = bincode::deserialize(&bytes).unwrap();

        // c_custkey is originally sorted
        let share2_seconds = batch_psi_shared_anno_receiver_parallel(
            &vec![c_custkey.clone(); query_num],
            false,
            vec![c_custkey.iter().map(|x| *x as u64).collect(); query_num],
            agg_add_res2s,
            &kzg_c_2nd,
            &mut stream_c_o,
            &vec![ys_tree_2nd; query_num],
            &vec![veri_info_2; query_num],
            vec![z_commit_2; query_num],
            chunk_size,
            self_id,
            ys_len_larger_2nd,
            debug,
            rec_streams_2nd,
            rec_streams_2nd_oep,
        );

        let (c_anno_1, c_anno_2) = gen_shared_anno(c_anno.into_iter().map(|x| x as u128).collect());
        let c_anno_1s = vec![c_anno_1; query_num];
        let c_anno_2s = vec![c_anno_2; query_num];

        let bytes = bincode::serialize(&c_anno_1s).unwrap();
        send_data_by_stream(&mut tx_c_o, &bytes, false);

        let share2_seconds = batch_sen_u32_to_u128(share2_seconds, &mut rx_o_c, &mut tx_c_o);

        let res2_share2s: Vec<Vec<u128>> = c_anno_2s
            .iter()
            .zip(share2_seconds.iter())
            .map(|(c_anno_2, share2_second)| {
                vec_mul_2(
                    c_anno_2,
                    share2_second,
                    &a2_2nd,
                    &b2_2nd,
                    &c2_2nd,
                    &mut stream_c_o,
                )
            })
            .collect();
        // get revealed anno for c
        let bytes = receive_data_by_stream(&mut rx_o_c2);
        let res2_share1s: Vec<Vec<u128>> = bincode::deserialize(&bytes).unwrap();

        let res_annos: Vec<Vec<u128>> = res2_share2s
            .into_iter()
            .zip(res2_share1s.into_iter())
            .map(|(res2_share2, res2_share1)| combine_share(res2_share2, res2_share1))
            .collect();

        for res_anno in res_annos {
            // keep non-zero-anno tuples from c
            let mut col_c_name = vec![];
            let mut col_c_custkey = vec![];
            let mut col_c_nationkey = vec![];
            let mut col_c_anno = vec![];
            for i in 0..res_anno.len() {
                if res_anno[i] != 0 {
                    col_c_name.push(c_name[i]);
                    col_c_custkey.push(c_custkey[i]);
                    col_c_nationkey.push(c_nationkey[i]);
                    col_c_anno.push(res_anno[i] as u32);
                }
            }

            // the clean result relation
            let res_relation =
                Relation::new(vec![col_c_custkey, col_c_name, col_c_nationkey, col_c_anno]);
            println!("{:?}", res_relation);
            break;
        }
    });
    });

    thread_l.join().unwrap();
    thread_o.join().unwrap();
    thread_c.join().unwrap();
    let t = timer.elapsed().real.as_micros() as u64;
    println!("query processing time: {} ms", t / 1000);
    let intra_comm = crate::INTRA_SHARD_COMM.lock().unwrap();
    let cross_comm = crate::CROSS_SHARD_COMM.lock().unwrap();
    let consen_num = crate::CONSENSUS_NUM.lock().unwrap();
    crate::tpch::show_comm_cost(*intra_comm, *cross_comm, *consen_num);
}

pub fn exe_q10_single(path: &Path, chunk_size: usize, process_id: u16, debug: bool, intra: bool) {
    println!("loading dataset...");

    let ((customer, c_anno), (orders, o_anno), (lineitem, l_anno)) =
        load_q10_tables(path, chunk_size);
    let c_custkey = customer.get_col(0);
    let c_name = customer.get_col(1);
    let c_nationkey = customer.get_col(2);
    let o_orderkey = orders.get_col(0);
    let o_custkey = orders.get_col(1);
    let mut l_orderkey = lineitem.get_col(0);

    let out_len_1st = o_anno.len();
    let out_len_2nd = c_anno.len();

    let ys_len_larger_1st = o_anno.len() > l_anno.len();
    let ys_len_larger_2nd = c_anno.len() > o_anno.len();

    let triples = load_beaver_truples();
    let (a1_1st, a2_1st, b1_1st, b2_1st, c1_1st, c2_1st) =
        obtain_beaver_tripes_by(out_len_1st, triples.clone());
    let (a1_2nd, a2_2nd, b1_2nd, b2_2nd, c1_2nd, c2_2nd) =
        obtain_beaver_tripes_by(out_len_2nd, triples);

    println!("loading pre-computed information...");
    let bytes = read_q10_pre_compute_info(path);
    let mut pre_infos: Vec<PreInfo> = Vec::<PreInfo>::deserialize_uncompressed(&*bytes).unwrap();
    // order matters
    let pre_info_2 = pre_infos.remove(1);
    let xs_info_2 = pre_info_2.xs_info;
    let veri_info_2 = pre_info_2.veri_info;
    let z_commit_2 = pre_info_2.z_commit;
    let pre_info_1 = pre_infos.remove(0);
    let xs_info_1 = pre_info_1.xs_info;
    let veri_info_1 = pre_info_1.veri_info;
    let z_commit_1 = pre_info_1.z_commit;

    // pre-compute sub_product trees
    println!("pre-computing some info...");
    let ys_pts_1st = points_from_num(o_orderkey.clone());
    let ys_tree_first = SubProductTree::new_from_points_parallel(&ys_pts_1st);
    let ys_pts_2nd = points_from_num(c_custkey.clone());
    let ys_tree_2nd = SubProductTree::new_from_points_parallel(&ys_pts_2nd);

    // setup
    println!("doing setup...");
    let (sen_streams_1st, rec_streams_1st) = obtain_unix_streams(THREAD_NUM);
    let (sen_streams_2nd, rec_streams_2nd) = obtain_unix_streams(THREAD_NUM);
    let (sen_streams_2nd_oep, rec_streams_2nd_oep) = obtain_unix_streams(THREAD_NUM);

    let mut rng = get_fixed_rng();
    let secret = Fr::rand(&mut rng);
    let n_1st_psi = l_orderkey.len();
    let max_deg_1st = n_1st_psi - 1;
    let n_2nd_psi = o_custkey.len();
    let max_deg_2nd = n_2nd_psi - 1;

    // thread_l
    let mut kzg_l_1st = setup_kzg(max_deg_1st);
    kzg_l_1st.setup(secret);
    // thread_o
    let mut kzg_o_1st = setup_kzg(max_deg_1st);
    kzg_o_1st.setup(secret);
    let mut kzg_o_2nd = setup_kzg(max_deg_2nd);
    kzg_o_2nd.setup(secret);
    // thread_c
    let mut kzg_c_2nd = setup_kzg(max_deg_2nd);
    kzg_c_2nd.setup(secret);

    
    let (mut stream_l_o, mut stream_o_l) = UnixStream::pair().unwrap();
    // IMPORTANT: should not re-use stream_l_o for obliAgg, because stream_l_o has been updated (mut ref), while obliAgg requires immutable ref
    let (mut stream_l_o2, mut stream_o_l2) = UnixStream::pair().unwrap();
    let (mut stream_o_c, mut stream_c_o) = UnixStream::pair().unwrap();
    let (mut tx_o_l, mut rx_o_l) = UnixStream::pair().unwrap();
    let (mut tx_o_l2, mut rx_o_l2) = UnixStream::pair().unwrap();
    let (mut tx_o_c, mut rx_o_c) = UnixStream::pair().unwrap();
    let (mut tx_o_c2, mut rx_o_c2) = UnixStream::pair().unwrap();
    let (mut tx_l_o, mut rx_l_o) = UnixStream::pair().unwrap();

    let (mut tx_l_o2, mut rx_l_o2) = UnixStream::pair().unwrap();
    let (mut tx_l_c, mut rx_l_c) = UnixStream::pair().unwrap();
    let (mut tx_c_o, mut rx_c_o) = UnixStream::pair().unwrap();

    let timer = howlong::ProcessCPUTimer::new();
    let thread_l = std::thread::spawn(move || {
        let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
        pool.install(|| {
        let self_id = process_id;

        //### step 1: O.semijoin(L), L as sender
        let mut rng = get_fixed_rng();
        println!("thread l: first PSI...");
        // lineitem local group by
        let (l_anno_sorted, _) = Relation::local_add_agg(&mut l_orderkey, &l_anno, &mut rng);
        let xs_pts = points_from_num(l_orderkey.clone());
        let xs_tree = SubProductTree::new_from_points_parallel(&xs_pts);

        let share1_first = if intra {
            intra_psi_anno_sender_parallel(
                l_orderkey.into_iter().map(|x| x as u64).collect(),
                l_anno_sorted.into_iter().map(|x| x as u64).collect(),
                &kzg_l_1st,
                &mut stream_l_o,
                &xs_info_1,
                &xs_tree,
                debug,
                self_id,
                0,
                ys_len_larger_1st,
                out_len_1st,
                sen_streams_1st,
            )
        } else {
            basic_psi_anno_sender_parallel(
                l_orderkey.into_iter().map(|x| x as u64).collect(),
                l_anno_sorted.into_iter().map(|x| x as u64).collect(),
                &xs_tree,
                &mut stream_l_o,
                out_len_1st,
                self_id,
                debug,
                ys_len_larger_1st,
                sen_streams_1st,
            )
        };

        // consensus on share1_first before sending to thread_c
        let bytes = bincode::serialize(&share1_first).unwrap();
        let dig = digest(Algorithm::SHA256, &bytes);
        if !debug {
            run_consensus(dig, self_id);
        }
        println!("consensus for share1_first");

        // receive o_anno_1 from o
        let bytes = receive_data_by_stream(&mut rx_o_l);
        let o_anno_1: Vec<u128> = bincode::deserialize(&bytes).unwrap();

        // do vec mul using beaver triple
        let res1_share1 = vec_mul_1(
            &o_anno_1,
            &share1_first,
            &a1_1st,
            &b1_1st,
            &c1_1st,
            &mut stream_l_o,
        );

        let res1_anno1 = sen_u128_to_u32(res1_share1, &mut rx_o_l, &mut tx_l_o);

        let sorted_anno1 = sender_permute(&mut stream_l_o, &res1_anno1);

        let agg_add_res2 = ev_agg_entire(
            &sorted_anno1.iter().map(|x| *x as u128).collect(),
            &mut stream_l_o2,
            AggType::Add,
        );

        // step1 finished
        let agg_add_res2 = rec_u128_to_u32(agg_add_res2, &mut tx_l_o2, &mut rx_o_l2);
        // send agg_or_res2 to thread_c
        let bytes = bincode::serialize(&agg_add_res2).unwrap();
        send_data_by_stream(&mut tx_l_c, &bytes, false);
        // finish for thread_l
    });
    });

    let thread_o = std::thread::spawn(move || {
        let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
        pool.install(|| {
        let self_id = process_id + N * 1;

        //### step 1: O.semijoin(L), O as receiver
        println!("thread o: first PSI...");
        // first PSI: orders as receiver
        let share2_first = if intra {
            intra_psi_anno_receiver_parallel(
                &o_orderkey,
                false,
                o_orderkey.clone().into_iter().map(|x| x as u64).collect(),
                &kzg_o_1st,
                &mut stream_o_l,
                &ys_tree_first,
                &vec![veri_info_1],
                vec![z_commit_1],
                self_id,
                0,
                ys_len_larger_1st,
                debug,
                false,
                rec_streams_1st,
            )
        } else {
            basic_psi_anno_receiver_parallel(
                o_orderkey.clone().into_iter().map(|x| x as u64).collect(),
                &mut stream_o_l,
                &ys_tree_first,
                self_id,
                debug,
                ys_len_larger_1st,
                rec_streams_1st,
            )
        };

        // consensus on share2_first before sending to thread_c
        let bytes = bincode::serialize(&share2_first).unwrap();
        let dig = digest(Algorithm::SHA256, &bytes);
        if !debug {
            run_consensus(dig, self_id);
        }
        println!("consensus for share2_first");

        let (o_anno_1, o_anno_2) = gen_shared_anno(o_anno.into_iter().map(|x| x as u128).collect());
        let bytes = bincode::serialize(&o_anno_1).unwrap();
        send_data_by_stream(&mut tx_o_l, &bytes, false);

        let res1_share2 = vec_mul_2(
            &o_anno_2,
            &share2_first,
            &a2_1st,
            &b2_1st,
            &c2_1st,
            &mut stream_o_l,
        );

        // convert u128 share to u32 share (for later OP)
        let res1_anno2 = rec_u128_to_u32(res1_share2, &mut tx_o_l, &mut rx_l_o);

        // get sort pmt & sort key, use OP to sort shared anno (u32 share)
        let sort_pmt = get_sort_pmt(&o_custkey);
        let sorted_o_custkey = sort_by_pmt(&o_custkey, &sort_pmt);
        // let sorted_o_orderkey = sort_by_pmt(&o_orderkey, &sort_pmt);
        let sorted_anno2 = permutor_permute(&mut stream_o_l, &sort_pmt, &res1_anno2);

        // circuit to do oblivious add_agg
        let ind = get_ind(&sorted_o_custkey);
        let agg_add_res1 = gen_random::<u128>(out_len_1st);
        gb_agg_entire(
            &ind,
            &sorted_anno2.iter().map(|v| *v as u128).collect(),
            &mut stream_o_l2,
            AggType::Add,
            &agg_add_res1,
        );
        let dummyed_o_custkey = local_group_by_with_dummy(&sorted_o_custkey);

        //### step2: C.semijoin(O), O as sender
        println!("thread o: second PSI...");
        // second psi, o is sender

        let agg_add_res1 = sen_u128_to_u32(agg_add_res1, &mut rx_l_o2, &mut tx_o_l2);

        let xs_pts = points_from_num(dummyed_o_custkey.clone());
        let xs_tree = SubProductTree::new_from_points_parallel(&xs_pts);

        let share1_second = if intra {
            intra_psi_shared_anno_sender_parallel(
                dummyed_o_custkey.into_iter().map(|v| v as u64).collect(),
                agg_add_res1,
                &kzg_o_2nd,
                &xs_tree,
                &xs_info_2,
                out_len_2nd,
                chunk_size,
                &mut stream_o_c,
                self_id,
                1,
                debug,
                ys_len_larger_2nd,
                sen_streams_2nd,
                sen_streams_2nd_oep,
            )
        } else {
            basic_psi_shared_anno_sender_parallel(
                dummyed_o_custkey.into_iter().map(|v| v as u64).collect(),
                agg_add_res1,
                &xs_tree,
                out_len_2nd,
                chunk_size,
                &mut stream_o_c,
                self_id,
                debug,
                ys_len_larger_2nd,
                sen_streams_2nd,
                sen_streams_2nd_oep,
            )
        };

        // col_mul using beaver_triple
        let bytes = receive_data_by_stream(&mut rx_c_o);
        let c_anno1: Vec<u128> = bincode::deserialize(&bytes).unwrap();
        let share1_second = rec_u32_to_u128(share1_second, &mut tx_o_c, &mut rx_c_o);

        let res2_share1 = vec_mul_1(
            &c_anno1,
            &share1_second,
            &a1_2nd,
            &b1_2nd,
            &c1_2nd,
            &mut stream_o_c,
        );

        // reveal res2_share1 to thread_c
        let bytes = bincode::serialize(&res2_share1).unwrap();
        send_data_by_stream(&mut tx_o_c2, &bytes, false);
        // thread_o finish
    });
    });

    let thread_c = std::thread::spawn(move || {
        let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
        pool.install(|| {
        let self_id = process_id + N * 2;
        //### step2: C.semijoin(O), C as receiver
        println!("thread l: second PSI...");
        let bytes = receive_data_by_stream(&mut rx_l_c);
        let agg_add_res2: Vec<u32> = bincode::deserialize(&bytes).unwrap();
        // let sorted_anno1 = rx_l_c.recv().unwrap();
        // c_custkey is originally sorted
        let share2_second = if intra {
            intra_psi_shared_anno_receiver_parallel(
                &c_custkey,
                false,
                c_custkey.clone().into_iter().map(|x| x as u64).collect(),
                &kzg_c_2nd,
                &ys_tree_2nd,
                &vec![veri_info_2],
                vec![z_commit_2],
                agg_add_res2,
                &mut stream_c_o,
                chunk_size,
                self_id,
                1,
                debug,
                ys_len_larger_2nd,
                rec_streams_2nd,
                rec_streams_2nd_oep,
            )
        } else {
            basic_psi_shared_anno_receiver_parallel(
                c_custkey.clone().into_iter().map(|x| x as u64).collect(),
                &ys_tree_2nd,
                agg_add_res2,
                &mut stream_c_o,
                chunk_size,
                self_id,
                debug,
                ys_len_larger_2nd,
                rec_streams_2nd,
                rec_streams_2nd_oep,
            )
        };

        let (c_anno_1, c_anno_2) = gen_shared_anno(c_anno.into_iter().map(|x| x as u128).collect());
        let bytes = bincode::serialize(&c_anno_1).unwrap();
        send_data_by_stream(&mut tx_c_o, &bytes, false);

        let share2_second = sen_u32_to_u128(share2_second, &mut rx_o_c, &mut tx_c_o);

        let res2_share2 = vec_mul_2(
            &c_anno_2,
            &share2_second,
            &a2_2nd,
            &b2_2nd,
            &c2_2nd,
            &mut stream_c_o,
        );

        // get revealed anno for c
        let bytes = receive_data_by_stream(&mut rx_o_c2);
        let res2_share1: Vec<u128> = bincode::deserialize(&bytes).unwrap();
        let res_anno = combine_share(res2_share2, res2_share1);
        // keep non-zero-anno tuples from c
        let mut col_c_name = vec![];
        let mut col_c_custkey = vec![];
        let mut col_c_nationkey = vec![];
        let mut col_c_anno = vec![];
        for i in 0..res_anno.len() {
            if res_anno[i] != 0 {
                col_c_name.push(c_name[i]);
                col_c_custkey.push(c_custkey[i]);
                col_c_nationkey.push(c_nationkey[i]);
                col_c_anno.push(res_anno[i] as u32);
            }
        }

        // the clean result relation
        let res_relation =
            Relation::new(vec![col_c_custkey, col_c_name, col_c_nationkey, col_c_anno]);
        println!("{:?}", res_relation);
    });
    });

    thread_l.join().unwrap();
    thread_o.join().unwrap();
    thread_c.join().unwrap();
    let t = timer.elapsed().real.as_micros() as u64;
    println!("query processing time: {} ms", t / 1000);
    let intra_comm = crate::INTRA_SHARD_COMM.lock().unwrap();
    let cross_comm = crate::CROSS_SHARD_COMM.lock().unwrap();
    let consen_num = crate::CONSENSUS_NUM.lock().unwrap();
    crate::tpch::show_comm_cost(*intra_comm, *cross_comm, *consen_num);
}
