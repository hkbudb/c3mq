use std::fs::File;
use std::io::{self, BufRead, Write};
use std::os::unix::net::UnixStream;
use std::path::Path;

use ark_bls12_381::{Bls12_381, Fr};
use ark_ec::pairing::Pairing;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use crypto_hash::{digest, Algorithm};
use rayon::ThreadPoolBuilder;

use crate::psi::subproduct_tree::SubProductTree;
use crate::psi::utils::{
    load_beaver_truples, obtain_beaver_tripes_by, receive_data_by_stream, send_data_by_stream,
    vec_mul_1, vec_mul_2,
};
use crate::{psi::*, THREAD_NUM};
use crate::relation::{remove_duplicate, Relation};
use crate::tpch::utils::split_vec_evenly;
use crate::tpch::{PRE_INFO, PRE_INFO_PARTITION};
use crate::utils::{
    combine_share, get_fixed_rng, obtain_unix_streams, points_from_num, run_consensus
};
use crate::N;

// e.g., path: ./data/1MB
pub fn load_q3_tables(
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
    let mut c_anno = vec![];

    for line in lines {
        let line = line.unwrap();
        let fields: Vec<&str> = line.split('|').collect();
        c_custkey.push(fields[0].parse::<u32>().unwrap());
        c_anno.push(fields[8].parse::<u32>().unwrap());
    }

    let customer = Relation::new(vec![c_custkey]);

    // orders
    let f_orders = File::open(&orders_path).unwrap();
    let reader = io::BufReader::new(f_orders);
    let lines = reader.lines().skip(2);
    let mut o_orderkey = vec![];
    let mut o_customerkey = vec![];
    let mut o_orderdate = vec![];
    let mut o_shippriority = vec![];

    let mut o_anno = vec![];

    for line in lines {
        let line = line.unwrap();
        let fields: Vec<&str> = line.split('|').collect();
        o_orderkey.push(fields[0].parse::<u32>().unwrap());
        o_customerkey.push(fields[1].parse::<u32>().unwrap());
        let date_info: Vec<&str> = fields[4].split('-').collect();
        let date_num = date_info[0].parse::<u32>().unwrap() * 10000
            + date_info[1].parse::<u32>().unwrap() * 100
            + date_info[2].parse::<u32>().unwrap();
        o_orderdate.push(date_num);
        o_shippriority.push(fields[7].parse::<u32>().unwrap());
        o_anno.push(fields[9].parse::<u32>().unwrap());
    }

    let mut orders = Relation::new(vec![o_orderkey, o_customerkey, o_orderdate, o_shippriority]);
    let pruned_size = orders.get_size() % chunk_size;
    orders.prune(pruned_size);
    o_anno.truncate(o_anno.len() - pruned_size);

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
        l_anno.push(fields[16].parse::<u32>().unwrap());
    }

    let lineitem = Relation::new(vec![l_orderkey]);

    ((customer, c_anno), (orders, o_anno), (lineitem, l_anno))
}


#[derive(CanonicalSerialize, CanonicalDeserialize)]
struct PreInfo {
    xs_info1: Vec<<Bls12_381 as Pairing>::G1Affine>,
    veri_info1: Vec<<Bls12_381 as Pairing>::G1Affine>,
    z_commit1: ark_ec::short_weierstrass::Affine<ark_bls12_381::g2::Config>,
    xs_info2: Vec<<Bls12_381 as Pairing>::G1Affine>,
    veri_info2: Vec<<Bls12_381 as Pairing>::G1Affine>,
    z_commit2: ark_ec::short_weierstrass::Affine<ark_bls12_381::g2::Config>,
}

#[derive(CanonicalSerialize, CanonicalDeserialize)]
struct PreInfoPartition {
    xs_info1: Vec<<Bls12_381 as Pairing>::G1Affine>,
    veri_info1: Vec<Vec<<Bls12_381 as Pairing>::G1Affine>>,
    z_commit1: Vec<ark_ec::short_weierstrass::Affine<ark_bls12_381::g2::Config>>,
    xs_info2: Vec<<Bls12_381 as Pairing>::G1Affine>,
    veri_info2: Vec<Vec<<Bls12_381 as Pairing>::G1Affine>>,
    z_commit2: Vec<ark_ec::short_weierstrass::Affine<ark_bls12_381::g2::Config>>,
}

pub fn wirte_q3_pre_compute_info(
    path: &Path,
    secret: <Bls12_381 as Pairing>::ScalarField,
    chunk_size: usize,
) {
    let ((customer, _c_anno), (orders, _o_anno), (lineitem, l_anno)) =
        load_q3_tables(path, chunk_size);

    // first psi
    let mut xs = lineitem.get_col(0); // l_orderkey
    let ys = orders.get_col(0); // o_orderkey

    // local group by for lineitem
    let mut rng = get_fixed_rng();
    let _l_anno_sorted = Relation::local_add_agg(&mut xs, &l_anno, &mut rng);

    let n_first_psi = lineitem.get_size();
    let max_deg = n_first_psi - 1;
    let mut kzg1 = setup_kzg(max_deg);
    let mut kzg2 = setup_kzg(max_deg);
    kzg1.setup(secret);
    kzg2.setup(secret);

    // because ys has no duplicate, no need to remove duplicate
    let xs_pts = points_from_num(xs.clone());
    let xs_info = kzg1.pre_compute_g1(&xs_pts, secret);
    // for unpartitioned data
    let ys_pts = points_from_num(ys.clone());
    let veri_info = kzg2.pre_compute_g1(&ys_pts, secret);
    let z_commit = kzg2.pre_compute_z_commitment(&ys_pts, secret);
    // for partitioned data
    let ys_partitioned = split_vec_evenly(&ys);
    let mut veri_infos = vec![];
    let mut z_commits = vec![];
    for ys in ys_partitioned {
        let ys_pts = points_from_num(ys);
        let veri_info = kzg2.pre_compute_g1(&ys_pts, secret);
        let z_commit = kzg2.pre_compute_z_commitment(&ys_pts, secret);
        veri_infos.push(veri_info);
        z_commits.push(z_commit);
    }

    // second psi
    let xs = customer.get_col(0); // c_custkey
    let ys = orders.get_col(1); // o_custkey

    // no need to do local group by for c_custkey
    // let mut rng = get_fixed_rng();
    // let _c_anno_sorted = Relation::local_add_agg(&mut xs, &c_anno, &mut rng);

    let n_second_psi = customer.get_size();
    let max_deg = n_second_psi - 1;
    let mut kzg1 = setup_kzg(max_deg);
    let mut kzg2 = setup_kzg(max_deg);
    kzg1.setup(secret);
    kzg2.setup(secret);

    // remove duplicate in ys
    let ys: Vec<u32> = remove_duplicate(&ys);

    let xs_pts = points_from_num(xs.clone());
    let xs_info2 = kzg1.pre_compute_g1(&xs_pts, secret);
    // for unpartitioned data
    let ys_pts = points_from_num(ys.clone());
    let veri_info2 = kzg2.pre_compute_g1(&ys_pts, secret);
    let z_commit2 = kzg2.pre_compute_z_commitment(&ys_pts, secret);
    // for partitioned data
    let ys_partitioned2 = split_vec_evenly(&ys);
    let mut veri_infos2 = vec![];
    let mut z_commits2 = vec![];
    for ys in ys_partitioned2 {
        let ys_pts = points_from_num(ys);
        let veri_info2 = kzg2.pre_compute_g1(&ys_pts, secret);
        let z_commit2 = kzg2.pre_compute_z_commitment(&ys_pts, secret);
        veri_infos2.push(veri_info2);
        z_commits2.push(z_commit2);
    }

    // write to file
    let data = PreInfo {
        xs_info1: xs_info.clone(),
        veri_info1: veri_info,
        z_commit1: z_commit,
        xs_info2: xs_info2.clone(),
        veri_info2: veri_info2,
        z_commit2: z_commit2,
    };

    let mut data_bytes: Vec<u8> = vec![];
    data.serialize_uncompressed(&mut data_bytes).unwrap();

    println!("writing pre-computed info to files...");
    let dir_path = path.join("q3");
    if !std::fs::metadata(dir_path.clone()).is_ok() {
        std::fs::create_dir(dir_path.clone()).unwrap();
    }
    let file_path = dir_path.join(PRE_INFO);
    if std::fs::metadata(file_path.clone()).is_ok() {
        std::fs::remove_file(&file_path).unwrap();
    }

    let mut file = File::create(&file_path).unwrap();
    file.write_all(&data_bytes).unwrap();

    // for partitioned data
    let data = PreInfoPartition {
        xs_info1: xs_info,
        veri_info1: veri_infos,
        z_commit1: z_commits,
        xs_info2: xs_info2,
        veri_info2: veri_infos2,
        z_commit2: z_commits2,
    };

    let mut data_bytes: Vec<u8> = vec![];
    data.serialize_uncompressed(&mut data_bytes).unwrap();

    println!("writing pre-computed info to files...");
    let dir_path = path.join("q3");
    if !std::fs::metadata(dir_path.clone()).is_ok() {
        std::fs::create_dir(dir_path.clone()).unwrap();
    }
    let file_path = dir_path.join(PRE_INFO_PARTITION);
    if std::fs::metadata(file_path.clone()).is_ok() {
        std::fs::remove_file(&file_path).unwrap();
    }

    let mut file = File::create(&file_path).unwrap();
    file.write_all(&data_bytes).unwrap();

    println!("finished");
}

pub(crate) fn read_q3_pre_compute_info(path: &Path, is_partitioned: bool) -> Vec<u8> {
    let file_path = if is_partitioned {
        path.join("q3").join(PRE_INFO_PARTITION)
    } else {
        path.join("q3").join(PRE_INFO)
    };

    let mut file = File::open(file_path).unwrap();
    let mut buffer = Vec::new();
    io::Read::read_to_end(&mut file, &mut buffer).unwrap();
    buffer
}

// the lib supports different queries, but for ease of implementing, here we just use the same query repeatedly
pub fn exe_q3_batch(
    path: &Path,
    chunk_size: usize,
    query_num: usize,
    process_id: u16,
    debug: bool,
) {
    println!("loading dataset...");
    let ((customer, c_anno), (orders, o_anno), (lineitem, l_anno)) =
        load_q3_tables(path, chunk_size);

    let mut l_orderkey = lineitem.get_col(0);
    let o_orderkey = orders.get_col(0);
    let c_custkey = customer.get_col(0);
    let o_custkey = orders.get_col(1);

    let ys_second_no_dup = remove_duplicate(&o_custkey);
    let out_len_1st = orders.get_size();
    let out_len_2nd = out_len_1st;

    let ys_len_larger_1st = orders.get_size() > lineitem.get_size();
    let ys_len_larger_2nd = orders.get_size() > customer.get_size();
    let triples = load_beaver_truples();
    let (a1, a2, b1, b2, c1, c2) = obtain_beaver_tripes_by(out_len_1st, triples);

    // load pre_info for q3
    println!("loading pre-computed information...");
    let bytes = read_q3_pre_compute_info(path, false);
    let pre_info: PreInfo = PreInfo::deserialize_uncompressed(&*bytes).unwrap();
    let xs_info_1st = pre_info.xs_info1;
    let xs_info_2nd = pre_info.xs_info2;
    let veri_info_1st = pre_info.veri_info1;
    let veri_info_2nd = pre_info.veri_info2;
    let z_commit_1st = pre_info.z_commit1;
    let z_commit_2nd = pre_info.z_commit2;

    // pre-compute subproduct_tree
    let ys_pts_1st = points_from_num(o_orderkey.clone());
    let ys_tree_1st = SubProductTree::new_from_points_parallel(&ys_pts_1st);
    let ys_pts_2nd = points_from_num(ys_second_no_dup.clone());
    let ys_tree_2nd = SubProductTree::new_from_points_parallel(&ys_pts_2nd);

    // setup
    println!("doing setup...");
    let (sen_streams_1st, rec_streams_1st) = obtain_unix_streams(THREAD_NUM);
    let (sen_streams_2nd, rec_streams_2nd) = obtain_unix_streams(THREAD_NUM);

    let mut rng = get_fixed_rng();
    let secret = Fr::rand(&mut rng);
    let n_1st_psi = lineitem.get_size();
    let max_deg_1st = n_1st_psi - 1;
    let n_2nd_psi = customer.get_size();
    let max_deg_2nd = n_2nd_psi - 1;
    let mut kzg_l = setup_kzg(max_deg_1st);
    kzg_l.setup(secret);
    let mut kzg_c = setup_kzg(max_deg_1st);
    kzg_c.setup(secret);
    let mut kzg_o_l = setup_kzg(max_deg_1st);
    kzg_o_l.setup(secret);
    let mut kzg_o_c = setup_kzg(max_deg_2nd);
    kzg_o_c.setup(secret);

    // first PSI: sender: lineitem, receiver: orders
    let (mut stream_l_o, mut stream_o_l) = UnixStream::pair().unwrap();
    // second PSI: sender: customer, receiver: orders
    let (mut stream_c_o, mut stream_o_c) = UnixStream::pair().unwrap();
    let (mut tx_l, mut rx_l) = UnixStream::pair().unwrap();
    let (mut tx_c, mut rx_c) = UnixStream::pair().unwrap();

    let timer = howlong::ProcessCPUTimer::new();

    let thread_l = std::thread::spawn(move || {
        let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
        pool.install(|| {
        let self_id = process_id;
        let mut rng = get_fixed_rng();
        println!("thread l: first PSI...");
        // first PSI: lineitem local group by
        let (l_anno_sorted, _) = Relation::local_add_agg(&mut l_orderkey, &l_anno, &mut rng);
        let xs_pts = points_from_num(l_orderkey.clone());
        let xs_tree = SubProductTree::new_from_points_parallel(&xs_pts);
        let share1s_first = batch_psi_anno_sender_parallel(
            vec![l_orderkey.into_iter().map(|x| x as u64).collect(); query_num],
            vec![l_anno_sorted.into_iter().map(|x| x as u64).collect(); query_num],
            &kzg_l,
            &mut stream_l_o,
            &vec![xs_info_1st; query_num],
            &vec![xs_tree; query_num],
            debug,
            self_id,
            ys_len_larger_1st,
            out_len_1st,
            sen_streams_1st,
        );
        println!("thread_l: finish first psi for process {}", self_id);
        // consensus on share1_first before sending to thread_c
        let bytes = bincode::serialize(&share1s_first).unwrap();
        let dig = digest(Algorithm::SHA256, &bytes);
        if !debug {
            run_consensus(dig, self_id);
        }
        let bytes = bincode::serialize(&share1s_first).unwrap();
        send_data_by_stream(&mut tx_l, &bytes, false);
    });
    });

    let thread_c = std::thread::spawn(move || {
        let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
        pool.install(|| {
        let self_id = process_id + N * 2;

        println!("thread c: second PSI...");
        // second PSI: customer does not need local group by
        // cannot pre-compute as xs_second was updated in local group by
        let xs_pts = points_from_num(c_custkey.clone());
        let xs_tree = SubProductTree::new_from_points_parallel(&xs_pts);

        let share1s_second = batch_psi_anno_sender_parallel(
            vec![c_custkey.into_iter().map(|x| x as u64).collect(); query_num],
            vec![c_anno.into_iter().map(|x| x as u64).collect(); query_num],
            &kzg_c,
            &mut stream_c_o,
            &vec![xs_info_2nd; query_num],
            &vec![xs_tree; query_num],
            debug,
            self_id,
            ys_len_larger_2nd,
            out_len_2nd,
            sen_streams_2nd,
        );

        println!("thread c: finish second PSI sender");
        // receive the share from thread_l
        let bytes = receive_data_by_stream(&mut rx_l);
        let share1s_first: Vec<Vec<u128>> = bincode::deserialize(&bytes).unwrap();

        // ready for vec_mul
        // TODO: use HPA here
        let mut z1s = vec![];
        for (share1_first, share1_second) in share1s_first.iter().zip(share1s_second.iter()) {
            z1s.push(vec_mul_1(
                &share1_first,
                &share1_second,
                &a1,
                &b1,
                &c1,
                &mut stream_c_o,
            ));
        }

        let bytes = bincode::serialize(&z1s).unwrap();
        send_data_by_stream(&mut tx_c, &bytes, false);
    });
    });

    let thread_o = std::thread::spawn(move || {
        let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
        pool.install(|| {
        let self_id = process_id + N * 1;

        println!("thread o: first PSI...");
        // first PSI: orders as receiver

        let share2s_first = batch_psi_anno_receiver_parallel(
            &vec![o_orderkey.clone(); query_num],
            false,
            vec![o_orderkey.clone().into_iter().map(|x| x as u64).collect(); query_num],
            &kzg_o_l,
            &mut stream_o_l,
            &vec![ys_tree_1st; query_num],
            &vec![veri_info_1st; query_num],
            vec![z_commit_1st; query_num],
            self_id,
            ys_len_larger_1st,
            debug,
            rec_streams_1st,
        );

        println!("thread o: second PSI...");
        // second PSI: orders as receiver

        let share2s_second = batch_psi_anno_receiver_parallel(
            &vec![o_custkey; query_num],
            true,
            vec![ys_second_no_dup.into_iter().map(|x| x as u64).collect(); query_num],
            &kzg_o_c,
            &mut stream_o_c,
            &vec![ys_tree_2nd; query_num],
            &vec![veri_info_2nd; query_num],
            vec![z_commit_2nd; query_num],
            self_id,
            ys_len_larger_2nd,
            debug,
            rec_streams_2nd,
        );

        // ready for col_opt
        let mut z2s = vec![];
        for (share2_first, share2_second) in share2s_first.iter().zip(share2s_second.iter()) {
            z2s.push(vec_mul_2(
                &share2_first,
                &share2_second,
                &a2,
                &b2,
                &c2,
                &mut stream_o_c,
            ));
        }

        // reveal: as orders has primary key o_orderkey, no need to do aggregation
        let bytes = receive_data_by_stream(&mut rx_c);
        let z1s: Vec<Vec<u128>> = bincode::deserialize(&bytes).unwrap();
        let mut zs = vec![];
        for (z1, z2) in z1s.into_iter().zip(z2s.into_iter()) {
            let z: Vec<u128> = combine_share(z1, z2);
            zs.push(z);
        }

        // TODO: here o_anno should be secret-shared then do vec_mul by beaver triples
        for z in zs {
            let mut res: Vec<u128> = o_anno
                .iter()
                .zip(z.iter())
                .map(|(a, b)| (*a as u128).wrapping_mul(*b))
                .collect();

            // TODO obtain the result table
            res.retain(|x| *x != 0);
            println!("res len: {}", res.len());
            if process_id == 0 {
                println!("{:?}", res);
                break;
            }
        }
    });
    });

    thread_l.join().unwrap();
    thread_c.join().unwrap();
    thread_o.join().unwrap();
    let t = timer.elapsed().real.as_micros() as u64;
    println!(
        "query processing time for {} queries: {} ms",
        query_num,
        t / 1000
    );
    let intra_comm = crate::INTRA_SHARD_COMM.lock().unwrap();
    let cross_comm = crate::CROSS_SHARD_COMM.lock().unwrap();
    let consen_num = crate::CONSENSUS_NUM.lock().unwrap();
    crate::tpch::show_comm_cost(*intra_comm, *cross_comm, *consen_num);
}

pub fn exe_q3_single(path: &Path, chunk_size: usize, process_id: u16, debug: bool, intra: bool) {
    println!("loading dataset...");
    let ((customer, c_anno), (orders, o_anno), (lineitem, l_anno)) =
        load_q3_tables(path, chunk_size);

    let mut l_orderkey = lineitem.get_col(0);
    let o_orderkey = orders.get_col(0);
    let c_custkey = customer.get_col(0);
    let o_custkey = orders.get_col(1);
    let ys_second_no_dup = remove_duplicate(&o_custkey);
    let out_len_1st = orders.get_size();
    let out_len_2nd = out_len_1st;

    let ys_len_larger_1st = orders.get_size() > lineitem.get_size();
    let ys_len_larger_2nd = orders.get_size() > customer.get_size();
    let triples = load_beaver_truples();
    let (a1, a2, b1, b2, c1, c2) = obtain_beaver_tripes_by(out_len_1st, triples);

    // load pre_info for q3
    println!("loading pre-computed information...");
    let bytes = read_q3_pre_compute_info(path, false);
    let (xs_info_1st, xs_info_2nd, veri_infos_1st, veri_infos_2nd, z_commits_1st, z_commits_2nd) = {
        let pre_info: PreInfo = PreInfo::deserialize_uncompressed(&*bytes).unwrap();
        let xs_info_1st = pre_info.xs_info1;
        let xs_info_2nd = pre_info.xs_info2;
        let veri_info_1st = pre_info.veri_info1;
        let veri_info_2nd = pre_info.veri_info2;
        let z_commit_1st = pre_info.z_commit1;
        let z_commit_2nd = pre_info.z_commit2;

        (
            xs_info_1st,
            xs_info_2nd,
            vec![veri_info_1st],
            vec![veri_info_2nd],
            vec![z_commit_1st],
            vec![z_commit_2nd],
        )
    };

    // pre-compute subproduct_tree
    let ys_pts_1st = points_from_num(o_orderkey.clone());
    let ys_tree_1st = SubProductTree::new_from_points_parallel(&ys_pts_1st);
    let ys_pts_2nd = points_from_num(ys_second_no_dup.clone());
    let ys_tree_2nd = SubProductTree::new_from_points_parallel(&ys_pts_2nd);
    // attention: baseline does not need deduplication, should use the tree without deduplication
    let ys_pts_2nd_baseline = points_from_num(o_custkey.clone());
    let ys_tree_2nd_basline = SubProductTree::new_from_points_parallel(&ys_pts_2nd_baseline);

    // setup
    println!("doing setup...");
    let (sen_streams_1st, rec_streams_1st) = obtain_unix_streams(THREAD_NUM);
    let (sen_streams_2nd, rec_streams_2nd) = obtain_unix_streams(THREAD_NUM);

    let mut rng = get_fixed_rng();
    let secret = Fr::rand(&mut rng);
    let n_1st_psi = lineitem.get_size();
    let max_deg_1st = n_1st_psi - 1;
    let n_2nd_psi = customer.get_size();
    let max_deg_2nd = n_2nd_psi - 1;
    // kzg setup is time consuming, but can be done off-line
    let mut kzg_l = setup_kzg(max_deg_1st);
    kzg_l.setup(secret);
    let mut kzg_c = setup_kzg(max_deg_1st);
    kzg_c.setup(secret);
    let mut kzg_o_l = setup_kzg(max_deg_1st);
    kzg_o_l.setup(secret);
    let mut kzgo_c = setup_kzg(max_deg_2nd);
    kzgo_c.setup(secret);

    // first PSI: sender: lineitem, receiver: orders
    let (mut stream_l_o, mut stream_o_l) = UnixStream::pair().unwrap();
    // // second PSI: sender: customer, receiver: orders
    let (mut stream_c_o, mut stream_o_c) = UnixStream::pair().unwrap();
    let (mut tx_l, mut rx_l) = UnixStream::pair().unwrap();
    let (mut tx_c, mut rx_c) = UnixStream::pair().unwrap();

    let timer = howlong::ProcessCPUTimer::new();
    let thread_l = std::thread::spawn(move || {
        let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
        pool.install(|| {
        let self_id = process_id;
        let mut rng = get_fixed_rng();
        // println!("thread l: first PSI...");
        // first PSI: lineitem local group by

        let (l_anno_sorted, _) = Relation::local_add_agg(&mut l_orderkey, &l_anno, &mut rng);
        let xs_pts = points_from_num(l_orderkey.clone());
        let xs_tree = SubProductTree::new_from_points_parallel(&xs_pts);

        let share1_first = if intra {
            intra_psi_anno_sender_parallel(
                l_orderkey.into_iter().map(|x| x as u64).collect(),
                l_anno_sorted.into_iter().map(|x| x as u64).collect(),
                &kzg_l,
                &mut stream_l_o,
                &xs_info_1st,
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
        // println!("thread_l: finish first psi");
        // consensus on share1_first before sending to thread_c
        let bytes = bincode::serialize(&share1_first).unwrap();
        let dig = digest(Algorithm::SHA256, &bytes);
        if !debug {
            run_consensus(dig, self_id);
        }

        let bytes = bincode::serialize(&share1_first).unwrap();

        send_data_by_stream(&mut tx_l, &bytes, false);
    });
    });

    let thread_c = std::thread::spawn(move || {
        let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
        pool.install(|| {
        let self_id = process_id + N * 2;

        // println!("thread c: second PSI...");
        // second PSI: customer does not need local group by
        // cannot pre-compute as xs_second was updated in local group by

        let xs_pts = points_from_num(c_custkey.clone());
        let xs_tree = SubProductTree::new_from_points_parallel(&xs_pts);

        let share1_second = if intra {
            intra_psi_anno_sender_parallel(
                c_custkey.into_iter().map(|x| x as u64).collect(),
                c_anno.into_iter().map(|x| x as u64).collect(),
                &kzg_c,
                &mut stream_c_o,
                &xs_info_2nd,
                &xs_tree,
                debug,
                self_id,
                1,
                ys_len_larger_2nd,
                out_len_2nd,
                sen_streams_2nd,
            )
        } else {
            basic_psi_anno_sender_parallel(
                c_custkey.into_iter().map(|x| x as u64).collect(),
                c_anno.into_iter().map(|x| x as u64).collect(),
                &xs_tree,
                &mut stream_c_o,
                out_len_2nd,
                self_id,
                debug,
                ys_len_larger_2nd,
                sen_streams_2nd,
            )
        };

        // println!("thread c: finish second PSI sender");
        // receive the share from thread_l
        let share1_first_bytes = receive_data_by_stream(&mut rx_l);
        let share1_first: Vec<u128> = bincode::deserialize(&share1_first_bytes).unwrap();

        // ready for vec_mul
        // TODO: use HPA here
        let z1 = vec_mul_1(
            &share1_first,
            &share1_second,
            &a1,
            &b1,
            &c1,
            &mut stream_c_o,
        );

        let bytes = bincode::serialize(&z1).unwrap();
        send_data_by_stream(&mut tx_c, &bytes, false);
    });
    });

    let thread_o = std::thread::spawn(move || {
        let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
        pool.install(|| {
        let self_id = process_id + N * 1;

        // println!("thread o: first PSI...");
        // first PSI: orders as receiver

        let share2_first = if intra {
            intra_psi_anno_receiver_parallel(
                &o_orderkey,
                false,
                o_orderkey.clone().into_iter().map(|x| x as u64).collect(),
                &kzg_o_l,
                &mut stream_o_l,
                // &mut o_streams,
                &ys_tree_1st,
                &veri_infos_1st,
                z_commits_1st,
                self_id,
                0,
                ys_len_larger_1st,
                debug,
                false,
                rec_streams_1st,
            )
        } else {
            basic_psi_anno_receiver_parallel(
                o_orderkey.into_iter().map(|x| x as u64).collect(),
                &mut stream_o_l,
                &ys_tree_1st,
                self_id,
                debug,
                ys_len_larger_1st,
                rec_streams_1st,
            )
        };

        // println!("thread o: second PSI...");
        // second PSI: orders as receiver

        let share2_second = if intra {
            intra_psi_anno_receiver_parallel(
                &o_custkey,
                true,
                ys_second_no_dup.into_iter().map(|x| x as u64).collect(),
                &kzgo_c,
                &mut stream_o_c,
                &ys_tree_2nd,
                &veri_infos_2nd,
                z_commits_2nd,
                self_id,
                1,
                ys_len_larger_2nd,
                debug,
                false,
                rec_streams_2nd,
            )
        } else {
            basic_psi_anno_receiver_parallel(
                o_custkey.into_iter().map(|x| x as u64).collect(),
                &mut stream_o_c,
                &ys_tree_2nd_basline,
                self_id,
                debug,
                ys_len_larger_2nd,
                rec_streams_2nd,
            )
        };

        // ready for col_opt
        let z2 = vec_mul_2(
            &share2_first,
            &share2_second,
            &a2,
            &b2,
            &c2,
            &mut stream_o_c,
        );

        // reveal: as orders has primary key o_orderkey, no need to do aggregation
        let z1_bytes = receive_data_by_stream(&mut rx_c);
        let z1: Vec<u128> = bincode::deserialize(&z1_bytes).unwrap();
        let z: Vec<u128> = combine_share(z1, z2);

        // TODO: here o_anno should be secret-shared then do vec_mul by beaver triples
        let mut res: Vec<u128> = o_anno
            .iter()
            .zip(z.iter())
            .map(|(a, b)| (*a as u128).wrapping_mul(*b))
            .collect();

        // TODO obtain the result table
        res.retain(|x| *x != 0);
        println!("res len: {}", res.len());
        if process_id == 0 {
            println!("{:?}", res);
        }
    });
    });

    thread_l.join().unwrap();
    thread_c.join().unwrap();
    thread_o.join().unwrap();

    let t = timer.elapsed().real.as_micros() as u64;
    println!("### query processing time: {} ms", t / 1000);

    let intra_comm = crate::INTRA_SHARD_COMM.lock().unwrap();
    let cross_comm = crate::CROSS_SHARD_COMM.lock().unwrap();
    let consen_num = crate::CONSENSUS_NUM.lock().unwrap();
    crate::tpch::show_comm_cost(*intra_comm, *cross_comm, *consen_num);
}

mod tests {

    #[test]
    fn test_load_data() {
        use super::*;

        let path = Path::new("./data/1MB");
        let ((customer, c_anno), (orders, _o_anno), (lineitem, _l_anno)) =
            load_q3_tables(path, 100);

        println!("{:?}", orders.get_col(1).len());
        println!("{:?}", lineitem.get_col(0).len());
        println!("{:?}", customer.get_col(0).len());

        let mut xs = customer.get_col(0); // c_custkey
        let ys = orders.get_col(1); // o_custkey
        let mut rng = get_fixed_rng();
        let _c_anno_sorted = Relation::local_add_agg(&mut xs, &c_anno, &mut rng);

        let n_second_psi = customer.get_size();
        println!("{:?}", n_second_psi);
        println!("{:?}", xs);
        println!("{:?}", ys.len());
    }

    #[test]
    fn test_read_write_pre_info() {
        use super::*;
        use ark_bls12_381::Fr;
        use ark_std::UniformRand;

        // let path = Path::new("./data/1MB");
        let path = Path::new("./data/test");

        let mut rng = get_fixed_rng();
        let secret = Fr::rand(&mut rng);
        wirte_q3_pre_compute_info(path, secret, 5);

        // read
        let bytes = read_q3_pre_compute_info(path, false);
        let _pre_info: PreInfo = PreInfo::deserialize_uncompressed(&*bytes).unwrap();
    }

    #[test]
    fn test_digest() {
        let bytes = vec![1; 32];
        let dig = crypto_hash::digest(crypto_hash::Algorithm::MD5, &bytes);
        println!("{}", dig.len());
        let dig = crypto_hash::digest(crypto_hash::Algorithm::SHA256, &bytes);
        println!("{}", dig.len());
    }

    #[test]
    fn test_query() {
        use super::*;

        let path = Path::new("./data/1MB");

        let ((customer, c_anno), (orders, o_anno), (lineitem, l_anno)) = load_q3_tables(path, 100);

        let mut xs_first = lineitem.get_col(0); // l_orderkey
        let ys_first = orders.get_col(0); // o_orderkey
        let xs_second = customer.get_col(0); // c_custkey
        let ys_second = orders.get_col(1); // o_custkey

        let output_size_first = orders.get_size();
        println!("output size: {}", output_size_first);

        let mut rng = get_fixed_rng();
        let (l_anno_sorted, _) = Relation::local_add_agg(&mut xs_first, &l_anno, &mut rng);

        let mut res1 = vec![];
        let mut res2 = vec![];
        for i in 0..output_size_first {
            match xs_first.iter().position(|x| *x == ys_first[i]) {
                Some(j) => {
                    res1.push(l_anno_sorted[j] * o_anno[i]);
                }
                none => {
                    res1.push(0);
                }
            }

            match xs_second.iter().position(|x| *x == ys_second[i]) {
                Some(j) => {
                    res2.push(c_anno[j] * o_anno[i]);
                }
                none => {
                    res2.push(0);
                }
            }
        }
        let mut res1_clone = res1.clone();
        res1_clone.retain(|x| *x != 0);
        println!("{:?}", res1_clone);

        let mut res2_clone = res2.clone();
        res2_clone.retain(|x| *x != 0);
        println!("{:?}", res2_clone.len());

        let mut res: Vec<u32> = res1
            .into_iter()
            .zip(res2.into_iter())
            .zip(o_anno.into_iter())
            .map(|((x, y), z)| x * y * z)
            .collect();
        res.retain(|x| *x != 0);
        println!("{:?}", res);
    }

    #[test]
    fn test_retain() {
        let mut v1 = vec![1, 0, 3, 0, 5];
        let mut v2 = vec![10, 20, 30, 40, 50];
        let mut v3 = vec![11, 21, 31, 41, 51];

        let mut i = 0;
        v1.retain(|&x| {
            let keep = x != 0;
            if keep {
                i += 1;
            } else {
                v2.remove(i);
                v3.remove(i);
            }
            keep
        });

        println!("{:?}", v1);
        println!("{:?}", v2);
        println!("{:?}", v3);
    }
}
