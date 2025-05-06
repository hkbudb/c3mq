use std::{
    fs::File, io::{self, BufRead, Write}, os::unix::net::UnixStream, path::Path
};

use ark_bls12_381::{Bls12_381, Fr};
use ark_ec::pairing::Pairing;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use crypto_hash::{digest, Algorithm};
use rayon::{iter::{
    IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, IntoParallelRefMutIterator, ParallelIterator
}, ThreadPoolBuilder};

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
    relation::{
        get_ind, get_sort_pmt, local_group_by_with_dummy, remove_duplicate, sort_by_pmt, Relation,
    },
    tpch::{
        utils::{
            batch_rec_u128_to_u32, batch_rec_u32_to_u128, batch_sen_u128_to_u32,
            batch_sen_u32_to_u128, gen_shared_anno, rec_u128_to_u32, rec_u32_to_u128, sen_u128_to_u32,
            sen_u32_to_u128,
        },
        PreInfo, PRE_INFO,
    },
    utils::{
        combine_share, gen_random, get_fixed_rng, obtain_unix_streams, points_from_num, run_consensus
    },
    N, THREAD_NUM,
};

// e.g., path: ./data/1MB
pub fn load_q8_tables(
    path: &Path,
    chunk_size: usize,
) -> (
    (Relation, Vec<u32>),
    (Relation, Vec<u32>),
    (Relation, Vec<u32>),
    (Relation, Vec<u32>),
    (Relation, Vec<u32>, Vec<u32>),
) {
    let customer_path = path.join("customer.tbl");
    let orders_path = path.join("orders.tbl");
    let lineitem_path = path.join("lineitem.tbl");
    let part_path = path.join("part.tbl");
    let supplier_path = path.join("supplier.tbl");

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
        c_anno.push(fields[11].parse::<u32>().unwrap());
    }
    let customer = Relation::new(vec![c_custkey]);

    // println!("{:?}", customer);
    // println!("{:?}", c_anno);

    // orders
    let f_orders = File::open(&orders_path).unwrap();
    let reader = io::BufReader::new(f_orders);
    let lines = reader.lines().skip(2);
    let mut o_orderkey = vec![];
    let mut o_custkey = vec![];
    let mut o_year = vec![];
    let mut o_anno = vec![];
    for line in lines {
        let line = line.unwrap();
        let fields: Vec<&str> = line.split('|').collect();
        o_orderkey.push(fields[0].parse::<u32>().unwrap());
        o_custkey.push(fields[1].parse::<u32>().unwrap());
        let date_info: Vec<&str> = fields[4].split('-').collect();
        o_year.push(date_info[0].parse::<u32>().unwrap());
        o_anno.push(fields[13].parse::<u32>().unwrap());
    }

    let mut orders = Relation::new(vec![o_orderkey, o_custkey, o_year]);

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
    let mut l_partkey = vec![];
    let mut l_suppkey = vec![];
    let mut l_anno = vec![];

    for line in lines {
        let line = line.unwrap();
        let fields: Vec<&str> = line.split('|').collect();
        l_orderkey.push(fields[0].parse::<u32>().unwrap());
        l_partkey.push(fields[1].parse::<u32>().unwrap());
        l_suppkey.push(fields[2].parse::<u32>().unwrap());
        l_anno.push(fields[19].parse::<u32>().unwrap());
    }

    let mut lineitem = Relation::new(vec![l_orderkey, l_partkey, l_suppkey]);

    let pruned_size = lineitem.get_size() % chunk_size;
    lineitem.prune(pruned_size);
    l_anno.truncate(l_anno.len() - pruned_size);

    // println!("{:?}", lineitem);
    // println!("{:?}", l_anno);

    // part
    let f_part = File::open(&part_path).unwrap();
    let reader = io::BufReader::new(f_part);
    let lines = reader.lines().skip(2);

    let mut p_partkey = vec![];
    let mut p_anno = vec![];
    for line in lines {
        let line = line.unwrap();
        let fields: Vec<&str> = line.split('|').collect();
        p_partkey.push(fields[0].parse::<u32>().unwrap());
        p_anno.push(fields[9].parse::<u32>().unwrap());
    }

    let part = Relation::new(vec![p_partkey]);
    // println!("{:?}", part);
    // println!("{:?}", p_anno);

    // supplier
    let f_supp = File::open(&supplier_path).unwrap();
    let reader = io::BufReader::new(f_supp);
    let lines = reader.lines().skip(2);

    let mut s_suppkey = vec![];
    let mut s_anno1 = vec![];
    let mut s_anno2 = vec![];

    for line in lines {
        let line = line.unwrap();
        let fields: Vec<&str> = line.split('|').collect();
        s_suppkey.push(fields[0].parse::<u32>().unwrap());
        s_anno1.push(fields[7].parse::<u32>().unwrap());
        s_anno2.push(fields[8].parse::<u32>().unwrap());
    }
    let supplier = Relation::new(vec![s_suppkey]);
    // println!("{:?}", supplier);
    // println!("{:?}", s_anno1);
    // println!("{:?}", s_anno2);

    (
        (customer, c_anno),
        (orders, o_anno),
        (lineitem, l_anno),
        (part, p_anno),
        (supplier, s_anno1, s_anno2),
    )
}

pub fn wirte_q8_pre_compute_info(
    path: &Path,
    secret: <Bls12_381 as Pairing>::ScalarField,
    chunk_size: usize,
) {
    let (
        (customer, _c_anno),
        (orders, _o_anno),
        (lineitem, l_anno),
        (part, _p_anno),
        (supplier, _s_anno1, _s_anno2),
    ) = load_q8_tables(path, chunk_size);

    let mut pre_infos = vec![];
    // first psi
    let c_custkey = customer.get_col(0); // xs
    let o_custkey = orders.get_col(1); // ys
    let n_psi = c_custkey.len();
    let max_deg = n_psi - 1;
    let mut kzg = setup_kzg(max_deg);
    kzg.setup(secret);
    // remove duplicates in ys
    let ys: Vec<u32> = remove_duplicate(&o_custkey);
    let xs_pts = points_from_num(c_custkey);
    let xs_info = kzg.pre_compute_g1(&xs_pts, secret);
    let ys_pts = points_from_num(ys);
    let veri_info = kzg.pre_compute_g1(&ys_pts, secret);
    let z_commit = kzg.pre_compute_z_commitment(&ys_pts, secret);
    let pre_info_1st = PreInfo {
        xs_info: xs_info,
        veri_info: veri_info,
        z_commit: z_commit,
    };
    pre_infos.push(pre_info_1st);

    // second psi
    let p_partkey = part.get_col(0); // xs
    let l_partkey = lineitem.get_col(1); // ys
    let n_psi = p_partkey.len();
    let max_deg = n_psi - 1;
    let mut kzg = setup_kzg(max_deg);
    kzg.setup(secret);
    // remove duplicates in ys
    let ys: Vec<u32> = remove_duplicate(&l_partkey);
    let xs_pts = points_from_num(p_partkey);
    let xs_info = kzg.pre_compute_g1(&xs_pts, secret);
    let ys_pts = points_from_num(ys);
    let veri_info = kzg.pre_compute_g1(&ys_pts, secret);
    let z_commit = kzg.pre_compute_z_commitment(&ys_pts, secret);
    let pre_info_2nd = PreInfo {
        xs_info: xs_info,
        veri_info: veri_info,
        z_commit: z_commit,
    };
    pre_infos.push(pre_info_2nd);

    // third psi
    let s_suppkey = supplier.get_col(0); // xs
    let l_suppkey = lineitem.get_col(2); // ys
    let n_psi = s_suppkey.len();
    let max_deg = n_psi - 1;
    let mut kzg = setup_kzg(max_deg);
    kzg.setup(secret);
    // remove duplicates in ys
    let ys: Vec<u32> = remove_duplicate(&l_suppkey);
    let xs_pts = points_from_num(s_suppkey);
    let xs_info = kzg.pre_compute_g1(&xs_pts, secret);
    let ys_pts = points_from_num(ys);
    let veri_info = kzg.pre_compute_g1(&ys_pts, secret);
    let z_commit = kzg.pre_compute_z_commitment(&ys_pts, secret);
    let pre_info_3rd = PreInfo {
        xs_info: xs_info,
        veri_info: veri_info,
        z_commit: z_commit,
    };
    pre_infos.push(pre_info_3rd);

    // fourth psi
    let mut l_orderkey = lineitem.get_col(0); // xs has duplicate
    let o_orderkey = orders.get_col(0); // ys

    // l_orderkey has duplicate, local group by first
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
    let pre_info_4th = PreInfo {
        xs_info: xs_info,
        veri_info: veri_info,
        z_commit: z_commit,
    };
    pre_infos.push(pre_info_4th);

    let mut data_bytes: Vec<u8> = vec![];
    pre_infos.serialize_uncompressed(&mut data_bytes).unwrap();

    println!("writing pre-computed info to files...");
    let dir_path = path.join("q8");
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

pub(crate) fn read_q8_pre_compute_info(path: &Path) -> Vec<u8> {
    let file_path = path.join("q8").join(PRE_INFO);
    let mut file = File::open(file_path).unwrap();
    let mut buffer = Vec::new();
    io::Read::read_to_end(&mut file, &mut buffer).unwrap();
    buffer
}

/*

select o_year sum(s_anno1*l_anno)/sum(s_anno2*l_anno)
from
  intermediate table
group by o_year

intermediate table:

select s_nationkey, o_year, l_anno
from part, supplier, lineitem, orders, customer
where p_partkey = l_partkey
  and s_suppkey = l_suppkey
  and l_orderkey = o_orderkey
  and o_custkey = c_custkey
  with some range selection

*/

pub fn exe_q8_batch(
    path: &Path,
    chunk_size: usize,
    query_num: usize,
    process_id: u16,
    debug: bool,
) {
    println!("loading dataset...");
    let (
        (customer, c_anno),
        (orders, o_anno),
        (lineitem, l_anno),
        (part, p_anno),
        (supplier, s_anno1, s_anno2),
    ) = load_q8_tables(path, chunk_size);


    let c_custkey = customer.get_col(0); // xs
    let o_custkey = orders.get_col(1); // ys
                                       
    let p_partkey = part.get_col(0); // xs
    let l_partkey = lineitem.get_col(1); // ys
                                         
    let s_suppkey = supplier.get_col(0); // xs
    let l_suppkey = lineitem.get_col(2); // ys
                                         
    let l_orderkey = lineitem.get_col(0); // xs has duplicate
    let o_orderkey = orders.get_col(0); // ys

    let o_year = orders.get_col(2);

    let out_len_1st = o_anno.len();
    let out_len_2nd = l_anno.len();
    let out_len_3rd = out_len_2nd; // 3rd psi will be repeated
    let out_len_4th = out_len_1st; // 4th psi will be repeated

    let triples = load_beaver_truples();
    let (a1_o_len, a2_o_len, b1_o_len, b2_o_len, c1_o_len, c2_o_len) =
        obtain_beaver_tripes_by(out_len_1st, triples.clone());
    let (a1_l_len, a2_l_len, b1_l_len, b2_l_len, c1_l_len, c2_l_len) =
        obtain_beaver_tripes_by(out_len_2nd, triples);

    println!("loading pre-computed information...");
    let bytes = read_q8_pre_compute_info(path);
    let mut pre_infos: Vec<PreInfo> = Vec::<PreInfo>::deserialize_uncompressed(&*bytes).unwrap();
    // order matters
    let pre_info_4 = pre_infos.remove(3);
    let xs_info_4 = pre_info_4.xs_info;
    let veri_info_4 = pre_info_4.veri_info;
    let z_commit_4 = pre_info_4.z_commit;
    let pre_info_3 = pre_infos.remove(2);
    let xs_info_3 = pre_info_3.xs_info;
    let veri_info_3 = pre_info_3.veri_info;
    let z_commit_3 = pre_info_3.z_commit;
    let pre_info_2 = pre_infos.remove(1);
    let xs_info_2 = pre_info_2.xs_info;
    let veri_info_2 = pre_info_2.veri_info;
    let z_commit_2 = pre_info_2.z_commit;
    let pre_info_1 = pre_infos.remove(0);
    let xs_info_1 = pre_info_1.xs_info;
    let veri_info_1 = pre_info_1.veri_info;
    let z_commit_1 = pre_info_1.z_commit;

    println!("pre-computing some info...");
    let ys_1st_no_dup = remove_duplicate(&o_custkey);
    let ys_pts_1st = points_from_num(ys_1st_no_dup.clone());
    let ys_tree_1st = SubProductTree::new_from_points_parallel(&ys_pts_1st);
    let ys_2nd_no_dup = remove_duplicate(&l_partkey);
    let ys_pts_2nd = points_from_num(ys_2nd_no_dup.clone());
    let ys_tree_2nd = SubProductTree::new_from_points_parallel(&ys_pts_2nd);
    let ys_3rd_no_dup = remove_duplicate(&l_suppkey);
    let ys_pts_3rd = points_from_num(ys_3rd_no_dup.clone());
    let ys_tree_3rd = SubProductTree::new_from_points_parallel(&ys_pts_3rd);
    let ys_pts_4th = points_from_num(o_orderkey.clone());
    let ys_tree_4th = SubProductTree::new_from_points_parallel(&ys_pts_4th);

    let ys_len_larger_1st = o_anno.len() > c_anno.len();
    let ys_len_larger_2nd = l_anno.len() > p_anno.len();
    let ys_len_larger_3rd = l_anno.len() > s_anno1.len();
    let ys_len_larger_4th = o_anno.len() > l_anno.len();

    // setup
    println!("doing setup...");
    let (sen_streams_1st, rec_streams_1st) = obtain_unix_streams(THREAD_NUM);
    let (sen_streams_2nd, rec_streams_2nd) = obtain_unix_streams(THREAD_NUM);
    let (sen_streams_3rd, rec_streams_3rd) = obtain_unix_streams(THREAD_NUM);
    let (sen_streams_3rd_b, rec_streams_3rd_b) = obtain_unix_streams(THREAD_NUM);

    let (sen_streams_4th, rec_streams_4th) = obtain_unix_streams(THREAD_NUM);
    let (sen_streams_4th_b, rec_streams_4th_b) = obtain_unix_streams(THREAD_NUM);
    let (sen_streams_4th_oep, rec_streams_4th_oep) = obtain_unix_streams(THREAD_NUM);
    let (sen_streams_4th_oep_b, rec_streams_4th_oep_b) = obtain_unix_streams(THREAD_NUM);

    // TODO: These streams can be reused?
    let (mut stream_1_2_bs, mut stream_2_1_bs) = obtain_unix_streams(THREAD_NUM);
    let (mut stream_1_2_cs, mut stream_2_1_cs) = obtain_unix_streams(THREAD_NUM);
    let (mut stream_1_2_ds, mut stream_2_1_ds) = obtain_unix_streams(THREAD_NUM);
    let (mut stream_1_2_es, mut stream_2_1_es) = obtain_unix_streams(THREAD_NUM);
    let group_size = query_num/THREAD_NUM;

    let mut rng = get_fixed_rng();
    let secret = Fr::rand(&mut rng);
    let n_1st_psi = c_custkey.len();
    let max_deg_1st = n_1st_psi - 1;
    let n_2nd_psi = p_partkey.len();
    let max_deg_2nd = n_2nd_psi - 1;
    let n_3rd_psi = s_suppkey.len();
    let max_deg_3rd = n_3rd_psi - 1;
    let n_4th_psi = l_orderkey.len();
    let max_deg_4th = n_4th_psi - 1;

    // thread_1
    let mut kzg_1_1st = setup_kzg(max_deg_1st);
    kzg_1_1st.setup(secret);
    let mut kzg_1_4th = setup_kzg(max_deg_4th);
    kzg_1_4th.setup(secret);
    // thread_2
    let mut kzg_2_1st = setup_kzg(max_deg_1st);
    kzg_2_1st.setup(secret);
    let mut kzg_2_2nd = setup_kzg(max_deg_2nd);
    kzg_2_2nd.setup(secret);
    let mut kzg_2_3rd = setup_kzg(max_deg_3rd);
    kzg_2_3rd.setup(secret);
    let mut kzg_2_4th = setup_kzg(max_deg_4th);
    kzg_2_4th.setup(secret);

    // thread_3
    let mut kzg_3_2nd = setup_kzg(max_deg_2nd);
    kzg_3_2nd.setup(secret);
    let mut kzg_3_3rd = setup_kzg(max_deg_3rd);
    kzg_3_3rd.setup(secret);

    let (mut stream_1_2, mut stream_2_1) = UnixStream::pair().unwrap();
    let (mut stream_2_3, mut stream_3_2) = UnixStream::pair().unwrap();
    let (mut tx_2_3, mut rx_2_3) = UnixStream::pair().unwrap();
    let (mut tx_3_1, mut rx_3_1) = UnixStream::pair().unwrap();
    let (mut tx_1_2, mut rx_1_2) = UnixStream::pair().unwrap();
    let (mut tx_1_2_b, mut rx_1_2_b) = UnixStream::pair().unwrap();
    let (mut tx_2_1, mut rx_2_1) = UnixStream::pair().unwrap();
    let (mut tx_2_1_b, mut rx_2_1_b) = UnixStream::pair().unwrap();

    let timer = howlong::ProcessCPUTimer::new();
    // thread_1 has: order
    let thread_1 = std::thread::spawn(move || {
        let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
        pool.install(|| {
        let self_id = process_id;
        //### step 1: O.semijoin(C), O as receiver
        // println!("thread 1: first PSI...");

        let res_c_o_s2s = batch_psi_anno_receiver_parallel(
            &vec![o_custkey; query_num],
            true,
            vec![ys_1st_no_dup.into_iter().map(|x| x as u64).collect(); query_num],
            &kzg_1_1st,
            &mut stream_1_2,
            &vec![ys_tree_1st; query_num],
            &vec![veri_info_1; query_num],
            vec![z_commit_1; query_num],
            self_id,
            ys_len_larger_1st,
            debug,
            rec_streams_1st,
        );

        // consensus on res_c_o_s2s
        let bytes = bincode::serialize(&res_c_o_s2s).unwrap();
        let dig = digest(Algorithm::SHA256, &bytes);
        if !debug {
            run_consensus(dig, self_id);
        }

        //### step 4: L.semijoin(O) O is receiver
        let bytes = receive_data_by_stream(&mut rx_3_1);
        let (res_p_s_l_mul_anno1_s1s, res_p_s_l_mul_anno2_s1s): (Vec<Vec<u128>>, Vec<Vec<u128>>) =
            bincode::deserialize(&bytes).unwrap();

        // let (res_p_s_l_mul_anno1_s1s, res_p_s_l_mul_anno2_s1s) = rx_3_1.recv().unwrap();

        // convert u128 share to u32 share
        let res_p_s_l_mul_anno1_s1s =
            batch_rec_u128_to_u32(res_p_s_l_mul_anno1_s1s, &mut tx_1_2, &mut rx_2_1);
        let res_p_s_l_mul_anno2_s1s =
            batch_rec_u128_to_u32(res_p_s_l_mul_anno2_s1s, &mut tx_1_2, &mut rx_2_1);

        let res_p_s_l_mul_anno1_s1s: Vec<Vec<u32>> = res_p_s_l_mul_anno1_s1s
            .iter()
            .map(|res_p_s_l_mul_anno1_s1| sender_permute(&mut stream_1_2, &res_p_s_l_mul_anno1_s1))
            .collect();

        let res_p_s_l_mul_anno2_s1s: Vec<Vec<u32>> = res_p_s_l_mul_anno2_s1s
            .iter()
            .map(|res_p_s_l_mul_anno2_s1| sender_permute(&mut stream_1_2, &res_p_s_l_mul_anno2_s1))
            .collect();

        // corresponding to s_anno1
        let mut agg_add_res1_anno1s = vec![];
        for i in 0..group_size {
            let mut sub_res: Vec<Vec<u128>> = stream_1_2_bs.par_iter_mut().zip(res_p_s_l_mul_anno1_s1s[i*group_size..(i+1)*group_size].into_par_iter()).map(|(stream, data)| {
                ev_agg_entire(
                    &data.iter().map(|x| *x as u128).collect(),
                    stream,
                    AggType::Add,
                )
            }).collect();
            agg_add_res1_anno1s.append(&mut sub_res);
        }

        // corresponding to s_anno2
        let mut agg_add_res1_anno2s = vec![];
        for i in 0..group_size {
            let mut sub_res: Vec<Vec<u128>> = stream_1_2_cs.par_iter_mut().zip(res_p_s_l_mul_anno2_s1s[i*group_size..(i+1)*group_size].into_par_iter()).map(|(stream, data)| {
                ev_agg_entire(
                    &data.iter().map(|x| *x as u128).collect(),
                    stream,
                    AggType::Add,
                )
            }).collect();
            agg_add_res1_anno2s.append(&mut sub_res);
        }

        // convert u128 share to u32 for later psi
        let agg_add_res1_anno1s =
            batch_rec_u128_to_u32(agg_add_res1_anno1s, &mut tx_1_2, &mut rx_2_1);
        let agg_add_res1_anno2s =
            batch_rec_u128_to_u32(agg_add_res1_anno2s, &mut tx_1_2, &mut rx_2_1);

        let res_s2_anno1s = batch_psi_shared_anno_receiver_parallel(
            &vec![o_orderkey.clone(); query_num],
            false,
            vec![o_orderkey.clone().into_iter().map(|x| x as u64).collect(); query_num],
            agg_add_res1_anno1s,
            &kzg_1_4th,
            &mut stream_1_2,
            &vec![ys_tree_4th.clone(); query_num],
            &vec![veri_info_4.clone(); query_num],
            vec![z_commit_4; query_num],
            chunk_size,
            self_id,
            ys_len_larger_4th,
            debug,
            rec_streams_4th,
            rec_streams_4th_oep,
        );

        let res_s2_anno2s = batch_psi_shared_anno_receiver_parallel(
            &vec![o_orderkey.clone(); query_num],
            false,
            vec![o_orderkey.into_iter().map(|x| x as u64).collect(); query_num],
            agg_add_res1_anno2s,
            &kzg_1_4th,
            &mut stream_1_2,
            &vec![ys_tree_4th; query_num],
            &vec![veri_info_4; query_num],
            vec![z_commit_4; query_num],
            chunk_size,
            self_id,
            ys_len_larger_4th,
            debug,
            rec_streams_4th_b,
            rec_streams_4th_oep_b,
        );

        let res_s2_anno1s = batch_sen_u32_to_u128(res_s2_anno1s, &mut rx_2_1, &mut tx_1_2);
        let res_s2_anno2s = batch_sen_u32_to_u128(res_s2_anno2s, &mut rx_2_1, &mut tx_1_2);

        // compute o_anno * res_c_o * res_anno1 and o_anno * res_c_o * res_anno2 using beaver triples
        let final_res_share2_anno1s: Vec<Vec<u128>> = res_c_o_s2s
            .iter()
            .zip(res_s2_anno1s.iter())
            .map(|(res_c_o_s2, res_s2_anno1)| {
                vec_mul_2(
                    res_c_o_s2,
                    res_s2_anno1,
                    &a2_o_len,
                    &b2_o_len,
                    &c2_o_len,
                    &mut stream_1_2,
                )
            })
            .collect();
        let final_res_share2_anno2s: Vec<Vec<u128>> = res_c_o_s2s
            .iter()
            .zip(res_s2_anno2s.iter())
            .map(|(res_c_o_s2, res_s2_anno2)| {
                vec_mul_2(
                    res_c_o_s2,
                    res_s2_anno2,
                    &a2_o_len,
                    &b2_o_len,
                    &c2_o_len,
                    &mut stream_1_2,
                )
            })
            .collect();

        let bytes = receive_data_by_stream(&mut rx_2_1_b);
        let o_anno2s: Vec<Vec<u128>> = bincode::deserialize(&bytes).unwrap();

        let final_res_share2_anno1s: Vec<Vec<u128>> = o_anno2s
            .iter()
            .zip(final_res_share2_anno1s.iter())
            .map(|(o_anno2, final_res_share2_anno1)| {
                vec_mul_2(
                    o_anno2,
                    final_res_share2_anno1,
                    &a2_o_len,
                    &b2_o_len,
                    &c2_o_len,
                    &mut stream_1_2,
                )
            })
            .collect();
        let final_res_share2_anno2s: Vec<Vec<u128>> = o_anno2s
            .iter()
            .zip(final_res_share2_anno2s.iter())
            .map(|(o_anno2, final_res_share2_anno2)| {
                vec_mul_2(
                    o_anno2,
                    final_res_share2_anno2,
                    &a2_o_len,
                    &b2_o_len,
                    &c2_o_len,
                    &mut stream_1_2,
                )
            })
            .collect();
        let final_res_share2_anno1s =
            batch_rec_u128_to_u32(final_res_share2_anno1s, &mut tx_1_2, &mut rx_2_1);
        let final_res_share2_anno2s =
            batch_rec_u128_to_u32(final_res_share2_anno2s, &mut tx_1_2, &mut rx_2_1);

        let final_res_share2_anno1s: Vec<Vec<u32>> = final_res_share2_anno1s
            .iter()
            .map(|final_res_share2_anno1| sender_permute(&mut stream_1_2, &final_res_share2_anno1))
            .collect();

        let final_res_share2_anno2s: Vec<Vec<u32>> = final_res_share2_anno2s
            .iter()
            .map(|final_res_share2_anno2| sender_permute(&mut stream_1_2, &final_res_share2_anno2))
            .collect();

        // run agg_add circuit
        let mut agg_add_res2_anno1s = vec![];
        for i in 0..group_size {
            let mut sub_res: Vec<Vec<u128>> = stream_1_2_ds.par_iter_mut().zip(final_res_share2_anno1s[i*group_size..(i+1)*group_size].into_par_iter()).map(|(stream, data)| {
                ev_agg_entire(
                    &data.iter().map(|x| *x as u128).collect(),
                    stream,
                    AggType::Add,
                )
            }).collect();
            agg_add_res2_anno1s.append(&mut sub_res);
        }

        let mut agg_add_res2_anno2s = vec![];
        for i in 0..group_size {
            let mut sub_res: Vec<Vec<u128>> = stream_1_2_es.par_iter_mut().zip(final_res_share2_anno2s[i*group_size..(i+1)*group_size].into_par_iter()).map(|(stream, data)| {
                ev_agg_entire(
                    &data.iter().map(|x| *x as u128).collect(),
                    stream,
                    AggType::Add,
                )
            }).collect();
            agg_add_res2_anno2s.append(&mut sub_res);
        }

        // reveal (agg_add_res2_anno1, agg_add_res2_anno2) to thread_2
        let bytes = bincode::serialize(&(agg_add_res2_anno1s, agg_add_res2_anno2s)).unwrap();
        send_data_by_stream(&mut tx_1_2_b, &bytes, false);
        // tx_1_2_b
        // .send((agg_add_res2_anno1s, agg_add_res2_anno2s))
        // .unwrap();
    });
    });

    // thread_2 has: lineitem, customer
    let thread_2 = std::thread::spawn(move || {
        let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
        pool.install(|| {
        let self_id = process_id + N * 1;

        //### step 1: O.semijoin(C), C as sender
        // no need to group by because c_custkey is prime
        let xs_pts = points_from_num(c_custkey.clone());
        let xs_tree = SubProductTree::new_from_points_parallel(&xs_pts);

        let res_c_o_s1s = batch_psi_anno_sender_parallel(
            vec![c_custkey.into_iter().map(|x| x as u64).collect(); query_num],
            vec![c_anno.into_iter().map(|x| x as u64).collect(); query_num],
            &kzg_2_1st,
            &mut stream_2_1,
            &vec![xs_info_1; query_num],
            &vec![xs_tree; query_num],
            debug,
            self_id,
            ys_len_larger_1st,
            out_len_1st,
            sen_streams_1st,
        );

        // consensus on res_c_o_s1
        let bytes = bincode::serialize(&res_c_o_s1s).unwrap();
        let dig = digest(Algorithm::SHA256, &bytes);
        if !debug {
            run_consensus(dig, self_id);
        }
        //### step 2: L.semijoin(P), L as receiver
        let res_p_l_s2s = batch_psi_anno_receiver_parallel(
            &vec![l_partkey; query_num],
            true,
            vec![ys_2nd_no_dup.into_iter().map(|x| x as u64).collect(); query_num],
            &kzg_2_2nd,
            &mut stream_2_3,
            &vec![ys_tree_2nd; query_num],
            &vec![veri_info_2; query_num],
            vec![z_commit_2; query_num],
            self_id,
            ys_len_larger_2nd,
            debug,
            rec_streams_2nd,
        );

        // consensus on res_p_l_s2
        let bytes = bincode::serialize(&res_p_l_s2s).unwrap();
        let dig = digest(Algorithm::SHA256, &bytes);
        if !debug {
            run_consensus(dig, self_id);
        }
        //### step 3: L.semijoin(S) L is receiver
        let res_s_l_s2_anno1s = batch_psi_anno_receiver_parallel(
            &vec![l_suppkey.clone(); query_num],
            true,
            vec![ys_3rd_no_dup.iter().map(|x| *x as u64).collect(); query_num],
            &kzg_2_3rd,
            &mut stream_2_3,
            &vec![ys_tree_3rd.clone(); query_num],
            &vec![veri_info_3.clone(); query_num],
            vec![z_commit_3; query_num],
            self_id,
            ys_len_larger_3rd,
            debug,
            rec_streams_3rd,
        );

        let res_s_l_s2_anno2s = batch_psi_anno_receiver_parallel(
            &vec![l_suppkey; query_num],
            true,
            vec![ys_3rd_no_dup.iter().map(|x| *x as u64).collect(); query_num],
            &kzg_2_3rd,
            &mut stream_2_3,
            &vec![ys_tree_3rd; query_num],
            &vec![veri_info_3; query_num],
            vec![z_commit_3; query_num],
            self_id,
            ys_len_larger_3rd,
            debug,
            rec_streams_3rd_b,
        );

        let (l_anno_1, l_anno_2) = gen_shared_anno(l_anno.into_iter().map(|x| x as u128).collect());
        let l_anno_1s = vec![l_anno_1; query_num];
        let l_anno_2s = vec![l_anno_2; query_num];

        let bytes = bincode::serialize(&l_anno_1s).unwrap();
        send_data_by_stream(&mut tx_2_3, &bytes, false);
        // tx_2_3.send(l_anno_1s).unwrap();

        let mut res_p_l_mul_s2s = vec![];
        for (res_p_l_s2, l_anno_2) in res_p_l_s2s.iter().zip(l_anno_2s.iter()) {
            res_p_l_mul_s2s.push(vec_mul_2(
                &l_anno_2,
                &res_p_l_s2,
                &a2_l_len,
                &b2_l_len,
                &c2_l_len,
                &mut stream_2_3,
            ));
        }
        // corresponding to s_anno1
        let mut res_p_s_l_mul_anno1_s2s = vec![];
        for (res_p_l_mul_s2, res_s_l_s2_anno1) in
            res_p_l_mul_s2s.iter().zip(res_s_l_s2_anno1s.iter())
        {
            res_p_s_l_mul_anno1_s2s.push(vec_mul_2(
                &res_p_l_mul_s2,
                &res_s_l_s2_anno1,
                &a2_l_len,
                &b2_l_len,
                &c2_l_len,
                &mut stream_2_3,
            ));
        }
        // corresponding to s_anno2
        let mut res_p_s_l_mul_anno2_s2s = vec![];
        for (res_p_l_mul_s2, res_s_l_s2_anno2) in
            res_p_l_mul_s2s.iter().zip(res_s_l_s2_anno2s.iter())
        {
            res_p_s_l_mul_anno2_s2s.push(vec_mul_2(
                &res_p_l_mul_s2,
                &res_s_l_s2_anno2,
                &a2_l_len,
                &b2_l_len,
                &c2_l_len,
                &mut stream_2_3,
            ));
        }

        //### step 4: L.semijoin(O) L is sender
        // OP to sort by l_orderkey
        // convert u128 share to u32 share for later OP

        let res_p_s_l_mul_anno1_s2s =
            batch_sen_u128_to_u32(res_p_s_l_mul_anno1_s2s, &mut rx_1_2, &mut tx_2_1);
        let res_p_s_l_mul_anno2_s2s =
            batch_sen_u128_to_u32(res_p_s_l_mul_anno2_s2s, &mut rx_1_2, &mut tx_2_1);

        let l_orderkey_pmt = get_sort_pmt(&l_orderkey);
        let sorted_l_orderkey = sort_by_pmt(&l_orderkey, &l_orderkey_pmt);

        let res_p_s_l_mul_anno1_s2s: Vec<Vec<u32>> = res_p_s_l_mul_anno1_s2s
            .iter()
            .map(|res_p_s_l_mul_anno1_s2| {
                permutor_permute(&mut stream_2_1, &l_orderkey_pmt, &res_p_s_l_mul_anno1_s2)
            })
            .collect();

        let res_p_s_l_mul_anno2_s2s: Vec<Vec<u32>> = res_p_s_l_mul_anno2_s2s
            .iter()
            .map(|res_p_s_l_mul_anno2_s2| {
                permutor_permute(&mut stream_2_1, &l_orderkey_pmt, &res_p_s_l_mul_anno2_s2)
            })
            .collect();

        // circuit to do oblivious add_agg
        let ind = get_ind(&sorted_l_orderkey);
        let agg_add_res2_anno1 = gen_random::<u128>(out_len_3rd);
        let agg_add_res2_anno2 = gen_random::<u128>(out_len_3rd);


        for i in 0..group_size {
            stream_2_1_bs.par_iter_mut().zip(res_p_s_l_mul_anno1_s2s[i*group_size..(i+1)*group_size].into_par_iter()).for_each(|(stream, data)| {
                gb_agg_entire(
                    &ind,
                    &data.iter().map(|v| *v as u128).collect(),
                    stream,
                    AggType::Add,
                    &agg_add_res2_anno1,
                );
            });
        }

        for i in 0..group_size {
            stream_2_1_cs.par_iter_mut().zip(res_p_s_l_mul_anno2_s2s[i*group_size..(i+1)*group_size].into_par_iter()).for_each(|(stream, data)| {
                gb_agg_entire(
                    &ind,
                    &data.iter().map(|v| *v as u128).collect(),
                    stream,
                    AggType::Add,
                    &agg_add_res2_anno2,
                );
            });
        }


        let dummyed_l_orderkey = local_group_by_with_dummy(&sorted_l_orderkey);

        // convert u128 share to u32 share
        let agg_add_res2_anno1s = batch_sen_u128_to_u32(
            vec![agg_add_res2_anno1; query_num],
            &mut rx_1_2,
            &mut tx_2_1,
        );
        let agg_add_res2_anno2s = batch_sen_u128_to_u32(
            vec![agg_add_res2_anno2; query_num],
            &mut rx_1_2,
            &mut tx_2_1,
        );

        let xs_pts = points_from_num(dummyed_l_orderkey.clone());
        let xs_tree = SubProductTree::new_from_points_parallel(&xs_pts);

        let res_s1_anno1s = batch_psi_shared_anno_sender_parallel(
            vec![dummyed_l_orderkey.iter().map(|v| *v as u64).collect(); query_num],
            agg_add_res2_anno1s,
            &kzg_2_4th,
            &mut stream_2_1,
            &vec![xs_info_4.clone(); query_num],
            &vec![xs_tree.clone(); query_num],
            debug,
            self_id,
            ys_len_larger_4th,
            out_len_4th,
            chunk_size,
            sen_streams_4th,
            sen_streams_4th_oep,
        );

        let res_s1_anno2s = batch_psi_shared_anno_sender_parallel(
            vec![dummyed_l_orderkey.iter().map(|v| *v as u64).collect(); query_num],
            agg_add_res2_anno2s,
            &kzg_2_4th,
            &mut stream_2_1,
            &vec![xs_info_4; query_num],
            &vec![xs_tree; query_num],
            debug,
            self_id,
            ys_len_larger_4th,
            out_len_4th,
            chunk_size,
            sen_streams_4th_b,
            sen_streams_4th_oep_b,
        );

        // u32 to u128 share
        let res_s1_anno1s = batch_rec_u32_to_u128(res_s1_anno1s, &mut tx_2_1, &mut rx_1_2);
        let res_s1_anno2s = batch_rec_u32_to_u128(res_s1_anno2s, &mut tx_2_1, &mut rx_1_2);

        // compute o_anno * res_c_o * res_anno1 and o_anno * res_c_o * res_anno2 using beaver triples
        let final_res_share1_anno1s: Vec<Vec<u128>> = res_c_o_s1s
            .iter()
            .zip(res_s1_anno1s.iter())
            .map(|(res_c_o_s1, res_s1_anno1)| {
                vec_mul_1(
                    res_c_o_s1,
                    res_s1_anno1,
                    &a1_o_len,
                    &b1_o_len,
                    &c1_o_len,
                    &mut stream_2_1,
                )
            })
            .collect();
        let final_res_share1_anno2s: Vec<Vec<u128>> = res_c_o_s1s
            .iter()
            .zip(res_s1_anno2s.iter())
            .map(|(res_c_o_s1, res_s1_anno2)| {
                vec_mul_1(
                    &res_c_o_s1,
                    &res_s1_anno2,
                    &a1_o_len,
                    &b1_o_len,
                    &c1_o_len,
                    &mut stream_2_1,
                )
            })
            .collect();
        let (o_anno1, o_anno2) = gen_shared_anno(o_anno.into_iter().map(|x| x as u128).collect());
        let o_anno1s = vec![o_anno1; query_num];
        let o_anno2s = vec![o_anno2; query_num];

        let bytes = bincode::serialize(&o_anno2s).unwrap();
        send_data_by_stream(&mut tx_2_1_b, &bytes, false);

        let final_res_share1_anno1s: Vec<Vec<u128>> = o_anno1s
            .iter()
            .zip(final_res_share1_anno1s.iter())
            .map(|(o_anno1, final_res_share1_anno1)| {
                vec_mul_1(
                    o_anno1,
                    final_res_share1_anno1,
                    &a1_o_len,
                    &b1_o_len,
                    &c1_o_len,
                    &mut stream_2_1,
                )
            })
            .collect();
        let final_res_share1_anno2s: Vec<Vec<u128>> = o_anno1s
            .iter()
            .zip(final_res_share1_anno2s.iter())
            .map(|(o_anno1, final_res_share1_anno2)| {
                vec_mul_1(
                    &o_anno1,
                    &final_res_share1_anno2,
                    &a1_o_len,
                    &b1_o_len,
                    &c1_o_len,
                    &mut stream_2_1,
                )
            })
            .collect();

        let final_res_share1_anno1s =
            batch_sen_u128_to_u32(final_res_share1_anno1s, &mut rx_1_2, &mut tx_2_1);
        let final_res_share1_anno2s =
            batch_sen_u128_to_u32(final_res_share1_anno2s, &mut rx_1_2, &mut tx_2_1);

        // group by o_year using agg_add circuit
        let o_year_pmt = get_sort_pmt(&o_year);
        let sorted_o_year = sort_by_pmt(&o_year, &o_year_pmt);

        let final_res_share1_anno1s: Vec<Vec<u32>> = final_res_share1_anno1s
            .iter()
            .map(|final_res_share1_anno1| {
                permutor_permute(&mut stream_2_1, &o_year_pmt, &final_res_share1_anno1)
            })
            .collect();
        let final_res_share1_anno2s: Vec<Vec<u32>> = final_res_share1_anno2s
            .iter()
            .map(|final_res_share1_anno2| {
                permutor_permute(&mut stream_2_1, &o_year_pmt, &final_res_share1_anno2)
            })
            .collect();

        let ind = get_ind(&sorted_o_year);
        let agg_add_res1_anno1 = gen_random::<u128>(out_len_1st);
        let agg_add_res1_anno2 = agg_add_res1_anno1.clone();

        for i in 0..group_size {
            stream_2_1_ds.par_iter_mut().zip(final_res_share1_anno1s[i*group_size..(i+1)*group_size].into_par_iter()).for_each(|(stream, data)| {
                gb_agg_entire(
                    &ind,
                    &data.iter().map(|v| *v as u128).collect(),
                    stream,
                    AggType::Add,
                    &agg_add_res1_anno1,
                );
            });
        }

        for i in 0..group_size {
            stream_2_1_es.par_iter_mut().zip(final_res_share1_anno2s[i*group_size..(i+1)*group_size].into_par_iter()).for_each(|(stream, data)| {
                gb_agg_entire(
                    &ind,
                    &data.iter().map(|v| *v as u128).collect(),
                    stream,
                    AggType::Add,
                    &agg_add_res1_anno2,
                );
            });
        }

        // receive revealed share from thread_1
        let bytes = receive_data_by_stream(&mut rx_1_2_b);
        let (agg_add_res2_anno1s, agg_add_res2_anno2s): (Vec<Vec<u128>>, Vec<Vec<u128>>) =
            bincode::deserialize(&bytes).unwrap();
        // let (agg_add_res2_anno1s, agg_add_res2_anno2s) = rx_1_2_b.recv().unwrap();

        let res_anno1s: Vec<Vec<u128>> = agg_add_res2_anno1s
            .into_par_iter()
            .map(|agg_add_res2_anno1| combine_share(agg_add_res1_anno1.clone(), agg_add_res2_anno1))
            .collect();
        let res_anno2s: Vec<Vec<u128>> = agg_add_res2_anno2s
            .into_par_iter()
            .map(|agg_add_res2_anno2| combine_share(agg_add_res1_anno2.clone(), agg_add_res2_anno2))
            .collect();

        for (res_anno1, res_anno2) in res_anno1s.iter().zip(res_anno2s.iter()) {
            let mut col_o_year1 = vec![];
            let mut col_o_year2 = vec![];
            let mut col_anno1 = vec![];
            let mut col_anno2 = vec![];
            for i in 0..res_anno1.len() {
                if res_anno1[i] != 0 {
                    col_o_year1.push(o_year[i]);
                    col_anno1.push(res_anno1[i] as u32);
                }
                if res_anno2[i] != 0 {
                    col_o_year2.push(o_year[i]);
                    col_anno2.push(res_anno2[i] as u32);
                }
            }

            // the clean result relation
            let res_relation1 = Relation::new(vec![col_o_year1, col_anno1]);
            let res_relation2 = Relation::new(vec![col_o_year2, col_anno2]);

            println!("{:?}", res_relation1);
            println!("===========================");
            println!("{:?}", res_relation2);
            break;
        }
    });
    });

    // thread_3 has: supplier, part
    let thread_3 = std::thread::spawn(move || {
        let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
        pool.install(|| {
        let self_id = process_id + N * 2;
        //### step 2: L.semijoin(P), P as sender
        // no need to group by because p_partkey is prime
        let xs_pts = points_from_num(p_partkey.clone());
        let xs_tree = SubProductTree::new_from_points_parallel(&xs_pts);

        let res_p_l_s1s = batch_psi_anno_sender_parallel(
            vec![p_partkey.into_iter().map(|x| x as u64).collect(); query_num],
            vec![p_anno.into_iter().map(|x| x as u64).collect(); query_num],
            &kzg_3_2nd,
            &mut stream_3_2,
            &vec![xs_info_2; query_num],
            &vec![xs_tree; query_num],
            debug,
            self_id,
            ys_len_larger_2nd,
            out_len_2nd,
            sen_streams_2nd,
        );

        //### step 3: L.semijoin(S) S is sender
        // no need to group by because s_suppkey is prime
        let xs_pts = points_from_num(s_suppkey.clone());
        let xs_tree = SubProductTree::new_from_points_parallel(&xs_pts);

        let res_s_l_s1_anno1s = batch_psi_anno_sender_parallel(
            vec![s_suppkey.iter().map(|x| *x as u64).collect(); query_num],
            vec![s_anno1.into_iter().map(|x| x as u64).collect(); query_num],
            &kzg_3_3rd,
            &mut stream_3_2,
            &vec![xs_info_3.clone(); query_num],
            &vec![xs_tree.clone(); query_num],
            debug,
            self_id,
            ys_len_larger_3rd,
            out_len_3rd,
            sen_streams_3rd,
        );

        let res_s_l_s1_anno2s = batch_psi_anno_sender_parallel(
            vec![s_suppkey.into_iter().map(|x| x as u64).collect(); query_num],
            vec![s_anno2.into_iter().map(|x| x as u64).collect(); query_num],
            &kzg_3_3rd,
            &mut stream_3_2,
            &vec![xs_info_3; query_num],
            &vec![xs_tree; query_num],
            debug,
            self_id,
            ys_len_larger_3rd,
            out_len_3rd,
            sen_streams_3rd_b,
        );

        // now compute p_anno * l_anno * s_anno_{1, 2}
        // consider lazy the vec_mul? will need extra obliPer

        let bytes = receive_data_by_stream(&mut rx_2_3);
        let l_anno_1s: Vec<Vec<u128>> = bincode::deserialize(&bytes).unwrap();

        let res_p_l_mul_s1s: Vec<Vec<u128>> = l_anno_1s
            .iter()
            .zip(res_p_l_s1s.iter())
            .map(|(l_anno_1, res_p_l_s1)| {
                vec_mul_1(
                    &l_anno_1,
                    &res_p_l_s1,
                    &a1_l_len,
                    &b1_l_len,
                    &c1_l_len,
                    &mut stream_3_2,
                )
            })
            .collect();

        let res_p_s_l_mul_anno1_s1s: Vec<Vec<u128>> = res_p_l_mul_s1s
            .iter()
            .zip(res_s_l_s1_anno1s.iter())
            .map(|(res_p_l_mul_s1, res_s_l_s1_anno1)| {
                vec_mul_1(
                    &res_p_l_mul_s1,
                    &res_s_l_s1_anno1,
                    &a1_l_len,
                    &b1_l_len,
                    &c1_l_len,
                    &mut stream_3_2,
                )
            })
            .collect();

        let res_p_s_l_mul_anno2_s1s: Vec<Vec<u128>> = res_p_l_mul_s1s
            .iter()
            .zip(res_s_l_s1_anno2s.iter())
            .map(|(res_p_l_mul_s1, res_s_l_s1_anno2)| {
                vec_mul_1(
                    &res_p_l_mul_s1,
                    &res_s_l_s1_anno2,
                    &a1_l_len,
                    &b1_l_len,
                    &c1_l_len,
                    &mut stream_3_2,
                )
            })
            .collect();

        // send res_p_s_l_mul_anno1_s1, res_p_s_l_mul_anno2_s1 to thread_1
        let bytes =
            bincode::serialize(&(res_p_s_l_mul_anno1_s1s, res_p_s_l_mul_anno2_s1s)).unwrap();
        send_data_by_stream(&mut tx_3_1, &bytes, false);
        // tx_3_1
        //     .send((res_p_s_l_mul_anno1_s1s, res_p_s_l_mul_anno2_s1s))
        //     .unwrap();
        });
    });

    thread_1.join().unwrap();
    thread_2.join().unwrap();
    thread_3.join().unwrap();
    let t = timer.elapsed().real.as_micros() as u64;
    println!(" query processing time: {} ms", t / 1000);
    let intra_comm = crate::INTRA_SHARD_COMM.lock().unwrap();
    let cross_comm = crate::CROSS_SHARD_COMM.lock().unwrap();
    let consen_num = crate::CONSENSUS_NUM.lock().unwrap();
    crate::tpch::show_comm_cost(*intra_comm, *cross_comm, *consen_num);
}

pub fn exe_q8_single(path: &Path, chunk_size: usize, process_id: u16, debug: bool, intra: bool) {
    println!("loading dataset...");
    let (
        (customer, c_anno),
        (orders, o_anno),
        (lineitem, l_anno),
        (part, p_anno),
        (supplier, s_anno1, s_anno2),
    ) = load_q8_tables(path, chunk_size);

    let c_custkey = customer.get_col(0); // xs
    let o_custkey = orders.get_col(1); // ys

    let p_partkey = part.get_col(0); // xs
    let l_partkey = lineitem.get_col(1); // ys

    let s_suppkey = supplier.get_col(0); // xs
    let l_suppkey = lineitem.get_col(2); // ys

    let l_orderkey = lineitem.get_col(0); // xs has duplicate
    let o_orderkey = orders.get_col(0); // ys

    let o_year = orders.get_col(2);

    let out_len_1st = o_anno.len();
    let out_len_2nd = l_anno.len();
    let out_len_3rd = out_len_2nd; // 3rd psi will be repeated
    let out_len_4th = out_len_1st; // 4th psi will be repeated

    let triples = load_beaver_truples();
    let (a1_o_len, a2_o_len, b1_o_len, b2_o_len, c1_o_len, c2_o_len) =
        obtain_beaver_tripes_by(out_len_1st, triples.clone());
    let (a1_l_len, a2_l_len, b1_l_len, b2_l_len, c1_l_len, c2_l_len) =
        obtain_beaver_tripes_by(out_len_2nd, triples);

    println!("loading pre-computed information...");
    let bytes = read_q8_pre_compute_info(path);
    let mut pre_infos: Vec<PreInfo> = Vec::<PreInfo>::deserialize_uncompressed(&*bytes).unwrap();
    // order matters
    let pre_info_4 = pre_infos.remove(3);
    let xs_info_4 = pre_info_4.xs_info;
    let veri_info_4 = pre_info_4.veri_info;
    let z_commit_4 = pre_info_4.z_commit;
    let pre_info_3 = pre_infos.remove(2);
    let xs_info_3 = pre_info_3.xs_info;
    let veri_info_3 = pre_info_3.veri_info;
    let z_commit_3 = pre_info_3.z_commit;
    let pre_info_2 = pre_infos.remove(1);
    let xs_info_2 = pre_info_2.xs_info;
    let veri_info_2 = pre_info_2.veri_info;
    let z_commit_2 = pre_info_2.z_commit;
    let pre_info_1 = pre_infos.remove(0);
    let xs_info_1 = pre_info_1.xs_info;
    let veri_info_1 = pre_info_1.veri_info;
    let z_commit_1 = pre_info_1.z_commit;

    println!("pre-computing some info...");
    let ys_pts_1st_baseline = points_from_num(o_custkey.clone());
    let ys_tree_1st_baseline = SubProductTree::new_from_points_parallel(&ys_pts_1st_baseline);
    let ys_1st_no_dup = remove_duplicate(&o_custkey);
    let ys_pts_1st = points_from_num(ys_1st_no_dup.clone());
    let ys_tree_1st = SubProductTree::new_from_points_parallel(&ys_pts_1st);

    let ys_pts_2nd_baseline = points_from_num(l_partkey.clone());
    let ys_tree_2nd_baseline = SubProductTree::new_from_points_parallel(&ys_pts_2nd_baseline);
    let ys_2nd_no_dup = remove_duplicate(&l_partkey);
    let ys_pts_2nd = points_from_num(ys_2nd_no_dup.clone());
    let ys_tree_2nd = SubProductTree::new_from_points_parallel(&ys_pts_2nd);

    let ys_pts_3rd_baseline = points_from_num(l_suppkey.clone());
    let ys_tree_3rd_baseline = SubProductTree::new_from_points_parallel(&ys_pts_3rd_baseline);
    let ys_3rd_no_dup = remove_duplicate(&l_suppkey);
    let ys_pts_3rd = points_from_num(ys_3rd_no_dup.clone());
    let ys_tree_3rd = SubProductTree::new_from_points_parallel(&ys_pts_3rd);

    let ys_pts_4th = points_from_num(o_orderkey.clone());
    let ys_tree_4th = SubProductTree::new_from_points_parallel(&ys_pts_4th);

    let ys_len_larger_1st = o_anno.len() > c_anno.len();
    let ys_len_larger_2nd = l_anno.len() > p_anno.len();
    let ys_len_larger_3rd = l_anno.len() > s_anno1.len();
    let ys_len_larger_4th = o_anno.len() > l_anno.len();

    // setup
    println!("doing setup...");
    let (sen_streams_1st, rec_streams_1st) = obtain_unix_streams(THREAD_NUM);
    let (sen_streams_2nd, rec_streams_2nd) = obtain_unix_streams(THREAD_NUM);
    let (sen_streams_3rd, rec_streams_3rd) = obtain_unix_streams(THREAD_NUM);
    let (sen_streams_3rd_b, rec_streams_3rd_b) = obtain_unix_streams(THREAD_NUM);

    let (sen_streams_4th, rec_streams_4th) = obtain_unix_streams(THREAD_NUM);
    let (sen_streams_4th_b, rec_streams_4th_b) = obtain_unix_streams(THREAD_NUM);
    let (sen_streams_4th_oep, rec_streams_4th_oep) = obtain_unix_streams(THREAD_NUM);
    let (sen_streams_4th_oep_b, rec_streams_4th_oep_b) = obtain_unix_streams(THREAD_NUM);

    // TODO: consider re-use streams?
    let (mut stream_1_2, mut stream_2_1) = UnixStream::pair().unwrap();
    let (mut stream_1_2_b, mut stream_2_1_b) = UnixStream::pair().unwrap();
    let (mut stream_1_2_c, mut stream_2_1_c) = UnixStream::pair().unwrap();
    let (mut stream_1_2_d, mut stream_2_1_d) = UnixStream::pair().unwrap();
    let (mut stream_1_2_e, mut stream_2_1_e) = UnixStream::pair().unwrap();
    let (mut stream_2_3, mut stream_3_2) = UnixStream::pair().unwrap();
    let (mut tx_2_3, mut rx_2_3) = UnixStream::pair().unwrap();
    let (mut tx_3_1, mut rx_3_1) = UnixStream::pair().unwrap();
    let (mut tx_1_2, mut rx_1_2) = UnixStream::pair().unwrap();
    let (mut tx_1_2_b, mut rx_1_2_b) = UnixStream::pair().unwrap();
    let (mut tx_2_1, mut rx_2_1) = UnixStream::pair().unwrap();
    let (mut tx_2_1_b, mut rx_2_1_b) = UnixStream::pair().unwrap();

    let mut rng = get_fixed_rng();
    let secret = Fr::rand(&mut rng);
    let n_1st_psi = c_custkey.len();
    let max_deg_1st = n_1st_psi - 1;
    let n_2nd_psi = p_partkey.len();
    let max_deg_2nd = n_2nd_psi - 1;
    let n_3rd_psi = s_suppkey.len();
    let max_deg_3rd = n_3rd_psi - 1;
    let n_4th_psi = l_orderkey.len();
    let max_deg_4th = n_4th_psi - 1;

    // thread_1
    let mut kzg_1_1st = setup_kzg(max_deg_1st);
    kzg_1_1st.setup(secret);
    let mut kzg_1_4th = setup_kzg(max_deg_4th);
    kzg_1_4th.setup(secret);
    // thread_2
    let mut kzg_2_1st = setup_kzg(max_deg_1st);
    kzg_2_1st.setup(secret);
    let mut kzg_2_2nd = setup_kzg(max_deg_2nd);
    kzg_2_2nd.setup(secret);
    let mut kzg_2_3rd = setup_kzg(max_deg_3rd);
    kzg_2_3rd.setup(secret);
    let mut kzg_2_4th = setup_kzg(max_deg_4th);
    kzg_2_4th.setup(secret);
    // thread_3
    let mut kzg_3_2nd = setup_kzg(max_deg_2nd);
    kzg_3_2nd.setup(secret);
    let mut kzg_3_3rd = setup_kzg(max_deg_3rd);
    kzg_3_3rd.setup(secret);


    
    let timer = howlong::ProcessCPUTimer::new();
    // thread_1 has: order
    let thread_1 = std::thread::spawn(move || {
        let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
        pool.install(|| {
        let self_id = process_id;
        //### step 1: O.semijoin(C), O as receiver
        // println!("thread 1: first PSI...");
        let res_c_o_s2 = if intra {
            intra_psi_anno_receiver_parallel(
                &o_custkey,
                true,
                ys_1st_no_dup.into_iter().map(|x| x as u64).collect(),
                &kzg_1_1st,
                &mut stream_1_2,
                &ys_tree_1st,
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
                o_custkey.clone().into_iter().map(|x| x as u64).collect(),
                &mut stream_1_2,
                &ys_tree_1st_baseline,
                self_id,
                debug,
                ys_len_larger_1st,
                rec_streams_1st,
            )
        };
        // consensus on res_c_o_s2
        let bytes = bincode::serialize(&res_c_o_s2).unwrap();
        let dig = digest(Algorithm::SHA256, &bytes);
        if !debug {
            run_consensus(dig, self_id);
        }

        //### step 4: L.semijoin(O) O is receiver
        let bytes = receive_data_by_stream(&mut rx_3_1);
        let (res_p_s_l_mul_anno1_s1, res_p_s_l_mul_anno2_s1): (Vec<u128>, Vec<u128>) =
            bincode::deserialize(&bytes).unwrap();

        // convert u128 share to u32 share
        let res_p_s_l_mul_anno1_s1 =
            rec_u128_to_u32(res_p_s_l_mul_anno1_s1, &mut tx_1_2, &mut rx_2_1);
        let res_p_s_l_mul_anno2_s1 =
            rec_u128_to_u32(res_p_s_l_mul_anno2_s1, &mut tx_1_2, &mut rx_2_1);

        let res_p_s_l_mul_anno1_s1 = sender_permute(&mut stream_1_2, &res_p_s_l_mul_anno1_s1);
        let res_p_s_l_mul_anno2_s1 = sender_permute(&mut stream_1_2, &res_p_s_l_mul_anno2_s1);

        // corresponding to s_anno1
        let agg_add_res1_anno1 = ev_agg_entire(
            &res_p_s_l_mul_anno1_s1.iter().map(|x| *x as u128).collect(),
            &mut stream_1_2_b,
            AggType::Add,
        );
        // corresponding to s_anno2
        let agg_add_res1_anno2 = ev_agg_entire(
            &res_p_s_l_mul_anno2_s1.iter().map(|x| *x as u128).collect(),
            &mut stream_1_2_c,
            AggType::Add,
        );

        // convert u128 share to u32 for later psi
        let agg_add_res1_anno1 = rec_u128_to_u32(agg_add_res1_anno1, &mut tx_1_2, &mut rx_2_1);
        let agg_add_res1_anno2 = rec_u128_to_u32(agg_add_res1_anno2, &mut tx_1_2, &mut rx_2_1);


        let res_s2_anno1 = if intra {
            intra_psi_shared_anno_receiver_parallel(
                &o_orderkey,
                false,
                o_orderkey.clone().into_iter().map(|x| x as u64).collect(),
                &kzg_1_4th,
                &ys_tree_4th,
                &vec![veri_info_4.clone()],
                vec![z_commit_4],
                agg_add_res1_anno1,
                &mut stream_1_2,
                chunk_size,
                self_id,
                4 % N,
                debug,
                ys_len_larger_4th,
                rec_streams_4th,
                rec_streams_4th_oep,
            )
        } else {
            basic_psi_shared_anno_receiver_parallel(
                o_orderkey.clone().into_iter().map(|x| x as u64).collect(),
                &ys_tree_4th,
                agg_add_res1_anno1,
                &mut stream_1_2,
                chunk_size,
                self_id,
                debug,
                ys_len_larger_4th,
                rec_streams_4th,
                rec_streams_4th_oep,
            )
        };

        let res_s2_anno2 = if intra {
            intra_psi_shared_anno_receiver_parallel(
                &o_orderkey,
                false,
                o_orderkey.clone().into_iter().map(|x| x as u64).collect(),
                &kzg_1_4th,
                &ys_tree_4th,
                &vec![veri_info_4],
                vec![z_commit_4],
                agg_add_res1_anno2,
                &mut stream_1_2,
                chunk_size,
                self_id,
                5 % N,
                debug,
                ys_len_larger_4th,
                rec_streams_4th_b,
                rec_streams_4th_oep_b,
            )
        } else {
            basic_psi_shared_anno_receiver_parallel(
                o_orderkey.clone().into_iter().map(|x| x as u64).collect(),
                &ys_tree_4th,
                agg_add_res1_anno2,
                &mut stream_1_2,
                chunk_size,
                self_id,
                debug,
                ys_len_larger_4th,
                rec_streams_4th_b,
                rec_streams_4th_oep_b,
            )
        };

        let res_s2_anno1 = sen_u32_to_u128(res_s2_anno1, &mut rx_2_1, &mut tx_1_2);
        let res_s2_anno2 = sen_u32_to_u128(res_s2_anno2, &mut rx_2_1, &mut tx_1_2);

        // compute o_anno * res_c_o * res_anno1 and o_anno * res_c_o * res_anno2 using beaver triples
        let final_res_share2_anno1 = vec_mul_2(
            &res_c_o_s2,
            &res_s2_anno1,
            &a2_o_len,
            &b2_o_len,
            &c2_o_len,
            &mut stream_1_2,
        );
        let final_res_share2_anno2 = vec_mul_2(
            &res_c_o_s2,
            &res_s2_anno2,
            &a2_o_len,
            &b2_o_len,
            &c2_o_len,
            &mut stream_1_2,
        );

        let bytes = receive_data_by_stream(&mut rx_2_1_b);
        let o_anno2: Vec<u128> = bincode::deserialize(&bytes).unwrap();

        let final_res_share2_anno1 = vec_mul_2(
            &o_anno2,
            &final_res_share2_anno1,
            &a2_o_len,
            &b2_o_len,
            &c2_o_len,
            &mut stream_1_2,
        );

        let final_res_share2_anno2 = vec_mul_2(
            &o_anno2,
            &final_res_share2_anno2,
            &a2_o_len,
            &b2_o_len,
            &c2_o_len,
            &mut stream_1_2,
        );

        let final_res_share2_anno1 =
            rec_u128_to_u32(final_res_share2_anno1, &mut tx_1_2, &mut rx_2_1);
        let final_res_share2_anno2 =
            rec_u128_to_u32(final_res_share2_anno2, &mut tx_1_2, &mut rx_2_1);

        let final_res_share2_anno1 = sender_permute(&mut stream_1_2, &final_res_share2_anno1);
        let final_res_share2_anno2 = sender_permute(&mut stream_1_2, &final_res_share2_anno2);

        // run agg_add circuit
        let agg_add_res2_anno1 = ev_agg_entire(
            &final_res_share2_anno1
                .par_iter()
                .map(|x| *x as u128)
                .collect(),
            &mut stream_1_2_d,
            AggType::Add,
        );
        let agg_add_res2_anno2 = ev_agg_entire(
            &final_res_share2_anno2
                .par_iter()
                .map(|x| *x as u128)
                .collect(),
            &mut stream_1_2_e,
            AggType::Add,
        );

        // reveal (agg_add_res2_anno1, agg_add_res2_anno2) to thread_2
        let bytes = bincode::serialize(&(agg_add_res2_anno1, agg_add_res2_anno2)).unwrap();
        send_data_by_stream(&mut tx_1_2_b, &bytes, false);
        // tx_1_2_b
        //     .send((agg_add_res2_anno1, agg_add_res2_anno2))
        //     .unwrap();
    });
    });

    // thread_2 has: lineitem, customer
    let thread_2 = std::thread::spawn(move || {
        let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
        pool.install(|| {
        let self_id = process_id + N * 1;

        //### step 1: O.semijoin(C), C as sender
        // no need to group by because c_custkey is prime
        let xs_pts = points_from_num(c_custkey.clone());
        let xs_tree = SubProductTree::new_from_points_parallel(&xs_pts);

        let res_c_o_s1 = if intra {
            intra_psi_anno_sender_parallel(
                c_custkey.into_iter().map(|x| x as u64).collect(),
                c_anno.into_iter().map(|x| x as u64).collect(),
                &kzg_2_1st,
                &mut stream_2_1,
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
                c_custkey.into_iter().map(|x| x as u64).collect(),
                c_anno.into_iter().map(|x| x as u64).collect(),
                &xs_tree,
                &mut stream_2_1,
                out_len_1st,
                self_id,
                debug,
                ys_len_larger_1st,
                sen_streams_1st,
            )
        };

        // consensus on res_c_o_s1
        let bytes = bincode::serialize(&res_c_o_s1).unwrap();
        let dig = digest(Algorithm::SHA256, &bytes);
        if !debug {
            run_consensus(dig, self_id);
        }

        //### step 2: L.semijoin(P), L as receiver
        let res_p_l_s2 = if intra {
            intra_psi_anno_receiver_parallel(
                &l_partkey,
                true,
                ys_2nd_no_dup.into_iter().map(|x| x as u64).collect(),
                &kzg_2_2nd,
                &mut stream_2_3,
                &ys_tree_2nd,
                &vec![veri_info_2],
                vec![z_commit_2],
                self_id,
                1,
                ys_len_larger_2nd,
                debug,
                false,
                rec_streams_2nd,
            )
        } else {
            basic_psi_anno_receiver_parallel(
                l_partkey.clone().into_iter().map(|x| x as u64).collect(),
                &mut stream_2_3,
                &ys_tree_2nd_baseline,
                self_id,
                debug,
                ys_len_larger_2nd,
                rec_streams_2nd,
            )
        };

        // consensus on res_p_l_s2
        let bytes = bincode::serialize(&res_p_l_s2).unwrap();
        let dig = digest(Algorithm::SHA256, &bytes);
        if !debug {
            run_consensus(dig, self_id);
        }

        //### step 3: L.semijoin(S) L is receiver
        let res_s_l_s2_anno1 = if intra {
            intra_psi_anno_receiver_parallel(
                &l_suppkey,
                true,
                ys_3rd_no_dup.iter().map(|x| *x as u64).collect(),
                &kzg_2_3rd,
                &mut stream_2_3,
                &ys_tree_3rd,
                &vec![veri_info_3.clone()],
                vec![z_commit_3],
                self_id,
                2,
                ys_len_larger_3rd,
                debug,
                false,
                rec_streams_3rd,
            )
        } else {
            basic_psi_anno_receiver_parallel(
                l_suppkey.clone().into_iter().map(|x| x as u64).collect(),
                &mut stream_2_3,
                &ys_tree_3rd_baseline,
                self_id,
                debug,
                ys_len_larger_3rd,
                rec_streams_3rd,
            )
        };
        let res_s_l_s2_anno2 = if intra {
            intra_psi_anno_receiver_parallel(
                &l_suppkey,
                true,
                ys_3rd_no_dup.into_iter().map(|x| x as u64).collect(),
                &kzg_2_3rd,
                &mut stream_2_3,
                &ys_tree_3rd,
                &vec![veri_info_3],
                vec![z_commit_3],
                self_id,
                3,
                ys_len_larger_3rd,
                debug,
                false,
                rec_streams_3rd_b,
            )
        } else {
            basic_psi_anno_receiver_parallel(
                l_suppkey.clone().into_iter().map(|x| x as u64).collect(),
                &mut stream_2_3,
                &ys_tree_3rd_baseline,
                self_id,
                debug,
                ys_len_larger_3rd,
                rec_streams_3rd_b,
            )
        };
        let (l_anno_1, l_anno_2) =
            gen_shared_anno(l_anno.into_par_iter().map(|x| x as u128).collect());
        let bytes = bincode::serialize(&l_anno_1).unwrap();
        send_data_by_stream(&mut tx_2_3, &bytes, false);

        let res_p_l_mul_s2 = vec_mul_2(
            &l_anno_2,
            &res_p_l_s2,
            &a2_l_len,
            &b2_l_len,
            &c2_l_len,
            &mut stream_2_3,
        );
        // corresponding to s_anno1
        let res_p_s_l_mul_anno1_s2 = vec_mul_2(
            &res_p_l_mul_s2,
            &res_s_l_s2_anno1,
            &a2_l_len,
            &b2_l_len,
            &c2_l_len,
            &mut stream_2_3,
        );
        // corresponding to s_anno2
        let res_p_s_l_mul_anno2_s2 = vec_mul_2(
            &res_p_l_mul_s2,
            &res_s_l_s2_anno2,
            &a2_l_len,
            &b2_l_len,
            &c2_l_len,
            &mut stream_2_3,
        );

        //### step 4: L.semijoin(O) L is sender
        // OP to sort by l_orderkey
        // convert u128 share to u32 share for later OP
        let res_p_s_l_mul_anno1_s2 =
            sen_u128_to_u32(res_p_s_l_mul_anno1_s2, &mut rx_1_2, &mut tx_2_1);
        let res_p_s_l_mul_anno2_s2 =
            sen_u128_to_u32(res_p_s_l_mul_anno2_s2, &mut rx_1_2, &mut tx_2_1);
        let l_orderkey_pmt = get_sort_pmt(&l_orderkey);
        let sorted_l_orderkey = sort_by_pmt(&l_orderkey, &l_orderkey_pmt);
        let res_p_s_l_mul_anno1_s2 =
            permutor_permute(&mut stream_2_1, &l_orderkey_pmt, &res_p_s_l_mul_anno1_s2);
        let res_p_s_l_mul_anno2_s2 =
            permutor_permute(&mut stream_2_1, &l_orderkey_pmt, &res_p_s_l_mul_anno2_s2);
        // circuit to do oblivious add_agg
        let ind = get_ind(&sorted_l_orderkey);
        let agg_add_res2_anno1 = gen_random::<u128>(out_len_3rd);
        let agg_add_res2_anno2 = gen_random::<u128>(out_len_3rd);

        gb_agg_entire(
            &ind,
            &res_p_s_l_mul_anno1_s2
                .iter()
                .map(|v| *v as u128)
                .collect(),
            &mut stream_2_1_b,
            AggType::Add,
            &agg_add_res2_anno1,
        );

        gb_agg_entire(
            &ind,
            &res_p_s_l_mul_anno2_s2.iter().map(|v| *v as u128).collect(),
            &mut stream_2_1_c,
            AggType::Add,
            &agg_add_res2_anno2,
        );

        let dummyed_l_orderkey = local_group_by_with_dummy(&sorted_l_orderkey);
        // convert u128 share to u32 share
        let agg_add_res2_anno1 = sen_u128_to_u32(agg_add_res2_anno1, &mut rx_1_2, &mut tx_2_1);
        let agg_add_res2_anno2 = sen_u128_to_u32(agg_add_res2_anno2, &mut rx_1_2, &mut tx_2_1);

        let xs_pts = points_from_num(dummyed_l_orderkey.clone());
        let xs_tree = SubProductTree::new_from_points_parallel(&xs_pts);

        let res_s1_anno1 = if intra {
            intra_psi_shared_anno_sender_parallel(
                dummyed_l_orderkey.iter().map(|v| *v as u64).collect(),
                agg_add_res2_anno1,
                &kzg_2_4th,
                &xs_tree,
                &xs_info_4,
                out_len_4th,
                chunk_size,
                &mut stream_2_1,
                self_id,
                4 % N,
                debug,
                ys_len_larger_4th,
                sen_streams_4th,
                sen_streams_4th_oep,
            )
        } else {
            basic_psi_shared_anno_sender_parallel(
                dummyed_l_orderkey.iter().map(|v| *v as u64).collect(),
                agg_add_res2_anno1,
                &xs_tree,
                out_len_4th,
                chunk_size,
                &mut stream_2_1,
                self_id,
                debug,
                ys_len_larger_4th,
                sen_streams_4th,
                sen_streams_4th_oep,
            )
        };

        let res_s1_anno2 = if intra {
            intra_psi_shared_anno_sender_parallel(
                dummyed_l_orderkey.iter().map(|v| *v as u64).collect(),
                agg_add_res2_anno2,
                &kzg_2_4th,
                &xs_tree,
                &xs_info_4,
                out_len_4th,
                chunk_size,
                &mut stream_2_1,
                self_id,
                5 % N,
                debug,
                ys_len_larger_4th,
                sen_streams_4th_b,
                sen_streams_4th_oep_b,
            )
        } else {
            basic_psi_shared_anno_sender_parallel(
                dummyed_l_orderkey.into_iter().map(|v| v as u64).collect(),
                agg_add_res2_anno2,
                &xs_tree,
                out_len_4th,
                chunk_size,
                &mut stream_2_1,
                self_id,
                debug,
                ys_len_larger_4th,
                sen_streams_4th_b,
                sen_streams_4th_oep_b,
            )
        };
        // u32 to u128 share
        let res_s1_anno1 = rec_u32_to_u128(res_s1_anno1, &mut tx_2_1, &mut rx_1_2);
        let res_s1_anno2 = rec_u32_to_u128(res_s1_anno2, &mut tx_2_1, &mut rx_1_2);
        // compute o_anno * res_c_o * res_anno1 and o_anno * res_c_o * res_anno2 using beaver triples
        let final_res_share1_anno1 = vec_mul_1(
            &res_c_o_s1,
            &res_s1_anno1,
            &a1_o_len,
            &b1_o_len,
            &c1_o_len,
            &mut stream_2_1,
        );
        let final_res_share1_anno2 = vec_mul_1(
            &res_c_o_s1,
            &res_s1_anno2,
            &a1_o_len,
            &b1_o_len,
            &c1_o_len,
            &mut stream_2_1,
        );

        let (o_anno1, o_anno2) =
            gen_shared_anno(o_anno.into_par_iter().map(|x| x as u128).collect());
        let bytes = bincode::serialize(&o_anno2).unwrap();
        send_data_by_stream(&mut tx_2_1_b, &bytes, false);

        let final_res_share1_anno1 = vec_mul_1(
            &o_anno1,
            &final_res_share1_anno1,
            &a1_o_len,
            &b1_o_len,
            &c1_o_len,
            &mut stream_2_1,
        );
        let final_res_share1_anno2 = vec_mul_1(
            &o_anno1,
            &final_res_share1_anno2,
            &a1_o_len,
            &b1_o_len,
            &c1_o_len,
            &mut stream_2_1,
        );

        let final_res_share1_anno1 =
            sen_u128_to_u32(final_res_share1_anno1, &mut rx_1_2, &mut tx_2_1);
        let final_res_share1_anno2 =
            sen_u128_to_u32(final_res_share1_anno2, &mut rx_1_2, &mut tx_2_1);
        // group by o_year using agg_add circuit
        let o_year_pmt = get_sort_pmt(&o_year);
        let sorted_o_year = sort_by_pmt(&o_year, &o_year_pmt);
        let final_res_share1_anno1 =
            permutor_permute(&mut stream_2_1, &o_year_pmt, &final_res_share1_anno1);
        let final_res_share1_anno2 =
            permutor_permute(&mut stream_2_1, &o_year_pmt, &final_res_share1_anno2);

        let ind = get_ind(&sorted_o_year);
        let agg_add_res1_anno1 = gen_random::<u128>(out_len_1st);
        let agg_add_res1_anno2 = agg_add_res1_anno1.clone();

        gb_agg_entire(
            &ind,
            &final_res_share1_anno1.iter().map(|v| *v as u128).collect(),
            &mut stream_2_1_d,
            AggType::Add,
            &agg_add_res1_anno1,
        );
        gb_agg_entire(
            &ind,
            &final_res_share1_anno2.iter().map(|v| *v as u128).collect(),
            &mut stream_2_1_e,
            AggType::Add,
            &agg_add_res1_anno2,
        );
        // receive revealed share from thread_1
        let bytes = receive_data_by_stream(&mut rx_1_2_b);
        let (agg_add_res2_anno1, agg_add_res2_anno2): (Vec<u128>, Vec<u128>) =
            bincode::deserialize(&bytes).unwrap();
        // let (agg_add_res2_anno1, agg_add_res2_anno2) = rx_1_2_b.recv().unwrap();

        let res_anno1 = combine_share(agg_add_res1_anno1, agg_add_res2_anno1);
        let res_anno2 = combine_share(agg_add_res1_anno2, agg_add_res2_anno2);

        let mut col_o_year1 = vec![];
        let mut col_o_year2 = vec![];
        let mut col_anno1 = vec![];
        let mut col_anno2 = vec![];

        for i in 0..res_anno1.len() {
            if res_anno1[i] != 0 {
                col_o_year1.push(o_year[i]);
                col_anno1.push(res_anno1[i] as u32);
            }
            if res_anno2[i] != 0 {
                col_o_year2.push(o_year[i]);
                col_anno2.push(res_anno2[i] as u32);
            }
        }

        // the clean result relation
        let res_relation1 = Relation::new(vec![col_o_year1, col_anno1]);
        let res_relation2 = Relation::new(vec![col_o_year2, col_anno2]);

        println!("{:?}", res_relation1);
        println!("===========================");
        println!("{:?}", res_relation2);
    });
    });

    // thread_3 has: supplier, part
    let thread_3 = std::thread::spawn(move || {
        let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
        pool.install(|| {
        let self_id = process_id + N * 2;
        //### step 2: L.semijoin(P), P as sender
        // no need to group by because p_partkey is prime
        let xs_pts = points_from_num(p_partkey.clone());
        let xs_tree = SubProductTree::new_from_points_parallel(&xs_pts);

        let res_p_l_s1 = if intra {
            intra_psi_anno_sender_parallel(
                p_partkey.into_iter().map(|x| x as u64).collect(),
                p_anno.into_iter().map(|x| x as u64).collect(),
                &kzg_3_2nd,
                &mut stream_3_2,
                &xs_info_2,
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
                p_partkey.into_iter().map(|x| x as u64).collect(),
                p_anno.into_iter().map(|x| x as u64).collect(),
                &xs_tree,
                &mut stream_3_2,
                out_len_2nd,
                self_id,
                debug,
                ys_len_larger_2nd,
                sen_streams_2nd,
            )
        };
        //### step 3: L.semijoin(S) S is sender
        // no need to group by because s_suppkey is prime
        let xs_pts = points_from_num(s_suppkey.clone());
        let xs_tree = SubProductTree::new_from_points_parallel(&xs_pts);

        let res_s_l_s1_anno1 = if intra {
            intra_psi_anno_sender_parallel(
                s_suppkey.iter().map(|x| *x as u64).collect(),
                s_anno1.into_iter().map(|x| x as u64).collect(),
                &kzg_3_3rd,
                &mut stream_3_2,
                &xs_info_3,
                &xs_tree,
                debug,
                self_id,
                2,
                ys_len_larger_3rd,
                out_len_3rd,
                sen_streams_3rd,
            )
        } else {
            basic_psi_anno_sender_parallel(
                s_suppkey.iter().map(|x| *x as u64).collect(),
                s_anno1.into_iter().map(|x| x as u64).collect(),
                &xs_tree,
                &mut stream_3_2,
                out_len_3rd,
                self_id,
                debug,
                ys_len_larger_3rd,
                sen_streams_3rd,
            )
        };

        let res_s_l_s1_anno2 = if intra {
            intra_psi_anno_sender_parallel(
                s_suppkey.iter().map(|x| *x as u64).collect(),
                s_anno2.into_iter().map(|x| x as u64).collect(),
                &kzg_3_3rd,
                &mut stream_3_2,
                &xs_info_3,
                &xs_tree,
                debug,
                self_id,
                3,
                ys_len_larger_3rd,
                out_len_3rd,
                sen_streams_3rd_b,
            )
        } else {
            basic_psi_anno_sender_parallel(
                s_suppkey.into_iter().map(|x| x as u64).collect(),
                s_anno2.into_iter().map(|x| x as u64).collect(),
                &xs_tree,
                &mut stream_3_2,
                out_len_3rd,
                self_id,
                debug,
                ys_len_larger_3rd,
                sen_streams_3rd_b,
            )
        };
        // now compute p_anno * l_anno * s_anno_{1, 2}
        // consider lazy the vec_mul? will need extra obliPer5b

        let bytes = receive_data_by_stream(&mut rx_2_3);
        let l_anno_1: Vec<u128> = bincode::deserialize(&bytes).unwrap();

        let res_p_l_mul_s1 = vec_mul_1(
            &l_anno_1,
            &res_p_l_s1,
            &a1_l_len,
            &b1_l_len,
            &c1_l_len,
            &mut stream_3_2,
        );

        let res_p_s_l_mul_anno1_s1 = vec_mul_1(
            &res_p_l_mul_s1,
            &res_s_l_s1_anno1,
            &a1_l_len,
            &b1_l_len,
            &c1_l_len,
            &mut stream_3_2,
        );

        let res_p_s_l_mul_anno2_s1 = vec_mul_1(
            &res_p_l_mul_s1,
            &res_s_l_s1_anno2,
            &a1_l_len,
            &b1_l_len,
            &c1_l_len,
            &mut stream_3_2,
        );

        // send res_p_s_l_mul_anno1_s1, res_p_s_l_mul_anno2_s1 to thread_1
        let bytes = bincode::serialize(&(res_p_s_l_mul_anno1_s1, res_p_s_l_mul_anno2_s1)).unwrap();
        send_data_by_stream(&mut tx_3_1, &bytes, false);
        // tx_3_1
        //     .send((res_p_s_l_mul_anno1_s1, res_p_s_l_mul_anno2_s1))
        //     .unwrap();
    });
    });
    thread_1.join().unwrap();
    thread_2.join().unwrap();
    thread_3.join().unwrap();
    let t = timer.elapsed().real.as_micros() as u64;
    println!(" query processing time: {} ms", t / 1000);
    let intra_comm = crate::INTRA_SHARD_COMM.lock().unwrap();
    let cross_comm = crate::CROSS_SHARD_COMM.lock().unwrap();
    let consen_num = crate::CONSENSUS_NUM.lock().unwrap();
    crate::tpch::show_comm_cost(*intra_comm, *cross_comm, *consen_num);
}
