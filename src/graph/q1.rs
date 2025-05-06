use std::{fs::File, io::{self, Write}, os::unix::net::UnixStream, path::Path};

use ark_bls12_381::{Bls12_381, Fr};
use ark_ec::pairing::Pairing;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use crypto_hash::{digest, Algorithm};
use rayon::ThreadPoolBuilder;
use ark_std::UniformRand;

use crate::{graph::{load_data, BTC_DATA_PATH, GRQC_DATA_PATH, P2P_DATA_PATH, WIKI_DATA_PATH}, psi::{basic_psi_anno_receiver_parallel, basic_psi_anno_sender_parallel, batch_psi_anno_receiver_parallel, batch_psi_anno_sender_parallel, intra_psi_anno_receiver_parallel, intra_psi_anno_sender_parallel, setup_kzg, subproduct_tree::SubProductTree, utils::{load_beaver_truples, obtain_beaver_tripes_by, receive_data_by_stream, send_data_by_stream, vec_mul_1, vec_mul_2}}, relation::{remove_duplicate, Relation}, tpch::PreInfo, utils::{combine_share, get_fixed_rng, obtain_unix_streams, points_from_num, run_consensus}, N, THREAD_NUM};


pub fn write_graph_q1_pre_info(which_dataset: u8, secret: <Bls12_381 as Pairing>::ScalarField) {
    let (table, r1_anno) = load_data(which_dataset);
    let mut r1_to = table.get_col(1);
    let r2_from = table.get_col(0);
    let r2_to = table.get_col(1);
    let mut r3_from = table.get_col(0);
    let r3_anno = r1_anno.clone();

    let mut pre_infos = vec![];

    // first psi, xs: r1_to, ys: r2_from
    // local group by
    let mut rng = get_fixed_rng();
    let _ = Relation::local_add_agg(&mut r1_to, &r1_anno, &mut rng);
    let n_psi = table.get_size();
    let max_deg = n_psi - 1;
    let mut kzg = setup_kzg(max_deg);
    kzg.setup(secret);
    // remove duplicates in ys
    let ys = remove_duplicate(&r2_from);
    let xs_pts = points_from_num(r1_to);
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

    // second psi, xs: r3_from, ys: r2_to
    // local group by
    let mut rng = get_fixed_rng();
    let _ = Relation::local_add_agg(&mut r3_from, &r3_anno, &mut rng);
    let n_psi = table.get_size();
    let max_deg = n_psi - 1;
    let mut kzg = setup_kzg(max_deg);
    kzg.setup(secret);
    // remove duplicates in ys
    let ys = remove_duplicate(&r2_to);
    let xs_pts = points_from_num(r3_from);
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

    let mut data_bytes: Vec<u8> = vec![];
    pre_infos.serialize_uncompressed(&mut data_bytes).unwrap();

    println!("writing pre-computed info to files...");

    let file_path = if which_dataset == 0 {
        Path::new(GRQC_DATA_PATH).join("q1_pre_info.json")
    } else if which_dataset == 1 {
        Path::new(BTC_DATA_PATH).join("q1_pre_info.json")
    } else if which_dataset == 2 {
        Path::new(P2P_DATA_PATH).join("q1_pre_info.json")
    } else if which_dataset == 3 {
        Path::new(WIKI_DATA_PATH).join("q1_pre_info.json")
    } else {
        panic!("invalid dataset option, please choose {{0, 1, 2, 3}}");
    };
    
    
    if std::fs::metadata(file_path.clone()).is_ok() {
        std::fs::remove_file(&file_path).unwrap();
    }
    let mut file = File::create(&file_path).unwrap();
    file.write_all(&data_bytes).unwrap();
}

pub(crate) fn load_graph_q1_pre_info(which_dataset: u8) -> Vec<u8> {
    let file_path = if which_dataset == 0 {
        Path::new(GRQC_DATA_PATH).join("q1_pre_info.json")
    } else if which_dataset == 1 {
        Path::new(BTC_DATA_PATH).join("q1_pre_info.json")
    } else if which_dataset == 2 {
        Path::new(P2P_DATA_PATH).join("q1_pre_info.json")
    } else if which_dataset == 3 {
        Path::new(WIKI_DATA_PATH).join("q1_pre_info.json")
    } else {
        panic!("invalid dataset option, please choose {{0, 1, 2, 3}}");
    };
    let mut file = File::open(file_path).unwrap();
    let mut buffer = Vec::new();
    io::Read::read_to_end(&mut file, &mut buffer).unwrap();
    buffer
}

pub fn exe_graph_q1_batch(process_id: u16, debug: bool, query_num: usize, which_dataset: u8) {
    println!("loading dataset...");
    let (table, r1_anno) = load_data(which_dataset);
    let mut r1_to = table.get_col(1);
    let r2_from = table.get_col(0);
    let r2_to = table.get_col(1);
    let mut r3_from = table.get_col(0);
    let r3_anno = r1_anno.clone();

    let out_len = r1_anno.len();
    let ys_len_larger = false;
    let triples = load_beaver_truples();
    let (a1, a2, b1, b2, c1, c2) = obtain_beaver_tripes_by(out_len, triples);

    // load pre_info
    println!("loading pre-computed information...");
    let bytes = load_graph_q1_pre_info(which_dataset);
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

    println!("pre-computing some info...");
    let ys_1st_no_dup = remove_duplicate(&r2_from);
    let ys_pts_1st = points_from_num(ys_1st_no_dup.clone());
    let ys_tree_1st = SubProductTree::new_from_points_parallel(&ys_pts_1st);

    let ys_2nd_no_dup = remove_duplicate(&r2_to);
    let ys_pts_2nd = points_from_num(ys_2nd_no_dup.clone());
    let ys_tree_2nd = SubProductTree::new_from_points_parallel(&ys_pts_2nd);

    println!("setup...");
    let (sen_streams_1st, rec_streams_1st) = obtain_unix_streams(THREAD_NUM);
    let (sen_streams_2nd, rec_streams_2nd) = obtain_unix_streams(THREAD_NUM);
    let (mut stream_1_2, mut stream_2_1) = UnixStream::pair().unwrap();
    let (mut stream_3_2, mut stream_2_3) = UnixStream::pair().unwrap();
    let (mut stream_1_3, mut stream_3_1) = UnixStream::pair().unwrap();

    let mut rng = get_fixed_rng();
    let secret = Fr::rand(&mut rng);
    let n_1st_psi = r1_to.len();
    let max_deg_1st = n_1st_psi - 1;
    let n_2nd_psi = r3_from.len();
    let max_deg_2nd = n_2nd_psi - 1;

    // thread_1
    let mut kzg_1 = setup_kzg(max_deg_1st);
    kzg_1.setup(secret);

    // thread_2
    let mut kzg_2_1st = setup_kzg(max_deg_1st);
    kzg_2_1st.setup(secret);
    let mut kzg_2_2nd = setup_kzg(max_deg_2nd);
    kzg_2_2nd.setup(secret);

    // thread_3
    let mut kzg_3 = setup_kzg(max_deg_2nd);
    kzg_3.setup(secret);

    let timer = howlong::ProcessCPUTimer::new();
    let thread_1 = std::thread::spawn(move || {
        let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
        pool.install(|| {
            let self_id = process_id;
            // first psi sender
            let mut rng = get_fixed_rng();
            let (r1_anno_sorted, _) = Relation::local_add_agg(&mut r1_to, &r1_anno, &mut rng);
            let xs_pts = points_from_num(r1_to.clone());
            let xs_tree = SubProductTree::new_from_points_parallel(&xs_pts);
            let share1s_1st = batch_psi_anno_sender_parallel(
                vec![r1_to.into_iter().map(|x| x as u64).collect(); query_num],
                vec![r1_anno_sorted.into_iter().map(|x| x as u64).collect(); query_num],
                &kzg_1,
                &mut stream_1_2,
                &vec![xs_info_1; query_num],
                &vec![xs_tree; query_num],
                debug,
                self_id,
                ys_len_larger,
                out_len,
                sen_streams_1st,
            );

            // consensus on share1s_1st before sending to thread_3
            let bytes = bincode::serialize(&share1s_1st).unwrap();
            let dig = digest(Algorithm::SHA256, &bytes);
            if !debug {
                run_consensus(dig, self_id);
            }

            send_data_by_stream(&mut stream_1_3, &bytes, false);
        });
    });

    let thread_2 = std::thread::spawn(move || {
        let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
        pool.install(|| {
            let self_id = process_id + N * 2;
            
            // first psi receiver
            let share2s_1st = batch_psi_anno_receiver_parallel(
                &vec![r2_from.clone(); query_num],
                true,
                vec![ys_1st_no_dup.clone().into_iter().map(|x| x as u64).collect(); query_num],
                &kzg_2_1st,
                &mut stream_2_1,
                &vec![ys_tree_1st; query_num],
                &vec![veri_info_1; query_num],
                vec![z_commit_1; query_num],
                self_id,
                ys_len_larger,
                debug,
                rec_streams_1st,
            );

            // second psi receiver
            let share2s_2nd = batch_psi_anno_receiver_parallel(
                &vec![r2_to.clone(); query_num],
                true,
                vec![ys_2nd_no_dup.clone().into_iter().map(|x| x as u64).collect(); query_num],
                &kzg_2_2nd,
                &mut stream_2_3,
                &vec![ys_tree_2nd; query_num],
                &vec![veri_info_2; query_num],
                vec![z_commit_2; query_num],
                self_id,
                ys_len_larger,
                debug,
                rec_streams_2nd,
            );

            let res2s: Vec<Vec<u128>> = share2s_1st.iter()
            .zip(share2s_2nd.iter())
            .map(|(share2_1st, share2_2nd)| {
                vec_mul_2(
                    &share2_1st,
                    &share2_2nd,
                    &a2,
                    &b2,
                    &c2,
                    &mut stream_2_3,
                )
            })
            .collect();

            let bytes = receive_data_by_stream(&mut stream_2_3);
            let res1s: Vec<Vec<u128>> = bincode::deserialize(&bytes).unwrap();
            let reses: Vec<Vec<u128>> = res1s.into_iter().zip(res2s.into_iter()).map(|(res1, res2)| {
                combine_share(res1, res2)
            }).collect();

            for res in reses {
                let mut col_from = vec![];
                let mut col_to = vec![];
                let mut col_anno = vec![];
                for i in 0..res.len() {
                    if res[i] != 0 {
                        col_from.push(r2_from[i]);
                        col_to.push(r2_to[i]);
                        col_anno.push(res[i] as u32);
                    }
                }
                let _res_relation = Relation::new(vec![col_from, col_to, col_anno]);
                break;
            }
        });
    });

    let thread_3 = std::thread::spawn(move || {
        let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
        pool.install(|| {
            let self_id = process_id + N * 1;
            
            // second psi sender 
            let mut rng = get_fixed_rng();
            let (r3_anno_sorted, _) = Relation::local_add_agg(&mut r3_from, &r3_anno, &mut rng);
            let xs_pts = points_from_num(r3_from.clone());
            let xs_tree = SubProductTree::new_from_points_parallel(&xs_pts);
            let share1s_2nd = batch_psi_anno_sender_parallel(
                vec![r3_from.into_iter().map(|x| x as u64).collect(); query_num],
                vec![r3_anno_sorted.into_iter().map(|x| x as u64).collect(); query_num],
                &kzg_3,
                &mut stream_3_2,
                &vec![xs_info_2; query_num],
                &vec![xs_tree; query_num],
                debug,
                self_id,
                ys_len_larger,
                out_len,
                sen_streams_2nd,
            );

            // consensus on share1s_2nd
            let bytes = bincode::serialize(&share1s_2nd).unwrap();
            let dig = digest(Algorithm::SHA256, &bytes);
            if !debug {
                run_consensus(dig, self_id);
            }

            let bytes = receive_data_by_stream(&mut stream_3_1);
            let share1s_1st: Vec<Vec<u128>> = bincode::deserialize(&bytes).unwrap();

            let res1s: Vec<Vec<u128>> = share1s_1st.iter().zip(share1s_2nd.iter()).map(|(share1_1st, share1_2nd)| {
                vec_mul_1(
                    share1_1st,
                    share1_2nd,
                    &a1,
                    &b1,
                    &c1,
                    &mut stream_3_2,
                )
            }).collect();

            // reveal res1s to thread 2
            let bytes = bincode::serialize(&res1s).unwrap();
            send_data_by_stream(&mut stream_3_2, &bytes, false);
        });
    });

    thread_1.join().unwrap();
    thread_2.join().unwrap();
    thread_3.join().unwrap();
    let t = timer.elapsed().real.as_micros() as u64;
    println!("query processing time: {} ms", t / 1000);
    let intra_comm = crate::INTRA_SHARD_COMM.lock().unwrap();
    let cross_comm = crate::CROSS_SHARD_COMM.lock().unwrap();
    let consen_num = crate::CONSENSUS_NUM.lock().unwrap();
    crate::tpch::show_comm_cost(*intra_comm, *cross_comm, *consen_num);


}

pub fn exe_graph_q1_single(process_id: u16, debug: bool, intra: bool, which_dataset: u8) {
    println!("loading dataset...");
    let (table, r1_anno) = load_data(which_dataset);
    let mut r1_to = table.get_col(1);
    let r2_from = table.get_col(0);
    let r2_to = table.get_col(1);
    let mut r3_from = table.get_col(0);
    let r3_anno = r1_anno.clone();

    let out_len = r1_anno.len();
    let ys_len_larger = false;

    let triples = load_beaver_truples();
    let (a1, a2, b1, b2, c1, c2) = obtain_beaver_tripes_by(out_len, triples);

    // load pre_info
    println!("loading pre-computed information...");
    let bytes = load_graph_q1_pre_info(which_dataset);
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

    println!("pre-computing some info...");
    let ys_pts_1st_baseline = points_from_num(r2_from.clone());
    let ys_tree_1st_baseline = SubProductTree::new_from_points_parallel(&ys_pts_1st_baseline);
    let ys_1st_no_dup = remove_duplicate(&r2_from);
    let ys_pts_1st = points_from_num(ys_1st_no_dup.clone());
    let ys_tree_1st = SubProductTree::new_from_points_parallel(&ys_pts_1st);

    let ys_pts_2nd_baseline = points_from_num(r2_to.clone());
    let ys_tree_2nd_baseline = SubProductTree::new_from_points_parallel(&ys_pts_2nd_baseline);
    let ys_2nd_no_dup = remove_duplicate(&r2_to);
    let ys_pts_2nd = points_from_num(ys_2nd_no_dup.clone());
    let ys_tree_2nd = SubProductTree::new_from_points_parallel(&ys_pts_2nd);

    println!("setup...");
    let (sen_streams_1st, rec_streams_1st) = obtain_unix_streams(THREAD_NUM);
    let (sen_streams_2nd, rec_streams_2nd) = obtain_unix_streams(THREAD_NUM);
    let (mut stream_1_2, mut stream_2_1) = UnixStream::pair().unwrap();
    let (mut stream_3_2, mut stream_2_3) = UnixStream::pair().unwrap();
    let (mut stream_1_3, mut stream_3_1) = UnixStream::pair().unwrap();

    let mut rng = get_fixed_rng();
    let secret = Fr::rand(&mut rng);
    let n_1st_psi = r1_to.len();
    let max_deg_1st = n_1st_psi - 1;
    let n_2nd_psi = r3_from.len();
    let max_deg_2nd = n_2nd_psi - 1;

    // thread_1
    let mut kzg_1 = setup_kzg(max_deg_1st);
    kzg_1.setup(secret);

    // thread_2
    let mut kzg_2_1st = setup_kzg(max_deg_1st);
    kzg_2_1st.setup(secret);
    let mut kzg_2_2nd = setup_kzg(max_deg_2nd);
    kzg_2_2nd.setup(secret);

    // thread_3
    let mut kzg_3 = setup_kzg(max_deg_2nd);
    kzg_3.setup(secret);

    let timer = howlong::ProcessCPUTimer::new();
    let thread_1 = std::thread::spawn(move || {
        let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
        pool.install(|| {
            let self_id = process_id;
            // first psi sender
            let mut rng = get_fixed_rng();
            let (r1_anno_sorted, _) = Relation::local_add_agg(&mut r1_to, &r1_anno, &mut rng);
            let xs_pts = points_from_num(r1_to.clone());
            let xs_tree = SubProductTree::new_from_points_parallel(&xs_pts);
            let share1_1st = if intra {
                intra_psi_anno_sender_parallel(
                    r1_to.into_iter().map(|x| x as u64).collect(),
                    r1_anno_sorted.into_iter().map(|x| x as u64).collect(),
                    &kzg_1,
                    &mut stream_1_2,
                    &xs_info_1,
                    &xs_tree,
                    debug,
                    self_id,
                    0,
                    ys_len_larger,
                    out_len,
                    sen_streams_1st,
                )
            } else {
                basic_psi_anno_sender_parallel(
                    r1_to.into_iter().map(|x| x as u64).collect(),
                    r1_anno_sorted.into_iter().map(|x| x as u64).collect(),
                    &xs_tree,
                    &mut stream_1_2,
                    out_len,
                    self_id,
                    debug,
                    ys_len_larger,
                    sen_streams_1st,
                )
            };
            // consensus on share1_1st before sending to thread_3
            let bytes = bincode::serialize(&share1_1st).unwrap();
            let dig = digest(Algorithm::SHA256, &bytes);
            if !debug {
                run_consensus(dig, self_id);
            }

            // send share1_1st to thread 3
            send_data_by_stream(&mut stream_1_3, &bytes, false);
        });
    });

    let thread_2 = std::thread::spawn(move || {
        let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
        pool.install(|| {
            let self_id = process_id + N * 2;
            
            // first psi receiver
            let share2_1st = if intra {
                intra_psi_anno_receiver_parallel(
                    &r2_from,
                    true,
                    ys_1st_no_dup.clone().into_iter().map(|x| x as u64).collect(),
                    &kzg_2_1st,
                    &mut stream_2_1,
                    &ys_tree_1st,
                    &vec![veri_info_1],
                    vec![z_commit_1],
                    self_id,
                    0,
                    ys_len_larger,
                    debug,
                    false,
                    rec_streams_1st,
                )
            } else {
                basic_psi_anno_receiver_parallel(
                    r2_from.clone().into_iter().map(|x| x as u64).collect(),
                    &mut stream_2_1,
                    &ys_tree_1st_baseline,
                    self_id,
                    debug,
                    ys_len_larger,
                    rec_streams_1st,
                )
            };

            // second psi receiver
            let share2_2nd = if intra {
                intra_psi_anno_receiver_parallel(
                    &r2_to,
                    true,
                    ys_2nd_no_dup.clone().into_iter().map(|x| x as u64).collect(),
                    &kzg_2_2nd,
                    &mut stream_2_3,
                    &ys_tree_2nd,
                    &vec![veri_info_2],
                    vec![z_commit_2],
                    self_id,
                    1,
                    ys_len_larger,
                    debug,
                    false,
                    rec_streams_2nd,
                )
            } else {
                basic_psi_anno_receiver_parallel(
                    r2_to.clone().into_iter().map(|x| x as u64).collect(),
                    &mut stream_2_3,
                    &ys_tree_2nd_baseline,
                    self_id,
                    debug,
                    ys_len_larger,
                    rec_streams_2nd,
                )
            };

            let res2 = vec_mul_2(
                &share2_1st,
                &share2_2nd,
                &a2,
                &b2,
                &c2,
                &mut stream_2_3,
            );

            let bytes = receive_data_by_stream(&mut stream_2_3);
            let res1: Vec<u128> = bincode::deserialize(&bytes).unwrap();
            let res = combine_share(res1, res2);

            // keep non-zero-anno tuples
            let mut col_from = vec![];
            let mut col_to = vec![];
            let mut col_anno = vec![];
            for i in 0..res.len() {
                if res[i] != 0 {
                    col_from.push(r2_from[i]);
                    col_to.push(r2_to[i]);
                    col_anno.push(res[i] as u32);
                }
            }
            // the clean result relation
            let _res_relation = Relation::new(vec![col_from, col_to, col_anno]);
            // println!("{:?}", res_relation);

        });
    });

    let thread_3 = std::thread::spawn(move || {
        let pool = ThreadPoolBuilder::new().num_threads(THREAD_NUM).build().unwrap();
        pool.install(|| {
            let self_id = process_id + N * 1;
            
            // second psi sender 
            let mut rng = get_fixed_rng();
            let (r3_anno_sorted, _) = Relation::local_add_agg(&mut r3_from, &r3_anno, &mut rng);
            let xs_pts = points_from_num(r3_from.clone());
            let xs_tree = SubProductTree::new_from_points_parallel(&xs_pts);
            let share1_2nd = if intra {
                intra_psi_anno_sender_parallel(
                    r3_from.into_iter().map(|x| x as u64).collect(),
                    r3_anno_sorted.into_iter().map(|x| x as u64).collect(),
                    &kzg_3,
                    &mut stream_3_2,
                    &xs_info_2,
                    &xs_tree,
                    debug,
                    self_id,
                    1,
                    ys_len_larger,
                    out_len,
                    sen_streams_2nd,
                )
            } else {
                basic_psi_anno_sender_parallel(
                    r3_from.into_iter().map(|x| x as u64).collect(),
                    r3_anno_sorted.into_iter().map(|x| x as u64).collect(),
                    &xs_tree,
                    &mut stream_3_2,
                    out_len,
                    self_id,
                    debug,
                    ys_len_larger,
                    sen_streams_2nd,
                )
            };
            // consensus on share1_2nd 
            let bytes = bincode::serialize(&share1_2nd).unwrap();
            let dig = digest(Algorithm::SHA256, &bytes);
            if !debug {
                run_consensus(dig, self_id);
            }

            let bytes = receive_data_by_stream(&mut stream_3_1);
            let share1_1st: Vec<u128> = bincode::deserialize(&bytes).unwrap();

            let res1 = vec_mul_1(
                &share1_1st,
                &share1_2nd,
                &a1,
                &b1,
                &c1,
                &mut stream_3_2,
            );

            // reveal res1 to thread 2
            let bytes = bincode::serialize(&res1).unwrap();
            send_data_by_stream(&mut stream_3_2, &bytes, false);
        });
    });

    thread_1.join().unwrap();
    thread_2.join().unwrap();
    thread_3.join().unwrap();
    let t = timer.elapsed().real.as_micros() as u64;
    println!("query processing time: {} ms", t / 1000);
    let intra_comm = crate::INTRA_SHARD_COMM.lock().unwrap();
    let cross_comm = crate::CROSS_SHARD_COMM.lock().unwrap();
    let consen_num = crate::CONSENSUS_NUM.lock().unwrap();
    crate::tpch::show_comm_cost(*intra_comm, *cross_comm, *consen_num);
}


