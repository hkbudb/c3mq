use c3mq::{
    tpch::{
        q10::wirte_q10_pre_compute_info,
        q14::wirte_q14_pre_compute_info,
        q18::wirte_q18_pre_compute_info,
        q3::wirte_q3_pre_compute_info,
        q4::wirte_q4_pre_compute_info,
        q8::wirte_q8_pre_compute_info,
    },
    utils::get_fixed_rng,
};
use c3mq::graph::{q1::write_graph_q1_pre_info, q2::write_graph_q2_pre_info};


pub fn write_pre_compute(path: &Path) {
    let chunk_size = 80;
    let mut rng = get_fixed_rng();
    let secret = Fr::rand(&mut rng);
    wirte_q3_pre_compute_info(path, secret, chunk_size);
    wirte_q4_pre_compute_info(path, secret, chunk_size);
    wirte_q8_pre_compute_info(path, secret, chunk_size);
    wirte_q10_pre_compute_info(path, secret, chunk_size);
    wirte_q14_pre_compute_info(path, secret, chunk_size);
    wirte_q18_pre_compute_info(path, secret, chunk_size);
    write_graph_q1_pre_info(0, secret);
    write_graph_q2_pre_info(0, secret);
    write_graph_q1_pre_info(1, secret);
    write_graph_q2_pre_info(1, secret);
    write_graph_q1_pre_info(2, secret);
    write_graph_q2_pre_info(2, secret);
    write_graph_q1_pre_info(3, secret);
    write_graph_q2_pre_info(3, secret);
}