// use crate::utils::dummy_tuple;

use std::collections::{HashMap, HashSet};

use rand::{distributions::Standard, prelude::Distribution, rngs::StdRng, Rng};
use serde::{Deserialize, Serialize};

use crate::{traits::FromPrimitive, utils::get_fixed_rng};

#[derive(Debug, Serialize, Deserialize)]
pub struct Relation {
    data: Vec<Vec<u32>>, // vec of cols
    size: usize,
}

impl Relation {
    pub fn new(data: Vec<Vec<u32>>) -> Self {
        let size = data[0].len();
        Self { data, size }
    }

    pub fn get_data(self) -> Vec<Vec<u32>> {
        self.data
    }

    pub fn get_col(&self, idx: usize) -> Vec<u32> {
        let col = self.data[idx].clone();
        col
    }

    pub fn get_size(&self) -> usize {
        self.size
    }

    pub fn sort_by(&mut self, idx: usize) {
        let data = &mut self.data;
        let pmt = get_sort_pmt::<u32>(&data[idx]);
        for i in 0..data.len() {
            data[i] = sort_by_pmt(&data[i], &pmt);
        }
    }

    pub fn remove_col(&mut self, idx: usize) {
        self.data.remove(idx);
    }

    pub fn local_add_agg(
        keys: &mut Vec<u32>,
        anno: &Vec<u32>,
        rng: &mut StdRng,
    ) -> (Vec<u32>, Vec<usize>) {
        let pmt = get_sort_pmt(keys);
        keys.sort();
        let mut sorted_anno: Vec<u32> = sort_by_pmt(anno, &pmt);

        let size = keys.len();
        for i in 0..size - 1 {
            if keys[i] == keys[i + 1] {
                sorted_anno[i + 1] += sorted_anno[i];
                sorted_anno[i] = 0;
                keys[i] = rng.gen::<u32>()
            }
        }
        (sorted_anno, pmt)
    }

    pub fn local_or_agg<T: Copy + PartialEq + FromPrimitive + Ord>(
        keys: &mut Vec<T>,
        anno: &Vec<T>,
        rng: &mut StdRng,
    ) -> (Vec<T>, Vec<usize>)
    where
        Standard: Distribution<T>,
    {
        let pmt = get_sort_pmt(keys);
        keys.sort();
        let mut sorted_anno: Vec<T> = sort_by_pmt(anno, &pmt);
        for i in 0..sorted_anno.len() {
            if sorted_anno[i] != T::from(0) {
                sorted_anno[i] = T::from(1);
            }
        }

        let size = keys.len();
        for i in 0..size - 1 {
            if keys[i] == keys[i + 1] {
                sorted_anno[i + 1] =
                    if sorted_anno[i] == T::from(1) || sorted_anno[i + 1] == T::from(1) {
                        T::from(1)
                    } else {
                        T::from(0)
                    };
                sorted_anno[i] = T::from(0);
                keys[i] = rng.gen::<T>()
            }
        }
        (sorted_anno, pmt)
    }

    pub fn prune(&mut self, n: usize) {
        for vec in &mut self.data {
            vec.truncate(self.size.saturating_sub(n));
        }
        self.size -= n;
    }

    // sort merge join
    pub fn local_join(&mut self, idx_self: usize, other: &mut Relation, idx_other: usize) -> Self {
        self.sort_by(idx_self);
        other.sort_by(idx_other);

        let mut ptr_1 = 0;
        let mut ptr_2 = 0;
        let mut res_data = vec![];
        let self_col_num = self.data.len();
        let other_col_num = other.data.len();
        for _ in 0..self_col_num + other_col_num {
            res_data.push(vec![]);
        }
        while ptr_1 < self.get_size() && ptr_2 < other.get_size() {
            if self.get_col(idx_self)[ptr_1] < other.get_col(idx_other)[ptr_2] {
                ptr_1 += 1;
            } else if self.get_col(idx_self)[ptr_1] > other.get_col(idx_other)[ptr_2] {
                ptr_2 += 1;
            } else {
                let mut left_cnt = ptr_1;
                for i in 0..self_col_num {
                    res_data[i].push(self.get_col(i)[left_cnt]);
                }
                for i in 0..other_col_num {
                    res_data[i + self_col_num].push(other.get_col(i)[ptr_2]);
                }
                while left_cnt < self.get_size() - 1 {
                    if self.get_col(idx_self)[left_cnt] != self.get_col(idx_self)[left_cnt + 1] {
                        break;
                    } else {
                        for i in 0..self_col_num {
                            res_data[i].push(self.get_col(i)[left_cnt + 1]);
                        }
                        for i in 0..other_col_num {
                            res_data[i + self_col_num].push(other.get_col(i)[ptr_2]);
                        }
                        left_cnt += 1;
                    }
                }
                ptr_2 += 1;
            }
        }

        Self::new(res_data)
    }

    pub fn group_by(&mut self, _idxes: Vec<usize>) {
        todo!()
    }
}

// return a permutation for sorting the vec
pub(crate) fn get_sort_pmt<T: FromPrimitive + Ord + Copy>(keys: &Vec<T>) -> Vec<usize> {
    let mut pmt: Vec<usize> = (0..keys.len()).collect();
    pmt.sort_by_key(|&i| keys[i]);
    pmt
}

pub(crate) fn sort_by_pmt<T: Copy>(vals: &Vec<T>, pmt: &Vec<usize>) -> Vec<T> {
    pmt.into_iter().map(|i| vals[*i]).collect()
}

pub(crate) fn get_ind(col: &Vec<u32>) -> Vec<u128> {
    let mut res = vec![];
    for i in 0..col.len() - 1 {
        if col[i] == col[i + 1] {
            res.push(1);
        } else {
            res.push(0);
        }
    }
    res
}

pub(crate) fn local_group_by_with_dummy<T: Copy + PartialEq>(key: &Vec<T>) -> Vec<T>
where
    Standard: Distribution<T>,
{
    let mut rng = get_fixed_rng();
    let size = key.len();
    let mut output = key.clone();
    for i in 0..size - 1 {
        if output[i] == output[i + 1] {
            output[i] = rng.gen::<T>();
        }
    }

    output
}

pub fn remove_duplicate(vec: &Vec<u32>) -> Vec<u32> {
    let mut seen = HashSet::new();
    let mut dedup_vec = Vec::new();
    for o in vec.iter() {
        if seen.insert(o) {
            dedup_vec.push(*o);
        }
    }
    dedup_vec
}

pub fn copy_duplicate<T: Clone>(
    original: &Vec<u32>,        // n ele, n >= m
    map: &HashMap<u32, (T, T)>, // m ele
) -> (Vec<T>, Vec<T>) {
    let mut vs_pp = vec![];
    let mut ys_hat = vec![];

    for o in original.iter() {
        let (v_pp, y_hat) = map.get(o).unwrap();
        vs_pp.push(v_pp.clone());
        ys_hat.push(y_hat.clone());
    }
    (vs_pp, ys_hat)
}

mod tests {
    #[test]
    fn test_sort() {
        use super::*;

        let mut keys = vec![1, 3, 2, 7, 5, 6];
        let annos = vec![11, 13, 12, 17, 15, 16];
        let pmt = get_sort_pmt::<u32>(&keys);
        keys.sort();
        let sorted_anno: Vec<u32> = sort_by_pmt(&annos, &pmt);

        assert_eq!(keys, vec![1, 2, 3, 5, 6, 7]);
        assert_eq!(sorted_anno, vec![11, 12, 13, 15, 16, 17]);
    }

    #[test]
    fn test_agg() {
        use super::*;
        use crate::utils::get_fixed_rng;

        let mut keys = vec![3, 2, 3, 3, 2, 1, 7, 4];
        let anno = vec![3, 2, 3, 3, 2, 1, 7, 4];
        let mut rng = get_fixed_rng();
        let (new_anno, _) = Relation::local_add_agg(&mut keys, &anno, &mut rng);
        assert_eq!(
            keys,
            vec![1, 2847912349, 2, 1625062324, 3915171720, 3, 4, 7]
        );
        assert_eq!(new_anno, vec![1, 0, 4, 0, 0, 9, 4, 7]);

        let mut keys: Vec<u32> = vec![3, 2, 3, 3, 2, 1, 7, 4];
        let anno = vec![3, 2, 3, 3, 2, 1, 7, 4];
        let mut rng = get_fixed_rng();
        let (new_anno, _) = Relation::local_or_agg(&mut keys, &anno, &mut rng);
        assert_eq!(
            keys,
            vec![1, 2847912349, 2, 1625062324, 3915171720, 3, 4, 7]
        );
        assert_eq!(new_anno, vec![1, 0, 1, 0, 0, 1, 1, 1]);
    }

    #[test]
    fn test_duplicate() {
        use super::*;

        let original = vec![1, 1, 2, 2, 3, 5, 4, 3, 2, 1, 4, 6];
        let vs_pp = vec![11, 12, 13, 15, 14, 16];
        let ys_hat = vec![21, 22, 23, 25, 24, 26];

        let dedup = remove_duplicate(&original);
        let mut map = HashMap::new();
        for (i, ele) in dedup.iter().enumerate() {
            map.insert(*ele, (vs_pp[i], ys_hat[i]));
        }

        let (new_vs_pp, new_ys_hat) = copy_duplicate::<i32>(&original, &map);

        let exp_vs_pp = vec![11, 11, 12, 12, 13, 15, 14, 13, 12, 11, 14, 16];
        let exp_ys_hat = vec![21, 21, 22, 22, 23, 25, 24, 23, 22, 21, 24, 26];

        assert_eq!(new_vs_pp, exp_vs_pp);
        assert_eq!(new_ys_hat, exp_ys_hat);
    }

    #[test]
    fn test_sort_by() {
        use super::*;
        let mut r = Relation::new(vec![
            vec![1, 3, 2, 5, 7, 4, 6],
            vec![11, 13, 12, 15, 17, 14, 16],
        ]);
        r.sort_by(0);
        println!("{:?}", r);
    }

    #[test]
    fn test_local_join() {
        use super::*;
        let mut r1 = Relation::new(vec![vec![1, 1, 2, 3], vec![11, 11, 12, 13]]);
        let mut r2 = Relation::new(vec![vec![0, 1, 3, 3, 4, 5], vec![10, 11, 13, 13, 14, 15]]);
        let r3 = &mut r1.local_join(0, &mut r2, 0);
        println!("{:?}", r3);
    }
}
