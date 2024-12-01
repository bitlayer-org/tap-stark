use bitcoin::taproot::LeafVersion::TapScript;
use bitcoin::taproot::NodeInfo;
use bitcoin::ScriptBuf;
use itertools::Itertools;

use super::complete_taptree::CompleteTaptree;

#[derive(Clone, Debug, Default)]
pub struct TreeBuilder {
    pub(crate) leaf_count: usize,
    pub(crate) leaf_indices: Vec<usize>,
    pub(crate) to_add_leaves: Vec<NodeInfo>,
}

impl TreeBuilder {
    pub fn new() -> Self {
        Self {
            leaf_count: 0,
            leaf_indices: Vec::new(),
            to_add_leaves: Vec::new(),
        }
    }

    pub fn add_leaf(&mut self, leaf_script: ScriptBuf) {
        self.leaf_count += 1;
        let leaf = NodeInfo::new_leaf_with_ver(leaf_script, TapScript);
        self.leaf_indices.push(self.leaf_count - 1);
        self.to_add_leaves.push(leaf);
    }

    /*
       The leaves_indices are postion info of merkle tree leaves in the taptree.
       When we building the taptree, it is much easier to work with a dict where the index is
       the taptree position and the element is the merkle tree postion.
       We flip the dict and save it to the leaf_indices.

    */
    pub fn build_tree(&mut self) -> CompleteTaptree {
        let leaf_count = self.to_add_leaves.len();
        assert!(is_power_of_two(leaf_count as u32));
        // this build tree now only working on the leaf-num equal to
        let mut working_nodes = self.to_add_leaves.clone();
        let mut t_idx_to_m_idx = self.leaf_indices.clone();

        while working_nodes.len() > 1 {
            // println!("working_nodes len:{:?}", working_nodes.len());
            //the tuple() method in itertool will drop the elements in Iter if the size is not enough to
            //generate a tuple, so we have to save the last node if the size of working node is odd.
            let mut reminder_node: Option<NodeInfo> = None;
            if working_nodes.len() % 2 == 1 {
                reminder_node = working_nodes.pop();
            }

            let node_tuples = working_nodes.into_iter().tuples();
            let mut todo: Vec<NodeInfo> = Vec::new();
            let mut a_start_idx = 0usize; // will be updated after finishing combining two nodes.

            for (a, b) in node_tuples {
                let a_leaf_size = a.leaf_nodes().len();
                let a_end_idx = a_start_idx + a_leaf_size;
                let b_start_idx = a_end_idx;
                let b_leaf_size = b.leaf_nodes().len();
                let b_end_idx = b_start_idx + b_leaf_size;
                let (ret_node, left_first) = NodeInfo::combine_with_order(a, b).unwrap();

                todo.push(ret_node);

                //swap index when !left_first
                if !left_first {
                    let mut temp_a_leaf_indices = vec![0usize; a_leaf_size];
                    temp_a_leaf_indices
                        .as_mut_slice()
                        .copy_from_slice(&t_idx_to_m_idx[a_start_idx..a_end_idx]);

                    let mut temp_b_leaf_indices = vec![0usize; b_leaf_size];
                    temp_b_leaf_indices
                        .as_mut_slice()
                        .copy_from_slice(&t_idx_to_m_idx[b_start_idx..b_end_idx]);
                    temp_b_leaf_indices.append(&mut temp_a_leaf_indices);
                    t_idx_to_m_idx[a_start_idx..b_end_idx]
                        .copy_from_slice(&temp_b_leaf_indices.as_slice());
                }
                a_start_idx += a_leaf_size + b_leaf_size;
            }
            working_nodes = todo;
            todo = Vec::new();
        }
        CompleteTaptree::new(
            working_nodes.into_iter().next().unwrap(),
            leaf_count,
            reverse_idx_dict(&t_idx_to_m_idx),
        )
    }
}

pub(crate) fn reverse_idx_dict(idx_dict: &Vec<usize>) -> Vec<usize> {
    let mut ret_vec = vec![0usize; idx_dict.len()];
    for (idx, pos) in idx_dict.iter().enumerate() {
        ret_vec[*pos] = idx;
    }
    ret_vec
}

fn is_power_of_two(n: u32) -> bool {
    n > 0 && (n & (n - 1)) == 0
}
