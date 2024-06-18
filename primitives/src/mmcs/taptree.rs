use core::ops::{Deref, DerefMut};
use core::{mem, usize};
use std::cmp::Reverse;

use bitcoin::taproot::LeafVersion::TapScript;
use bitcoin::taproot::{LeafNode, LeafNodes, NodeInfo, TaprootMerkleBranch};
use bitcoin::{ScriptBuf, TapNodeHash};
use itertools::{Chunk, Itertools};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_util::{log2_ceil_usize, log2_strict_usize, reverse_slice_index_bits};
use scripts::secret_generator::ThreadSecretGen;

use super::error::BfError;
use super::point::PointsLeaf;
use crate::field::BfField;

pub fn combine_two_nodes(a: NodeInfo, b: NodeInfo) -> Result<(NodeInfo, bool), BfError> {
    let parent = NodeInfo::combine_with_order(a, b)?;
    Ok(parent)
}
use bitcoin::ScriptBuf as Script;
use bitcoin_script::{define_pushable, script};
use scripts::bit_comm::bit_comm::BitCommitment;
define_pushable!();

pub struct EvaluationLeaf<const NUM_POLY: usize, F: BfField> {
    leaf_index: usize,
    x: F,
    x_commitment: BitCommitment<F>,
    neg_x_commitment: BitCommitment<F>,
    evaluations: Vec<F>,
    evaluations_commitments: Vec<BitCommitment<F>>,
}

impl<const NUM_POLY: usize, F: BfField> EvaluationLeaf<NUM_POLY, F> {
    pub fn new(leaf_index: usize, x: F, evaluations: Vec<F>) -> Self {
        assert_eq!(evaluations.len(), NUM_POLY);

        let x_commitment = BitCommitment::new::<ThreadSecretGen>(x);
        let neg_x_commitment = BitCommitment::new::<ThreadSecretGen>(F::field_mod() - x);
        let mut evaluations_commitments = Vec::new();
        for i in 0..NUM_POLY {
            evaluations_commitments.push(BitCommitment::new::<ThreadSecretGen>(evaluations[i]));
        }

        Self {
            leaf_index,
            x,
            x_commitment,
            neg_x_commitment,
            evaluations,
            evaluations_commitments,
        }
    }

    pub fn leaf_script(&self) -> Script {
        // equal to x script
        let scripts = script! {
            { self.x_commitment.commitments[0].checksig_verify_script() }
            { self.x_commitment.commitments[0].commit_u32_as_4bytes_script() }
            // todo: calculate to equal to -x
            for i in 0..NUM_POLY{
                { self.evaluations_commitments[NUM_POLY-1-i].commitments[0].checksig_verify_script() }
                { self.evaluations_commitments[NUM_POLY-1-i].commitments[0].commit_u32_as_4bytes_script() }
            }
            OP_1
        };

        scripts
    }

    pub fn two_point_leaf_script(&self) -> Script {
        // equal to x script
        let scripts = script! {
            { self.x_commitment.commitments[0].checksig_verify_script() }
            { self.x_commitment.commitments[0].commit_u32_as_4bytes_script() }
            { self.neg_x_commitment.commitments[0].checksig_verify_script() }
            { self.neg_x_commitment.commitments[0].commit_u32_as_4bytes_script() }
            for i in 0..NUM_POLY{
                { self.evaluations_commitments[NUM_POLY-1-i].commitments[0].checksig_verify_script() }
                { self.evaluations_commitments[NUM_POLY-1-i].commitments[0].commit_u32_as_4bytes_script() }
            }
            OP_1
        };
        scripts
    }
}

// Todo: use &[F] to replace Vec<F>
pub fn construct_evaluation_leaf_script<const NUM_POLY: usize, F: BfField>(
    leaf_index: usize,
    x: F,
    y_s: Vec<F>,
) -> Result<ScriptBuf, BfError> {
    let leaf_script: EvaluationLeaf<NUM_POLY, F> = EvaluationLeaf::new(leaf_index, x, y_s);
    let script = leaf_script.leaf_script();
    Ok(script)
}

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub struct GlobalTree {}

// =============== Polycommitment Tree ===============

#[derive(Clone, Debug)]
pub struct PolyCommitTree<F: BfField, const NUM_POLY: usize> {
    pub tree: BasicTree<NUM_POLY>,
    pub points_leafs: Vec<PointsLeaf<F>>,
    pub leaves: Vec<RowMajorMatrix<F>>,
}

impl<const NUM_POLY: usize, F: BfField> PolyCommitTree<F, NUM_POLY> {
    pub fn new() -> Self {
        Self {
            tree: BasicTree::<NUM_POLY>::new(),
            points_leafs: Vec::new(),
            leaves: Vec::new(),
        }
    }

    pub fn commit_points(&mut self, leaves: Vec<RowMajorMatrix<F>>) {
        self.leaves = leaves.clone();
        //evaluations sorted by height
        let mut leaves_largest_first = leaves
            .iter()
            .sorted_by_key(|l| Reverse(l.height()))
            .peekable();
        let max_height = leaves_largest_first.peek().unwrap().height();
        let log_max_height = log2_ceil_usize(max_height);
        //println!("max height:{:?}", max_height);
        let mut tree_builder = TreeBuilder::<NUM_POLY>::new();

        let mut leaf_xs = vec![vec![]; max_height];
        let mut leaf_ys = vec![vec![]; max_height];

        for log_height in (0..log_max_height + 1).rev() {
            let matrices = leaves_largest_first
                .peeking_take_while(|m| log2_ceil_usize(m.height()) == log_height)
                .collect_vec();
            if matrices.len() != 0 {
                let curr_height = matrices[0].height();
                for matrix in matrices.iter() {
                    let width = matrix.width();
                    for index in 0..curr_height {
                        //find which leaf to store
                        let curr_index = index << (log_max_height - log_height);
                        let next_index = (index + 1) << (log_max_height - log_height);
                        for i in 0..width {
                            for leaf_index in curr_index..next_index {
                                //default x to F::one(), may be we will delete x in struct point soon
                                leaf_xs[leaf_index].push(F::one());
                                leaf_ys[leaf_index].push(matrix.values[index * matrix.width() + i]);
                            }
                        }
                    }
                }
            }
        }

        for index in 0..max_height {
            if leaf_ys[index].len() != 0 {
                println!("index:{:?}, ys:{:?}", index, leaf_ys[index]);
                let leaf = PointsLeaf::new(
         index,
                    &leaf_xs[index],
                    &leaf_ys[index],
                );
                self.add_leaf(&mut tree_builder, &leaf);
            }
        }
        self.tree = tree_builder.build_tree();
    }

    pub fn root(&self) -> &NodeInfo {
        self.tree.root()
    }

    pub fn get_tapleaf(&self, index: usize) -> Option<&LeafNode> {
        self.tree.get_tapleaf(index)
    }

    pub fn verify_inclusion_by_index(&self, index: usize) -> bool {
        self.tree.verify_inclusion_by_index(index)
    }

    pub fn add_leaf(&mut self, builder: &mut TreeBuilder<NUM_POLY>, leaf: &PointsLeaf<F>) {
        self.points_leafs.push(leaf.clone());

        builder.add_leaf(leaf.recover_points_euqal_to_commited_point());
    }

    pub fn get_points_leafs(&self) -> &[PointsLeaf<F>] {
        &self.points_leafs
    }

    pub fn get_points_leaf(&self, index: usize) -> &PointsLeaf<F> {
        &self.points_leafs[index]
    }

    pub fn get_matrix_widths(&self) -> Vec<usize> {
        self.leaves.iter().map(|m| m.width()).collect()
    }
}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub struct BasicTree<const NUM_POLY: usize> {
    pub root_node: Option<NodeInfo>,
    leaf_count: usize,
    leaf_indices: Vec<usize>,
}

pub struct TreeBuilder<const NUM_POLY: usize> {
    leaf_count: usize,
    leaf_indices: Vec<usize>,
    to_add_leaves: Vec<NodeInfo>,
}

impl<const NUM_POLY: usize> TreeBuilder<NUM_POLY> {
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
    pub fn build_tree(&mut self) -> BasicTree<NUM_POLY> {
        let mut working_nodes = self.to_add_leaves.clone();
        let mut t_idx_to_m_idx = self.leaf_indices.clone();

        while working_nodes.len() > 1 {
            println!("working_nodes len:{:?}", working_nodes.len());
            //the tuple() method in itertool will drop the elements in Iter if the size is not enough to
            //generate a tuple, so we have to save the last node if the size of working node is odd.
            let mut reminder_node: Option<NodeInfo> = None;
            if working_nodes.len() % 2 == 1 {
                reminder_node = working_nodes.pop();
            }

            let mut node_tuples = working_nodes.into_iter().tuples();
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
        BasicTree {
            root_node: Some(working_nodes.into_iter().next().unwrap()),
            leaf_count: self.leaf_count,
            leaf_indices: reverse_idx_dict(&t_idx_to_m_idx),
        }
    }
}

fn reverse_idx_dict(idx_dict: &Vec<usize>) -> Vec<usize> {
    let mut ret_vec = vec![0usize; idx_dict.len()];
    for (idx, pos) in idx_dict.iter().enumerate() {
        ret_vec[*pos] = idx;
    }
    ret_vec
}

impl<const NUM_POLY: usize> BasicTree<NUM_POLY> {
    pub fn new() -> Self {
        Self {
            root_node: None,
            leaf_count: 0,
            leaf_indices: Vec::new(),
        }
    }

    pub fn root(&self) -> &NodeInfo {
        let root = self.root_node.as_ref().unwrap();
        root
    }

    // This function only support combine trees with same depth
    pub fn combine_tree(a: Self, b: Self) -> Self {
        // perserve indices map before combining two trees.
        let mut a_leaf_indices = a.leaf_indices.clone();
        let mut b_leaf_indices = b.leaf_indices.clone();

        let (combined_tree, noswap) =
            combine_two_nodes(a.root_node.unwrap(), b.root_node.unwrap()).unwrap();

        let mut a_t_idx_to_m_idx = reverse_idx_dict(&a_leaf_indices);
        let mut b_t_idx_to_m_idx = reverse_idx_dict(&b_leaf_indices);

        let t_idx_to_m_idx = match noswap {
            true => {
                for b_m_idx in b_t_idx_to_m_idx.iter() {
                    a_t_idx_to_m_idx.push(*b_m_idx);
                }
                a_t_idx_to_m_idx
            }
            false => {
                for a_m_idx in a_t_idx_to_m_idx.iter() {
                    b_t_idx_to_m_idx.push(*a_m_idx);
                }
                b_t_idx_to_m_idx
            }
        };

        Self {
            root_node: Some(combined_tree),
            leaf_count: t_idx_to_m_idx.len(),
            leaf_indices: reverse_idx_dict(&t_idx_to_m_idx),
        }
    }

    pub fn leaf_count(&self) -> usize {
        self.leaf_count
    }

    pub fn leaves(&self) -> LeafNodes {
        let nodes = self.root_node.as_ref().unwrap().leaf_nodes();
        nodes
    }

    pub fn get_leaf_merkle_path(&self, index: usize) -> Option<&TaprootMerkleBranch> {
        let index = self.index_map(index);
        if let Some(leaf) = self.leaves().nth(index) {
            Some(leaf.merkle_branch())
        } else {
            None
        }
    }

    fn index_map(&self, index: usize) -> usize {
        self.leaf_indices[index] as usize
    }

    pub fn get_tapleaf(&self, index: usize) -> Option<&LeafNode> {
        let index = self.index_map(index);
        self.leaves().nth(index)
    }

    pub fn verify_inclusion_by_index(&self, index: usize) -> bool {
        let index = self.index_map(index);
        let leaf = self.get_tapleaf(index).unwrap();
        let path = self.get_leaf_merkle_path(index).unwrap();
        let mut first_node_hash = TapNodeHash::from_node_hashes(leaf.node_hash(), path[0]);
        path[1..].into_iter().for_each(|sibling_node| {
            first_node_hash = TapNodeHash::from_node_hashes(first_node_hash, *sibling_node);
        });

        first_node_hash == self.root().node_hash()
    }
}

impl<const NUM_POLY: usize> From<NodeInfo> for BasicTree<NUM_POLY> {
    fn from(value: NodeInfo) -> Self {
        Self {
            root_node: Some(value),
            leaf_count: 0,
            leaf_indices: Vec::new(),
        }
    }
}

pub fn verify_inclusion(root: TapNodeHash, leaf: &LeafNode) -> bool {
    let path = leaf.merkle_branch();
    let mut first_node_hash = TapNodeHash::from_node_hashes(leaf.node_hash(), path[0]);
    path[1..].into_iter().for_each(|sibling_node| {
        first_node_hash = TapNodeHash::from_node_hashes(first_node_hash, *sibling_node);
    });

    first_node_hash == root
}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
enum PolynomialType {
    Eva,
    Coeff,
}
struct Polynomials<F: BfField> {
    values: Vec<F>,
    points: Vec<F>, // only for evaluations
    style: PolynomialType,
}

impl<F: BfField> Polynomials<F> {
    pub fn new(values: Vec<F>, style: PolynomialType) -> Self {
        Self {
            values,
            points: Vec::new(),
            style,
        }
    }

    pub fn new_eva_poly(values: Vec<F>, points: Vec<F>, style: PolynomialType) -> Self {
        Self {
            values,
            points,
            style,
        }
    }

    fn convert_to_evals_at_subgroup(&self) -> Self {
        assert!(self.style == PolynomialType::Coeff);
        let subgroup_bits = log2_strict_usize(self.values.len());
        let subgroup = F::sub_group(subgroup_bits);
        let mut evals = Vec::new();
        for i in 0..subgroup.len() {
            let point = subgroup[i];
            let result = self
                .values
                .iter()
                .fold(F::zero(), |acc, item| acc + *item * point.exp_u64(i as u64));
            evals.push(result);
        }
        assert_eq!(subgroup.len(), evals.len());
        Self::new_eva_poly(evals, subgroup, PolynomialType::Eva)
    }

    fn values(&self) -> &Vec<F> {
        &self.values
    }

    fn points(&self) -> &Vec<F> {
        assert!(self.style == PolynomialType::Eva);
        &self.points
    }
}

#[cfg(test)]
mod tests {

    use p3_baby_bear::BabyBear;
    use p3_dft::{Radix2Dit, TwoAdicSubgroupDft};
    use p3_field::extension::BinomialExtensionField;
    use p3_field::{AbstractExtensionField, AbstractField};
    use p3_interpolation::interpolate_subgroup;
    use p3_matrix::dense::RowMajorMatrix;
    use rand::distributions::Standard;
    use rand::prelude::Distribution;
    use rand::{thread_rng, Rng};
    use scripts::execute_script_with_inputs;

    use super::*;

    #[test]
    fn test_check_x_neg_x_equal_script() {
        const num_polys: usize = 1;
        let x = BabyBear::from_u32(0x11654321);
        let neg_x = BabyBear::field_mod() - x; // 669ABCE0
        let expect_neg_x = BabyBear::from_u32(0x669ABCE0);
        assert_eq!(neg_x, expect_neg_x);
        let leaf =
            EvaluationLeaf::<num_polys, BabyBear>::new(0, x, vec![BabyBear::from_u32(0x11654321)]);

        // check signature and verify the value
        let signature = leaf.x_commitment.commitments[0].signature();
        // check equal to r
        let exec_scripts = script! {
            { leaf.x_commitment.commitments[0].checksig_verify_script() }
            { leaf.x_commitment.commitments[0].check_equal_x_or_neg_x_script(&leaf.neg_x_commitment.commitments[0]) }
            OP_1
        };
        let exec_result = execute_script_with_inputs(exec_scripts, signature);
        assert!(exec_result.success);

        // check equal to -r
        let signature = leaf.x_commitment.commitments[0].signature();
        let exec_scripts = script! {
            { leaf.x_commitment.commitments[0].checksig_verify_script() }
            { leaf.neg_x_commitment.commitments[0].check_equal_x_or_neg_x_script(&leaf.x_commitment.commitments[0]) }
            OP_1
        };
        let exec_result = execute_script_with_inputs(exec_scripts, signature);
        assert!(exec_result.success);

        for _ in 0..30 {
            let mut rng = rand::thread_rng();
            let random_number: u32 = rng.gen();
            let x = random_number % BabyBear::MOD;
            let x = BabyBear::from_u32(x);
            let neg_x = BabyBear::field_mod() - x;
            let leaf = EvaluationLeaf::<num_polys, BabyBear>::new(
                0,
                x,
                vec![BabyBear::from_u32(0x11654321)],
            );

            // check signature and verify the value
            let signature = leaf.x_commitment.commitments[0].signature();
            // check equal to r
            let exec_scripts = script! {
                { leaf.x_commitment.commitments[0].checksig_verify_script() }
                { leaf.x_commitment.commitments[0].check_equal_x_or_neg_x_script(&leaf.neg_x_commitment.commitments[0]) }
                OP_1
            };
            let exec_result = execute_script_with_inputs(exec_scripts, signature);
            assert!(exec_result.success);

            // check equal to -r
            let signature = leaf.x_commitment.commitments[0].signature();
            let exec_scripts = script! {
                { leaf.x_commitment.commitments[0].checksig_verify_script() }
                { leaf.neg_x_commitment.commitments[0].check_equal_x_or_neg_x_script(&leaf.x_commitment.commitments[0]) }
                OP_1
            };
            let exec_result = execute_script_with_inputs(exec_scripts, signature);
            assert!(exec_result.success);

            let signature = leaf.neg_x_commitment.commitments[0].signature();
            let exec_scripts = script! {
                { leaf.neg_x_commitment.commitments[0].checksig_verify_script() }
                { leaf.x_commitment.commitments[0].check_equal_x_or_neg_x_script(&leaf.neg_x_commitment.commitments[0]) }
                OP_1
            };
            let exec_result = execute_script_with_inputs(exec_scripts, signature);
            assert!(exec_result.success);
        }
    }

    #[test]
    fn test_tree_builder() {
        type F = BabyBear;
        let depth = 3;
        let mut coeffs1: Vec<F> = Vec::with_capacity(2u32.pow(depth as u32) as usize);
        for i in 0..2u32.pow(depth as u32) {
            coeffs1.push(F::from_canonical_u32(i));
        }
        let poly1 = Polynomials::new(coeffs1, PolynomialType::Coeff);
        let eva_poly1 = poly1.convert_to_evals_at_subgroup();
        let evas1 = eva_poly1.values();

        let mut tb = TreeBuilder::<3>::new();

        for i in 0..evas1.len() {
            let leaf_script = construct_evaluation_leaf_script::<1, F>(
                i,
                eva_poly1.points[i],
                vec![evas1[i].clone()],
            )
            .unwrap();
            tb.add_leaf(leaf_script);
        }

        let tree = tb.build_tree();
        // assert!(root_node.leaf_nodes().len()==8);
    }

    // fn commit_with_poly_tree<F: BfField>(degree: usize) -> PolyCommitTree<F, 1>
    // where
    //     Standard: Distribution<F>,
    // {
    //     let mut rng = thread_rng();
    //     let coeffs = (0..degree).map(|_| rng.gen::<F>()).collect::<Vec<_>>();

    //     let poly = Polynomials::new(coeffs, PolynomialType::Coeff);
    //     let eva_poly = poly.convert_to_evals_at_subgroup();
    //     let evas = eva_poly.values();
    //     let mut poly_taptree = PolyCommitTree::<F, 1>::new(2);
    //     poly_taptree.commit_rev_points(evas.clone(), 2);
    //     poly_taptree
    // }

    // #[test]
    // fn test_poly_commit_tree() {
    //     // x^2 + 2 x + 3
    //     type F = BabyBear;
    //     let poly_taptree = commit_with_poly_tree::<F>(8);

    //     (0..4).into_iter().for_each(|index| {
    //         let leaf = poly_taptree.get_tapleaf(index).unwrap();
    //         let script = leaf.leaf().as_script().unwrap();
    //         let points_leaf = poly_taptree.get_points_leaf(index);
    //         assert_eq!(
    //             points_leaf.recover_points_euqal_to_commited_point(),
    //             *script.0
    //         );
    //         let success = verify_inclusion(poly_taptree.root().node_hash(), leaf);
    //         assert_eq!(success, true);
    //     });
    // }

    #[test]
    fn test_swap_slice() {
        let mut values = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

        let temp1 = values[2..4].to_vec();
        let temp2 = values[6..8].to_vec();

        values[2..4].clone_from_slice(&temp2);
        values[6..8].clone_from_slice(&temp1);

        println!("{:?}", values);
    }
}
