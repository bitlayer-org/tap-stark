
use core::ops::{Deref, DerefMut};
use core::{mem, usize};

use primitives::{field::BfField};
use crate::fri_script::point::{PointsLeaf};
use crate::fri_script::leaf::EvaluationLeaf;
use bitcoin::taproot::LeafVersion::TapScript;
use bitcoin::taproot::{LeafNode, LeafNodes, NodeInfo, TaprootMerkleBranch};
use bitcoin::{ScriptBuf, TapNodeHash};
use itertools::{Chunk, Itertools};
use p3_util::{log2_strict_usize, reverse_slice_index_bits};

use crate::error::BfError;

pub fn combine_two_nodes(a: NodeInfo, b: NodeInfo) -> Result<(NodeInfo, bool), BfError> {
    let parent = NodeInfo::combine_with_order(a, b)?;
    Ok(parent)
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
}

impl<const NUM_POLY: usize, F: BfField> PolyCommitTree<F, NUM_POLY> {
    pub fn new(log_poly_points: usize) -> Self {
        Self {
            tree: BasicTree::<NUM_POLY>::new(log_poly_points),
            points_leafs: Vec::new(),
        }
    }

    pub fn commit_points(&mut self, evaluations: Vec<F>) {
        let poly_points = evaluations.len();
        let evas = Polynomials::new_eva_poly(
            evaluations,
            F::sub_group(log2_strict_usize(poly_points)),
            PolynomialType::Eva,
        );
        let mut builder = TreeBuilder::<NUM_POLY>::new();
        for i in 0..evas.values.len() {
            let leaf_script = construct_evaluation_leaf_script::<1, F>(
                i,
                evas.points[i],
                vec![evas.values[i].clone()],
            )
            .unwrap();
        }
        self.tree = builder.build_tree();
    }

    pub fn commit_rev_points(&mut self, evaluations: Vec<F>, width: usize) {
        let poly_points = evaluations.len();
        let mut subgroup = F::sub_group(log2_strict_usize(poly_points));
        let leaf_indexs: Vec<usize> = (0..poly_points).into_iter().collect();
        reverse_slice_index_bits(&mut subgroup);
        let mut tree_builder = TreeBuilder::<NUM_POLY>::new();
        for i in (0..poly_points).into_iter().step_by(width) {
            let leaf = PointsLeaf::new(
                leaf_indexs[i],
                leaf_indexs[i + 1],
                subgroup[i],
                evaluations[i],
                subgroup[i + 1],
                evaluations[i + 1],
            );
            self.add_leaf(&mut tree_builder, &leaf)
        }

        self.tree = tree_builder.build_tree();
    }

    pub fn root(&self) -> &NodeInfo {
        self.tree.root()
    }

    pub fn get_tapleaf(&self, index: usize) -> Option<&LeafNode> {
        self.tree.get_tapleaf(index)
    }

    // pub fn combine_tree()

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
    pub fn new(log_poly_points: usize) -> Self {
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

    use bf_scripts::BabyBear;
    use p3_dft::{Radix2Dit, TwoAdicSubgroupDft};
    use p3_field::extension::BinomialExtensionField;
    use p3_field::{AbstractExtensionField, AbstractField};
    use p3_interpolation::interpolate_subgroup;
    use p3_matrix::dense::RowMajorMatrix;
    use rand::distributions::Standard;
    use rand::prelude::Distribution;
    use rand::{thread_rng, Rng};

    use super::*;

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

    fn commit_with_poly_tree<F: BfField>(degree: usize) -> PolyCommitTree<F, 1>
    where
        Standard: Distribution<F>,
    {
        let mut rng = thread_rng();
        let coeffs = (0..degree).map(|_| rng.gen::<F>()).collect::<Vec<_>>();

        let poly = Polynomials::new(coeffs, PolynomialType::Coeff);
        let eva_poly = poly.convert_to_evals_at_subgroup();
        let evas = eva_poly.values();
        let mut poly_taptree = PolyCommitTree::<F, 1>::new(2);
        poly_taptree.commit_rev_points(evas.clone(), 2);
        poly_taptree
    }

    #[test]
    fn test_poly_commit_tree() {
        // x^2 + 2 x + 3
        type F = BabyBear;
        let poly_taptree = commit_with_poly_tree::<F>(8);

        (0..4).into_iter().for_each(|index| {
            let leaf = poly_taptree.get_tapleaf(index).unwrap();
            let script = leaf.leaf().as_script().unwrap();
            let points_leaf = poly_taptree.get_points_leaf(index);
            assert_eq!(
                points_leaf.recover_points_euqal_to_commited_point(),
                *script.0
            );
            let success = verify_inclusion(poly_taptree.root().node_hash(), leaf);
            assert_eq!(success, true);
        });
    }

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
