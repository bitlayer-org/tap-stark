use core::marker::PhantomData;
use core::{panic, usize};

use bitcoin::hashes::Hash as Bitcoin_HASH;
use bitcoin::taproot::{LeafNode, TapLeaf};
use bitcoin::TapNodeHash;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_util::log2_strict_usize;
use scripts::execute_script_with_inputs;
use serde::ser::SerializeStruct;
use serde::{Deserialize, Serialize, Serializer};

use super::bf_mmcs::BFMmcs;
use super::error::BfError;
use super::point::PointsLeaf;
use super::taptree::{verify_inclusion, PolyCommitTree};
use crate::challenger::chan_field::{u256_to_u32, u32_to_u256, U256, U32};
use crate::field::BfField;

pub type TreeRoot = [U32; ROOT_WIDTH];
// Commit two adjacent points to a leaf node
pub const DEFAULT_MATRIX_WIDTH: usize = 2;
pub const LOG_DEFAULT_MATRIX_WIDTH: usize = 1;

pub const ROOT_WIDTH: usize = 8;
#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, PartialOrd)]
pub struct TapTreeMmcs<F> {
    _marker: PhantomData<F>,
}

impl<F> TapTreeMmcs<F> {
    pub fn new() -> Self {
        Self {
            _marker: PhantomData,
        }
    }
}

#[derive(Serialize, Deserialize, Clone)]
#[serde(bound = "")]
pub struct CommitProof<F: BfField> {
    pub points_leaf: PointsLeaf<F>,
    pub leaf_node: LeafNode,
}

impl<F: BfField> CommitProof<F> {
    pub fn new(points_leaf: PointsLeaf<F>, leaf_node: LeafNode) -> Self {
        Self {
            points_leaf,
            leaf_node,
        }
    }

    pub fn verify_points_leaf(&self) -> bool {
        if let TapLeaf::Script(script, _ver) = self.leaf_node.leaf().clone() {
            let res = execute_script_with_inputs(script, self.points_leaf.witness());
            return res.success;
        } else {
            panic!("Invalid script")
        }
    }

    pub fn get_open_values(&self) -> Vec<F> {
        self.points_leaf.get_all_points_value()
    }
}

impl<F: BfField> BFMmcs<F> for TapTreeMmcs<F> {
    type ProverData = PolyCommitTree<F, 1>;
    type Proof = CommitProof<F>;
    type Commitment = TreeRoot;
    type Error = BfError;

    fn open_taptree(&self, index: usize, prover_data: &PolyCommitTree<F, 1>) -> Self::Proof {
        let leaf_index = index;
        let leaf = prover_data.get_tapleaf(leaf_index);
        let opening_leaf = match leaf {
            Some(v) => v,
            None => {
                panic!("invalid leaf index")
            }
        };
        //println!("leaf_index:{:?}", leaf_index);
        let open_leaf = prover_data.get_points_leaf(leaf_index).clone();
        CommitProof {
            points_leaf: open_leaf,
            leaf_node: opening_leaf.clone(),
        }
    }

    fn open_batch(
        &self,
        index: usize, // This is the index corresponding to the highest matrix
        prover_data: &PolyCommitTree<F, 1>,
    ) -> (Vec<Vec<F>>, Self::Proof) {
        let comm_proof = self.open_taptree(index, prover_data);
        let open_values = comm_proof.get_open_values();
        let matrix_widths = prover_data.get_matrix_widths();
        let mut result = Vec::with_capacity(matrix_widths.len());
        let mut start = 0;

        for &width in &matrix_widths {
            let end = start + width;
            result.push(Vec::from(&open_values[start..end]));
            start = end;
        }

        (result, comm_proof)
    }

    fn verify_batch(
        &self,
        opened_values: &Vec<Vec<F>>,
        proof: &Self::Proof,
        root: &Self::Commitment,
    ) -> Result<(), Self::Error> {
        let total_len: usize = opened_values.iter().map(|v| v.len()).sum();
        let mut result = Vec::with_capacity(total_len);
        for vec in opened_values {
            result.extend(vec);
        }

        let points = proof.get_open_values();
        assert_eq!(points.len(), result.len());
        for (p, r) in points.iter().zip(result.iter()) {
            if p != r {
                return Err(BfError::InvalidOpenedValue);
            }
        }

        self.verify_taptree(proof, root)
    }

    fn verify_taptree(
        &self,
        proof: &Self::Proof,
        root: &Self::Commitment,
    ) -> Result<(), Self::Error> {
        let root_node = TapNodeHash::from_byte_array(u32_to_u256(root.clone()));
        let success = verify_inclusion(root_node, &proof.leaf_node);
        if success {
            Ok(())
        } else {
            Err(BfError::InvalidMerkleProof)
        }
    }

    fn commit(&self, inputs: Vec<RowMajorMatrix<F>>) -> (Self::Commitment, Self::ProverData) {
        // let log_leaves = log2_strict_usize(inputs[0].height());
        let mut tree = PolyCommitTree::<F, 1>::new();

        tree.commit_points(inputs);
        let root: U256 = tree.root().node_hash().as_byte_array().clone();

        (u256_to_u32(root), tree)
    }

    fn get_matrices<'a>(&self, prover_data: &'a Self::ProverData) -> Vec<&'a RowMajorMatrix<F>> {
        prover_data.leaves.iter().collect()
    }
}

#[cfg(test)]
mod test {
    use bitcoin::taproot::TapLeaf;
    use p3_baby_bear::BabyBear;
    use p3_field::AbstractField;
    use p3_matrix::dense::RowMajorMatrix;
    use scripts::execute_script_with_inputs;

    use super::TapTreeMmcs;
    use crate::mmcs::bf_mmcs::BFMmcs;
    type F = BabyBear;

    #[test]
    fn test_taptree_mmcs() {
        // mat_1 = [
        //   0 1
        //   2 1
        //   2 2
        //   1 0
        // ]
        let mat_1 = RowMajorMatrix::new(
            vec![
                F::zero(),
                F::one(),
                F::two(),
                F::one(),
                F::two(),
                F::two(),
                F::one(),
                F::zero(),
            ],
            2,
        );

        // mat_2 = [
        //   0 1 2 1
        //   2 2 1 0
        //   0 1 2 1
        //   2 2 1 0
        // ]
        let mat_2 = RowMajorMatrix::new(
            vec![
                F::zero(),
                F::one(),
                F::two(),
                F::one(),
                F::two(),
                F::two(),
                F::one(),
                F::zero(),
                F::zero(),
                F::one(),
                F::two(),
                F::one(),
                F::two(),
                F::two(),
                F::one(),
                F::zero(),
            ],
            4,
        );

        // mat_3 = [
        //   0
        //   1
        //   2
        //   1
        //   2
        //   2
        //   1
        //   0
        // ]
        let mat_3 = RowMajorMatrix::new(
            vec![
                F::zero(),
                F::one(),
                F::two(),
                F::one(),
                F::two(),
                F::two(),
                F::one(),
                F::zero(),
            ],
            1,
        );

        // we get pointleafs like:
        // index:0, ys:[0, 0, 1, 0, 1, 2, 1]
        // index:1, ys:[1, 0, 1, 0, 1, 2, 1]
        // index:2, ys:[2, 2, 1, 2, 2, 1, 0]
        // index:3, ys:[1, 2, 1, 2, 2, 1, 0]
        // index:4, ys:[2, 2, 2, 0, 1, 2, 1]
        // index:5, ys:[2, 2, 2, 0, 1, 2, 1]
        // index:6, ys:[1, 1, 0, 2, 2, 1, 0]
        // index:7, ys:[0, 1, 0, 2, 2, 1, 0]

        let inputs = vec![mat_1, mat_2, mat_3];
        let mmcs = TapTreeMmcs::new();
        let (commit, prover_data) = mmcs.commit(inputs);

        //test get_max_height
        let max_height = mmcs.get_max_height(&prover_data);
        assert_eq!(max_height, 8);

        let index = 2;
        let proof = mmcs.open_taptree(index, &prover_data);

        let wrong_index = 3;
        let wrong_proof = mmcs.open_taptree(wrong_index, &prover_data);

        // let _ = proof.points_leaf.print_point_evals();
        {
            let points_leaf = proof.points_leaf.clone();
            let input = points_leaf.witness();
            if let TapLeaf::Script(script, _ver) = proof.leaf_node.clone().leaf().clone() {
                assert_eq!(script, points_leaf.recover_points_euqal_to_commited_point());
                let res = execute_script_with_inputs(
                    points_leaf.recover_points_euqal_to_commited_point(),
                    input,
                );
                if !res.success {
                    println!("execute_script_with_inputs error");
                }
                assert_eq!(res.success, true);
            } else {
                panic!("Invalid script")
            }
        }

        {
            let points_leaf = proof.points_leaf.clone();
            let wrong_points_leaf = wrong_proof.points_leaf.clone();
            let wrong_input = wrong_points_leaf.witness();
            if let TapLeaf::Script(script, _ver) = proof.leaf_node.clone().leaf().clone() {
                assert_eq!(script, points_leaf.recover_points_euqal_to_commited_point());
                let res = execute_script_with_inputs(
                    points_leaf.recover_points_euqal_to_commited_point(),
                    wrong_input,
                );
                if !res.success {
                    println!("execute_script_with_inputs error as expected");
                }
                assert_eq!(res.success, false);
            } else {
                panic!("Invalid script")
            }
        }

        let success = mmcs.verify_taptree(&proof, &commit);
    }
}
