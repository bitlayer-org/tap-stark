use core::marker::PhantomData;
use core::{panic, usize};

use bitcoin::hashes::Hash as Bitcoin_HASH;
use bitcoin::taproot::LeafNode;
use bitcoin::TapNodeHash;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_util::log2_strict_usize;

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
#[derive(Clone, Debug, PartialEq, PartialOrd)]
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

#[derive(Clone)]
pub struct CommitProof<F: BfField> {
    pub points_leaf: PointsLeaf<F>,
    pub leaf_node: LeafNode,
}

impl<F: BfField> BFMmcs<F> for TapTreeMmcs<F> {
    type ProverData = PolyCommitTree<F, 1>;
    type Proof = CommitProof<F>;
    type Commitment = TreeRoot;
    type Error = BfError;

    fn open_taptree(&self, index: usize, prover_data: &PolyCommitTree<F, 1>) -> Self::Proof {
        // The matrix with width-2 lead to the index need to right shift 1-bit
        // let leaf_index = index >> LOG_DEFAULT_MATRIX_WIDTH;
        let leaf_index = index;
        let leaf = prover_data.get_tapleaf(leaf_index);
        let opening_leaf = match leaf {
            Some(v) => v,
            None => {
                // println!(
                //     "leaf index:{:?}, leaf count:{:?}",
                //     index,
                //     prover_data.leaf_count()
                // );
                panic!("invalid leaf index")
            }
        };
        println!("leaf_index:{:?}", leaf_index);
        let open_leaf = prover_data.get_points_leaf(leaf_index).clone();
        CommitProof {
            points_leaf: open_leaf,
            leaf_node: opening_leaf.clone(),
        }
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
    fn get_matrices (
        &self,
        prover_data: &Self::ProverData,
    ) -> Vec<RowMajorMatrix<F>> {
        prover_data.leaves.clone()
    }
}

#[cfg(test)]
mod test{
    use p3_baby_bear::BabyBear;
    use p3_field::AbstractField;
    use p3_matrix::dense::RowMajorMatrix;

    use crate::mmcs::bf_mmcs::BFMmcs;

    use super::TapTreeMmcs;
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
            vec![F::zero(), F::one(), F::two(), F::one(), F::two(), F::two(), F::one(), F::zero()],
            2,
        );

        // mat_2 = [
        //   0 1 2 1
        //   2 2 1 0
        //   0 1 2 1
        //   2 2 1 0
        // ]
        let mat_2 = RowMajorMatrix::new(
            vec![F::zero(), F::one(), F::two(), F::one(), F::two(), F::two(), F::one(), F::zero(), F::zero(), F::one(), F::two(), F::one(), F::two(), F::two(), F::one(), F::zero()],
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
            vec![F::zero(), F::one(), F::two(), F::one(), F::two(), F::two(), F::one(), F::zero()],
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
        let index = 2;
        let proof = mmcs.open_taptree(index, &prover_data);

        // let _ = proof.points_leaf.print_point_evals();

        let success = mmcs.verify_taptree(&proof, &commit);

    }
}
