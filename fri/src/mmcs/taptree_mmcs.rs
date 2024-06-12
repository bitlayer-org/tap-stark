use alloc::vec::Vec;
use core::marker::PhantomData;
use core::{panic, usize};

use bitcoin::hashes::Hash as Bitcoin_HASH;
use bitcoin::TapNodeHash;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_util::log2_strict_usize;

use super::bf_mmcs::BFMmcs;
use crate::challenger::chan_field::{u256_to_u32, u32_to_u256, U256, U32};
use crate::error::BfError;
use crate::field::BfField;
use crate::prover::LOG_DEFAULT_MATRIX_WIDTH;
use crate::taptree::{verify_inclusion, PolyCommitTree};
use crate::BfCommitPhaseProofStep;

pub type TreeRoot = [U32; ROOT_WIDTH];
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
impl<F: BfField> BFMmcs<F> for TapTreeMmcs<F> {
    type ProverData = PolyCommitTree<F, 1>;
    type Proof = BfCommitPhaseProofStep<F>;
    type Commitment = TreeRoot;
    type Error = BfError;

    fn open_taptree(&self, index: usize, prover_data: &PolyCommitTree<F, 1>) -> Self::Proof {
        // The matrix with width-2 lead to the index need to right shift 1-bit
        let leaf_index = index >> LOG_DEFAULT_MATRIX_WIDTH;
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
        let open_leaf = prover_data.get_points_leaf(leaf_index).clone();
        BfCommitPhaseProofStep {
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
        let log_leaves = log2_strict_usize(inputs[0].height());
        let mut tree = PolyCommitTree::<F, 1>::new(log_leaves);

        tree.commit_rev_points(inputs[0].values.clone(), inputs[0].width);
        let root: U256 = tree.root().node_hash().as_byte_array().clone();

        (u256_to_u32(root), tree)
    }
}
