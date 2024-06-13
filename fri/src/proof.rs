use alloc::vec::Vec;

use bitcoin::taproot::LeafNode;
use primitives::field::BfField;
// use serde::{Deserialize, Serialize};
use primitives::mmcs::bf_mmcs::BFMmcs;
use primitives::mmcs::point::PointsLeaf;
use primitives::mmcs::taptree_mmcs::CommitProof;
// #[derive(Serialize, Deserialize)]
// #[serde(bound(
//     serialize = "Witness: Serialize",
//     deserialize = "Witness: Deserialize<'de>"
// ))]
pub struct FriProof<F: BfField, M: BFMmcs<F>, Witness> {
    pub(crate) commit_phase_commits: Vec<M::Commitment>,
    pub(crate) query_proofs: Vec<BfQueryProof<F>>,
    // This could become Vec<FC::Challenge> if this library was generalized to support non-constant
    // final polynomials.
    pub(crate) final_poly: F,
    pub(crate) pow_witness: Witness,
}

// #[derive(Serialize, Deserialize)]
// #[serde(bound = "")]
pub struct BfQueryProof<F: BfField> {
    /// For each commit phase commitment, this contains openings of a commit phase codeword at the
    /// queried location, along with an opening proof.
    pub(crate) commit_phase_openings: Vec<CommitProof<F>>,
}

pub fn get_leaf_index_by_query_index(query_index: usize) -> (usize, usize, usize) {
    let index_i = query_index >> 1;
    let index_i_sibling = index_i ^ 1;
    let index_pair = index_i >> 1;
    (index_pair, index_i, index_i_sibling)
}
