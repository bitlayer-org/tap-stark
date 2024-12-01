use alloc::vec::Vec;
use std::marker::PhantomData;

use basic::field::BfField;
use basic::mmcs::bf_mmcs::BFMmcs;
use basic::tcs::{
    CommitedData, CommitedProof, DefaultSyncBcManager, PolyTCS, UseBComm, B, BM, BO, SG, TCS,
};
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Clone)]
#[serde(bound(
    serialize = "Witness: Serialize, InputProof: Serialize",
    deserialize = "Witness: Deserialize<'de>, InputProof: Deserialize<'de>"
))]
pub struct FriProof<F: BfField, M: BFMmcs<F>, Witness, InputProof> {
    pub(crate) commit_phase_commits: Vec<M::Commitment>,
    pub(crate) query_proofs: Vec<BfQueryProof<F, InputProof>>,
    // This could become Vec<FC::Challenge> if this library was generalized to support non-constant
    // final polynomials.
    pub(crate) final_poly: F,
    pub(crate) pow_witness: Witness,
    // _phantom: PhantomData<(M, InputProof)>,
}

#[derive(Serialize, Deserialize, Clone)]
#[serde(bound(
    serialize = "InputProof: Serialize",
    deserialize = "InputProof: Deserialize<'de>",
))]
pub struct BfQueryProof<F: BfField, InputProof> {
    pub input_proof: InputProof,
    /// For each commit phase commitment, this contains openings of a commit phase codeword at the
    /// queried location, along with an opening proof.
    pub(crate) commit_phase_openings: Vec<(Vec<Vec<F>>, CommitedProof<BO, B>)>, // for the same polys, each query produces a new CommitedProof
}

pub fn get_leaf_index_by_query_index(query_index: usize) -> (usize, usize, usize) {
    let index_i = query_index >> 1;
    let index_i_sibling = index_i ^ 1;
    let index_pair = index_i >> 1;
    (index_pair, index_i, index_i_sibling)
}
