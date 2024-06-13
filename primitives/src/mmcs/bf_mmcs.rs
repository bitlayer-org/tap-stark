// use alloc::vec;
// use alloc::vec::Vec;
use core::fmt::Debug;

use p3_matrix::dense::RowMajorMatrix;
// use serde::de::DeserializeOwned;
// use serde::Serialize;

/// A "Mixed Matrix Commitment Scheme" (MMCS) is a generalization of a vector commitment scheme; it
/// supports committing to matrices and then opening rows. It is also batch-oriented; one can commit
/// to a batch of matrices at once even if their widths and heights differ.
///
/// When a particular row index is opened, it is interpreted directly as a row index for matrices
/// with the largest height. For matrices with smaller heights, some bits of the row index are
/// removed (from the least-significant side) to get the effective row index. These semantics are
/// useful in the FRI protocol. See the documentation for `open_batch` for more details.
pub trait BFMmcs<T: Send + Sync>: Clone {
    type ProverData;
    // type Commitment: Clone + Serialize + DeserializeOwned;
    // type Proof: Clone + Serialize + DeserializeOwned;
    type Commitment: Clone;
    type Proof: Clone;
    type Error: Debug;

    fn commit(&self, inputs: Vec<RowMajorMatrix<T>>) -> (Self::Commitment, Self::ProverData);

    fn commit_matrix(&self, input: RowMajorMatrix<T>) -> (Self::Commitment, Self::ProverData) {
        self.commit(vec![input])
    }

    fn commit_vec(&self, input: Vec<T>) -> (Self::Commitment, Self::ProverData)
    where
        T: Clone + Send + Sync,
    {
        self.commit_matrix(RowMajorMatrix::new_col(input))
    }

    fn open_taptree(&self, index: usize, prover_data: &Self::ProverData) -> Self::Proof;
    fn verify_taptree(
        &self,
        proof: &Self::Proof,
        root: &Self::Commitment,
    ) -> Result<(), Self::Error>;
}
