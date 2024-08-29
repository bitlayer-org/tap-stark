// use alloc::vec;
// use alloc::vec::Vec;
use core::fmt::Debug;

use p3_matrix::dense::RowMajorMatrix;
use serde::de::DeserializeOwned;
use serde::Serialize;

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
    type Commitment: Clone + Serialize + DeserializeOwned;
    type Proof: Clone + Serialize + DeserializeOwned;
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
    fn open_batch(
        &self,
        index: usize,
        prover_data: &Self::ProverData,
    ) -> (Vec<Vec<T>>, Self::Proof) {
        unimplemented!()
    }

    fn verify_batch(
        &self,
        opened_values: &Vec<Vec<T>>,
        proof: &Self::Proof,
        root: &Self::Commitment,
    ) -> Result<(), Self::Error>;

    fn verify_taptree(
        &self,
        proof: &Self::Proof,
        root: &Self::Commitment,
    ) -> Result<(), Self::Error>;

    /// Get the matrices that were committed to.
    fn get_matrices<'a>(&self, prover_data: &'a Self::ProverData) -> Vec<&'a RowMajorMatrix<T>>;

    fn get_matrix_heights(&self, prover_data: &Self::ProverData) -> Vec<usize> {
        self.get_matrices(prover_data)
            .iter()
            .map(|matrix| matrix.values.len() / matrix.width)
            .collect()
    }

    /// Get the largest height of any committed matrix.
    fn get_max_height(&self, prover_data: &Self::ProverData) -> usize {
        self.get_matrix_heights(prover_data)
            .into_iter()
            .max()
            .unwrap_or_else(|| panic!("No committed matrices?"))
    }
}
