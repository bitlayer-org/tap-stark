use core::marker::PhantomData;
use core::usize;

use bitcoin::hashes::Hash as Bitcoin_HASH;
use bitcoin::TapNodeHash;
use itertools::Itertools;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_util::log2_ceil_usize;

use super::bf_mmcs::BFMmcs;
use super::error::BfError;
use crate::challenger::chan_field::{u256_to_u32, u32_to_u256, U32};
use crate::field::BfField;
use crate::tcs::{
    CommitedData, CommitedProof, DefaultSyncBcManager, PolyTCS, B, BM, BO, SG, TCS,
};

pub type TreeRoot = [U32; ROOT_WIDTH];
// Commit two adjacent points to a leaf node
pub const DEFAULT_MATRIX_WIDTH: usize = 2;
pub const LOG_DEFAULT_MATRIX_WIDTH: usize = 1;

pub const ROOT_WIDTH: usize = 8;
#[derive(Clone)]
pub struct TapTreeMmcs<F> {
    tcs: TCS<BM, SG, BO, B>,
    num_queries: usize,
    _marker: PhantomData<F>,
}

impl<'a, F> TapTreeMmcs<F> {
    pub fn new(manager: DefaultSyncBcManager, num_queries: usize) -> Self {
        Self {
            tcs: TCS::new(manager),
            num_queries,
            _marker: PhantomData,
        }
    }
}

impl<F: BfField> BFMmcs<F> for TapTreeMmcs<F> {
    type ProverData = Vec<CommitedData<F, BO, B>>;
    type Proof = CommitedProof<BO, B>;
    type Commitment = Vec<TreeRoot>;
    type Error = BfError;

    fn open_batch(
        &self,
        query_times_index: usize,
        query_index: usize, // This is the index corresponding to the highest matrix
        prover_data: &Self::ProverData,
    ) -> (Vec<Vec<F>>, Self::Proof) {
        let max_height = prover_data[0].get_max_height();
        let log_max_height = log2_ceil_usize(max_height);
        let openings = prover_data[0]
            .leaves
            .iter()
            .map(|matrix| {
                let log2_height = log2_ceil_usize(matrix.height());
                let bits_reduced = log_max_height - log2_height;
                let reduced_index = query_index >> bits_reduced;
                matrix.row(reduced_index).collect()
            })
            .collect_vec();

        let (commited_proof, openings_evals) = self.tcs.open_with_one_query(
            query_times_index,
            query_index,
            prover_data,
            self.num_queries,
        );
        let openings_flatten: Vec<F> = openings.clone().into_iter().flatten().collect();
        assert_eq!(openings_flatten, openings_evals);

        (openings, commited_proof)
    }

    fn verify_batch(
        &self,
        query_times_index: usize,
        opened_values: &Vec<Vec<F>>,
        proofs: &Self::Proof,
        roots: &Self::Commitment,
    ) -> Result<(), Self::Error> {
        let openings_flatten: Vec<F> = opened_values.clone().into_iter().flatten().collect();

        let commitments: Vec<TapNodeHash> = roots
            .iter()
            .map(|root| TapNodeHash::from_byte_array(u32_to_u256(*root)))
            .collect();

        let success = self
            .tcs
            .verify(commitments[query_times_index], proofs, openings_flatten);
        if success {
            Ok(())
        } else {
            Err(BfError::InvalidOpenedValue)
        }
    }

    fn commit(&self, inputs: Vec<RowMajorMatrix<F>>) -> (Self::Commitment, Self::ProverData) {
        let commited_data = self
            .tcs
            .commit_poly_with_query_times(inputs, self.num_queries);
        let commitments: Vec<[U32; 8]> = commited_data
            .iter()
            .map(|data| {
                let root = *data
                    .commit_taptree
                    .root()
                    .hash
                    .as_byte_array();
                u256_to_u32(root)
            })
            .collect();

        (commitments, commited_data)
    }

    fn get_matrices<'a>(&self, prover_data: &'a Self::ProverData) -> Vec<&'a RowMajorMatrix<F>> {
        prover_data[0].leaves.iter().collect()
    }
}

#[cfg(test)]
mod test {
    
    use p3_baby_bear::BabyBear;
    use p3_field::AbstractField;
    use p3_matrix::dense::RowMajorMatrix;
    

    use super::TapTreeMmcs;
    use crate::mmcs::bf_mmcs::BFMmcs;
    use crate::tcs::DefaultSyncBcManager;
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

        // let inputs = vec![mat_1, mat_2, mat_3];
        let inputs = vec![mat_3, mat_2, mat_1];
        let query_times = 10;
        let mmcs = TapTreeMmcs::new(DefaultSyncBcManager::new(), query_times);
        let (commits, prover_datas) = mmcs.commit(inputs);

        for query_index in 0..8 {
            for query_times_index in 0..query_times {
                let (openings, proof) =
                    mmcs.open_batch(query_times_index, query_index, &prover_datas);
                mmcs.verify_batch(query_times_index, &openings, &proof, &commits)
                    .unwrap();
            }
        }
    }
}
