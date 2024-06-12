// use alloc::vec::Vec;
// use core::marker::PhantomData;
// use core::usize;

// use bf_scripts::{BfBaseField, BfExtensionField};
// use bitcoin::TapNodeHash;
// use p3_commit::{DirectMmcs, ExtensionMatrix, Mmcs};
// use p3_matrix::dense::RowMajorMatrix;
// use p3_matrix::{Dimensions, Matrix};
// use p3_util::log2_strict_usize;

// use super::error::BfError;
// use crate::prover::DEFAULT_MATRIX_WIDTH;
// use crate::taptree::PolyCommitTree;
// use crate::BfCommitPhaseProofStep;
// #[derive(Clone, Debug, PartialEq, PartialOrd)]
// pub struct ExtensionTapTreeMmcs<
//     F: BfBaseField,
//     EF: BfExtensionField<F>,
//     const NUM_POLY: usize,
//     InnerMmcs,
// > {
//     inner: InnerMmcs,
//     _marker: PhantomData<(F, EF)>,
// }

// impl<F: BfBaseField, EF: BfExtensionField<F>, const NUM_POLY: usize, InnerMmcs>
//     ExtensionTapTreeMmcs<F, EF, NUM_POLY, InnerMmcs>
// {
//     pub fn new(inner: InnerMmcs) -> Self {
//         Self {
//             inner,
//             _marker: PhantomData,
//         }
//     }
// }

// impl<F: BfBaseField, EF: BfExtensionField<F>, const NUM_POLY: usize, InnerMmcs: Mmcs<F>> Mmcs<EF>
//     for ExtensionTapTreeMmcs<F, EF, NUM_POLY, InnerMmcs>
// {
//     type ProverData = PolyCommitTree<NUM_POLY>;
//     type Proof = BfCommitPhaseProofStep;
//     type Commitment = TapNodeHash;
//     type Error = BfError;
//     type Mat<'a> = ExtensionMatrix<F, EF, InnerMmcs::Mat<'a>> where Self: 'a;

//     fn open_batch(
//         &self,
//         index: usize,
//         prover_data: &PolyCommitTree<NUM_POLY>,
//     ) -> (Vec<Vec<EF>>, Self::Proof) {
//         unimplemented!()
//     }

//     fn open_taptree(&self, index: usize, prover_data: &PolyCommitTree<NUM_POLY>) -> Self::Proof {
//         let opening_leaf = prover_data.get_leaf(index).unwrap().clone();
//         let merkle_branch = opening_leaf.merkle_branch().clone();
//         let leaf = opening_leaf.leaf().clone();
//         BfCommitPhaseProofStep {
//             leaf_node: leaf,
//             merkle_branch: merkle_branch,
//         }
//     }

//     fn verify_taptree(
//         &self,
//         proof: &Self::Proof,
//         root: &Self::Commitment,
//     ) -> Result<(), Self::Error> {
//         let mut first_node_hash = TapNodeHash::from_node_hashes(*root, proof.merkle_branch[0]);
//         proof.merkle_branch[1..]
//             .into_iter()
//             .for_each(|sibling_node| {
//                 first_node_hash = TapNodeHash::from_node_hashes(first_node_hash, *sibling_node);
//             });
//         if root.clone() == first_node_hash {
//             Ok(())
//         } else {
//             Err(BfError::InvalidMerkleProof)
//         }
//     }

//     fn get_matrices<'a>(&'a self, prover_data: &'a Self::ProverData) -> Vec<Self::Mat<'a>> {
//         unimplemented!();
//     }

//     fn get_max_height(&self, prover_data: &Self::ProverData) -> usize {
//         unimplemented!();
//     }

//     fn verify_batch(
//         &self,
//         commit: &Self::Commitment,
//         dimensions: &[Dimensions],
//         index: usize,
//         opened_values: &[Vec<EF>],
//         proof: &Self::Proof,
//     ) -> Result<(), Self::Error> {
//         unimplemented!();
//     }
// }

// impl<F: BfBaseField, EF: BfExtensionField<F>, const NUM_POLY: usize, InnerMmcs> DirectMmcs<EF>
//     for ExtensionTapTreeMmcs<F, EF, NUM_POLY, InnerMmcs>
// where
//     InnerMmcs: Mmcs<F>,
// {
//     fn commit(&self, inputs: Vec<RowMajorMatrix<EF>>) -> (Self::Commitment, Self::ProverData) {
//         assert_eq!(inputs.len(), 1);
//         assert_eq!(inputs[0].width, DEFAULT_MATRIX_WIDTH);

//         let log_leaves = log2_strict_usize(inputs[0].height());
//         let mut tree = PolyCommitTree::<NUM_POLY>::new(log_leaves);

//         tree.commit_rev_extension_points(inputs[0].values.clone(), inputs[0].width);
//         let root = tree.root().clone();
//         (root.node_hash(), tree)
//     }
// }
