// use std::str::pattern::SearchStep;

use std::cmp::Reverse;
use std::marker::PhantomData;
use std::slice::Iter;
use std::sync::{Arc, Mutex};

use bitcoin::taproot::{LeafNode, NodeInfo, TaprootMerkleBranch};
use bitcoin::{ScriptBuf, TapNodeHash};
use bitcoin_script::{define_pushable, script};
use bitcomm::{BcManagerIns, BcOperator, SecretGenIns, Winternitz};
use complete_taptree::{verify_inclusion, CompleteTaptree};
use error::TCSError;
use itertools::Itertools;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_util::log2_ceil_usize;
use primitives::{
    BCManager, BCommitOperator, BCommitWithSecret, CommitType, CompressType, SecretGen,
};
use scripts::execute_script_with_inputs;
use serde::{Deserialize, Serialize};

use crate::field::BfField;
define_pushable!();

pub mod builder;
pub mod complete_taptree;
pub mod error;

pub type SG = SecretGenIns;
pub type B = Winternitz;
pub type BO = BcOperator<B>;
pub type BM = BcManagerIns<SG, B, BO>;
pub type DefaultSyncBcManager = SyncBcManager<BM, SG, BO, B>;

#[derive(Clone)]
pub struct SyncBcManager<
    BM: BCManager<SG, B, BC>,
    SG: SecretGen,
    BC: BCommitOperator<B>,
    B: BCommitWithSecret,
> {
    bc_manager: Arc<Mutex<Box<BM>>>,
    _marker: PhantomData<(SG, BC, B)>,
}

impl<BM: BCManager<SG, B, BC>, SG: SecretGen, BC: BCommitOperator<B>, B: BCommitWithSecret> Default for SyncBcManager<BM, SG, BC, B> {
    fn default() -> Self {
        Self::new()
    }
}

impl<BM: BCManager<SG, B, BC>, SG: SecretGen, BC: BCommitOperator<B>, B: BCommitWithSecret>
    SyncBcManager<BM, SG, BC, B>
{
    fn assign_bc(&self, ct: CommitType) -> BC {
        self.bc_manager.lock().unwrap().assign_bc(ct)
    }

    pub fn new() -> Self {
        Self {
            bc_manager: Arc::new(Mutex::new(Box::new(BM::new(SG::new())))),
            _marker: PhantomData,
        }
    }
}

#[derive(Clone)]
pub struct TCS<
    BM: BCManager<SG, B, BC>,
    SG: SecretGen,
    BC: BCommitOperator<B>,
    B: BCommitWithSecret,
> {
    bc_manager: SyncBcManager<BM, SG, BC, B>,
    _marker: PhantomData<(SG, BC, B)>,
}

#[derive(Clone)]
pub struct CommitedData<F: BfField, BC: BCommitOperator<B>, B: BCommitWithSecret> {
    pub(crate) leaves: Vec<RowMajorMatrix<F>>,
    pub(crate) commit_leaves: Vec<CommitedLeaf<F, BC, B>>,
    pub(crate) commit_taptree: CompleteTaptree,
    pub(crate) use_bcs: UseBComm<BC, B>,
}

impl<F: BfField, BC: BCommitOperator<B>, B: BCommitWithSecret> CommitedData<F, BC, B> {
    pub(crate) fn get_max_height(&self) -> usize {
        let mut max_height = 0;
        for matrix in &self.leaves {
            max_height = max_height.max(matrix.height());
        }
        max_height
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct CommitedProof<BC: BCommitOperator<B>, B: BCommitWithSecret> {
    leaf: LeafNode,
    use_bcs: UseBComm<BC, B>,
    query_index: usize,
}

type CommitProofAlias<BC, B> = (LeafNode, UseBComm<BC, B>, usize);

impl<BC: BCommitOperator<B>, B: BCommitWithSecret> From<CommitProofAlias<BC, B>>
    for CommitedProof<BC, B>
{
    fn from(alias: CommitProofAlias<BC, B>) -> Self {
        CommitedProof {
            leaf: alias.0,
            use_bcs: alias.1,
            query_index: alias.2,
        }
    }
}

impl<BC: BCommitOperator<B>, B: BCommitWithSecret> CommitedProof<BC, B> {
    fn to_commited_leaf<F: BfField>(self, evaluations: Vec<F>) -> CommitedLeaf<F, BC, B> {
        CommitedLeaf {
            index: self.query_index,
            evaluations,
            use_bcs: self.use_bcs,
            _marker: PhantomData,
        }
    }
}

impl<F: BfField, BC: BCommitOperator<B>, B: BCommitWithSecret> CommitedData<F, BC, B> {
    fn query_proof(&self, query_index: usize) -> CommitedProof<BC, B> {
        let tapleaf = self.commit_taptree.get_tapleaf(query_index).unwrap();
        (tapleaf.clone(), self.use_bcs.clone(), query_index).into()
    }
}

pub fn verify_proof(root: TapNodeHash, leaf: &LeafNode, witness: Vec<Vec<u8>>) -> bool {
    let inclusion = verify_inclusion(root, leaf);
    let success = execute_script_with_inputs(leaf.script().unwrap().into(), witness).success;
    inclusion && success
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct CommitedLeaf<F: BfField, BC: BCommitOperator<B>, B: BCommitWithSecret> {
    use_bcs: UseBComm<BC, B>,
    index: usize,
    evaluations: Vec<F>,
    _marker: PhantomData<B>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct UseBComm<BC: BCommitOperator<B>, B: BCommitWithSecret> {
    index_bc: BC,
    evaluations_bc: Vec<BC>,
    _marker: PhantomData<B>,
}

impl<F: BfField, BC: BCommitOperator<B>, B: BCommitWithSecret> CommitedLeaf<F, BC, B> {
    fn new_with_bcs(bcs: UseBComm<BC, B>, index: usize, evaluations: Vec<F>) -> Self {
        Self {
            use_bcs: bcs,
            index,
            evaluations,
            _marker: PhantomData,
        }
    }

    fn generate_witness(&mut self) -> Vec<Vec<u8>> {
        self.set_commited_value();
        let mut witness = vec![];
        self.use_bcs.evaluations_bc.iter().rev().for_each(|bc| {
            witness.append(&mut bc.witness());
        });

        witness.append(&mut self.use_bcs.index_bc.witness());
        witness
    }

    fn set_commited_value(&mut self) {
        self.use_bcs
            .index_bc
            .set_commit_value((self.index as u32).into());
        self.use_bcs
            .evaluations_bc
            .iter_mut()
            .enumerate()
            .for_each(|(index, bc)| {
                bc.set_commit_value(self.evaluations[index].as_u32_vec().into());
            });
    }

    fn generate_script(&mut self) -> ScriptBuf {
        self.set_commited_value();
        let mut exec_scripts = script! {
            {self.use_bcs.index_bc.locking_script_with_type(CompressType::U32).compile() }
            {self.index}
            OP_EQUALVERIFY
        };

        self.use_bcs
            .evaluations_bc
            .iter()
            .enumerate()
            .for_each(|(index, bc)| {
                let values = self.evaluations[index].as_u32_vec();
                exec_scripts = script! {
                    {exec_scripts.clone()}
                    { bc.locking_script_with_type(CompressType::U32).compile() }
                    for i in (0..values.len()).rev() {
                        {values[i]}
                        OP_EQUALVERIFY
                    }
                };
            });

        script! {
            {exec_scripts}
            OP_1
        }
    }
}

impl<BM: BCManager<SG, B, BC>, SG: SecretGen, BC: BCommitOperator<B>, B: BCommitWithSecret>
    PolyTCS<BM, SG, BC, B> for TCS<BM, SG, BC, B>
{
    fn new(manager: SyncBcManager<BM, SG, BC, B>) -> Self {
        Self {
            bc_manager: manager,
            _marker: PhantomData,
        }
    }

    fn new_wtih_query_proof(query_proof: impl TaptreeConcater) -> Self {
        unimplemented!()
    }

    fn commit_polys<F: BfField>(&self, leaves: Vec<RowMajorMatrix<F>>) -> CommitedData<F, BC, B> {
        let commit_type = match F::U32_SIZE {
            1 => CommitType::U32,
            4 => CommitType::U128,
            _ => {
                panic!("only support 1 or 4");
            }
        };

        let leaf_ys = self.padding_matrix(leaves.iter());

        let first_width = leaf_ys[0].len();
        let max_height = leaf_ys.len();
        // assign bc here
        let index_bc = self.bc_manager.assign_bc(CommitType::U32);
        let evaluations_bc: Vec<BC> = (0..first_width)
            .map(|_index| self.bc_manager.assign_bc(commit_type.clone()))
            .collect();
        let use_bcs = UseBComm {
            index_bc,
            evaluations_bc,
            _marker: PhantomData,
        };
        let mut leaves_script = vec![];
        let mut commited_leaves = vec![];

        for index in 0..max_height {
            if !leaf_ys[index].is_empty() {
                //println!("index:{:?}, ys:{:?}", index, leaf_ys[index]);
                let mut to_commit_leaf =
                    CommitedLeaf::new_with_bcs(use_bcs.clone(), index, leaf_ys[index].clone());
                leaves_script.push(to_commit_leaf.generate_script());
                commited_leaves.push(to_commit_leaf);
            }
        }

        // generate commit taptree
        let commit_tree = CompleteTaptree::new_with_scripts(leaves_script);
        CommitedData {
            leaves,
            commit_leaves: commited_leaves,
            commit_taptree: commit_tree,
            use_bcs,
        }
    }

    fn commit_poly_with_query_times<F: BfField>(
        &self,
        polys: Vec<RowMajorMatrix<F>>,
        total_query_times: usize,
    ) -> Vec<CommitedData<F, BC, B>> {
        (0..total_query_times)
            .map(|_| self.commit_polys(polys.clone()))
            .collect()
    }

    fn open<F: BfField>(
        &self,
        index: usize,
        prover_data: &CommitedData<F, BC, B>,
    ) -> (CommitedProof<BC, B>, Vec<F>) {
        let leaves_evals = self.padding_matrix(prover_data.leaves.iter());
        (prover_data.query_proof(index), leaves_evals[index].clone())
    }

    fn open_with_query_times<F: BfField>(
        &self,
        indices: Vec<usize>,
        prover_datas: &Vec<CommitedData<F, BC, B>>,
        query_times: usize,
    ) -> (Vec<CommitedProof<BC, B>>, Vec<Vec<F>>) {
        assert_eq!(indices.len(), query_times);
        assert_eq!(prover_datas.len(), query_times);

        let proofs = (0..query_times)
            .zip(indices.clone())
            .map(|(query_times_index, query_index)| {
                prover_datas[query_times_index].query_proof(query_index)
            })
            .collect();

        let leaves_evals = self.padding_matrix(prover_datas[0].leaves.iter());
        let opening_values: Vec<Vec<F>> = indices
            .iter()
            .map(|query_index| leaves_evals[*query_index].clone())
            .collect();

        (proofs, opening_values)
    }
}

// polynomial Taptree Commitment Scheme
pub trait PolyTCS<
    BM: BCManager<SG, B, BC>,
    SG: SecretGen,
    BC: BCommitOperator<B>,
    B: BCommitWithSecret,
>
{
    fn new(manager: SyncBcManager<BM, SG, BC, B>) -> Self;

    fn new_wtih_query_proof(query_proof: impl TaptreeConcater) -> Self;

    fn padding_matrix<F: BfField>(
        &self,
        leaves: Iter<'_, p3_matrix::dense::DenseMatrix<F>>,
    ) -> Vec<Vec<F>> {
        //evaluations sorted by height
        let mut leaves_largest_first = leaves.sorted_by_key(|l| Reverse(l.height())).peekable();
        let max_height = leaves_largest_first.peek().unwrap().height();
        let log_max_height = log2_ceil_usize(max_height);
        //println!("max height:{:?}", max_height);
        let mut leaf_ys = vec![vec![]; max_height];

        for log_height in (0..log_max_height + 1).rev() {
            let matrices = leaves_largest_first
                .peeking_take_while(|m| log2_ceil_usize(m.height()) == log_height)
                .collect_vec();
            if !matrices.is_empty() {
                let curr_height = matrices[0].height();
                for matrix in matrices.iter() {
                    let width = matrix.width();
                    for index in 0..curr_height {
                        //find which leaf to store
                        let curr_index = index << (log_max_height - log_height);
                        let next_index = (index + 1) << (log_max_height - log_height);
                        for i in 0..width {
                            for leaf_index in curr_index..next_index {
                                leaf_ys[leaf_index].push(matrix.values[index * matrix.width() + i]);
                            }
                        }
                    }
                }
            }
        }

        // check the leaf_ys has the same width
        let frist_width = leaf_ys[0].len();
        leaf_ys.iter().for_each(|ys| {
            assert_eq!(frist_width, ys.len());
        });
        leaf_ys
    }
    // only use for prover
    // different leaf use the same bit-comm set within the Polynomial-Commitment-Scheme-Taptree
    // index use a unique bit-comm to simulate the open-index
    // each evalutaion corresponding to each unique bitcomm within one leaf
    // the sequences of bcs: vec<index1-bitcomm,index2-bitcomm...>, vec<eval1-bitcomm, eval2-bitcomm ...>
    // return the pair (polynomial index, query_times index)  which uses to as the key of the polynomial taptree
    fn commit_polys<F: BfField>(&self, poly: Vec<RowMajorMatrix<F>>) -> CommitedData<F, BC, B>;

    // only use for prover
    // different leaf use the same bit-comm set within the Polynomial-Commitment-Scheme-Taptree
    // index use a unique bit-comm to simulate the open-index
    // each evalutaion corresponding to each unique bitcomm within one leaf
    // the sequences of bcs: index-bitcomm, eval1-bitcomm, eval2-bitcomm ...
    // return the polynomial index which uses to as the key of the polynomial taptree
    fn commit_poly_with_query_times<F: BfField>(
        &self,
        polys: Vec<RowMajorMatrix<F>>,
        total_query_times: usize,
    ) -> Vec<CommitedData<F, BC, B>>;

    fn open<F: BfField>(
        &self,
        query_index: usize,
        prover_data: &CommitedData<F, BC, B>,
    ) -> (CommitedProof<BC, B>, Vec<F>);

    fn open_with_one_query<F: BfField>(
        &self,
        query_times_index: usize,
        query_index: usize,
        prover_data: &Vec<CommitedData<F, BC, B>>,
        query_times: usize,
    ) -> (CommitedProof<BC, B>, Vec<F>) {
        assert_eq!(prover_data.len(), query_times);
        self.open(query_index, &prover_data[query_times_index])
    }

    fn open_with_query_times<F: BfField>(
        &self,
        indices: Vec<usize>,
        prover_data: &Vec<CommitedData<F, BC, B>>,
        query_times: usize,
    ) -> (Vec<CommitedProof<BC, B>>, Vec<Vec<F>>);

    fn verify<F: BfField>(
        &self,
        root: TapNodeHash,
        proof: &CommitedProof<BC, B>,
        opening_values: Vec<F>,
    ) -> bool {
        // genreate the witness by constrcting the CommitedLeaf
        let mut commited_leaf = proof.clone().to_commited_leaf(opening_values);

        verify_proof(root, &proof.leaf, commited_leaf.generate_witness())
    }

    fn verify_with_query_times<F: BfField>(
        &self,
        root: Vec<TapNodeHash>,
        proofs: &Vec<CommitedProof<BC, B>>,
        opening_values: Vec<Vec<F>>,
        query_times: usize,
    ) -> bool {
        let mut success = true;
        for query_times_index in 0..query_times {
            if !success {
                return false;
            }
            success = self.verify(
                root[query_times_index],
                &proofs[query_times_index],
                opening_values[query_times_index].clone(),
            );
        }
        success
    }
    // each poly only support one query
    // return the taptree_root,the tapleaf which should be opened, the merklepath for the opening tapleaf, and the bcs set
}

trait TaptreeConcater {
    fn new_with_scripts(scripts: Vec<impl ScriptToEmbbed>) -> Self;

    fn combine_other_script(&mut self, slash_scripts: Vec<impl ScriptToEmbbed>) -> Self;

    fn combine(&self, other: impl TaptreeConcater) -> Self;

    fn get_indices(&self) -> &Vec<usize>;

    fn leaf_count(&self) -> usize;

    fn get_root(&self) -> &NodeInfo;

    //
    fn get_leaf_proof(&self, index: usize) -> (LeafNode, TaprootMerkleBranch);
}

trait FinalTaptree {
    fn to_taproot(&self) -> TapNodeHash;
}

pub fn combine_two_nodes(a: NodeInfo, b: NodeInfo) -> Result<(NodeInfo, bool), TCSError> {
    let parent = NodeInfo::combine_with_order(a, b)?;
    Ok(parent)
}

trait ScriptToEmbbed {
    fn prefix_concat(&self) -> ScriptBuf {
        ScriptBuf::new()
    }

    fn suffix_concat(&self) -> ScriptBuf {
        ScriptBuf::new()
    }

    fn origin_script(&self) -> ScriptBuf;

    fn compelte_script(&self) -> ScriptBuf {
        script! {
            {self.prefix_concat()}
            {self.origin_script()}
            {self.suffix_concat()}
        }
    }
}

impl ScriptToEmbbed for ScriptBuf {
    fn origin_script(&self) -> ScriptBuf {
        self.clone()
    }
}

// struct IncompleteTaptree{
//     root: NodeInfo,
//     leaves: Vec<(Tapleaf,MerklePath,Vec<BitComm>)>,
// }

// impl TaptreeConcater for IncompleteTaptree{
//     fn combine_other_taptree(&mut self, slash_scripts: Vec<Script>);
//     // 现在存在的问题在于，我们如果把TCSQueryTaptree给到Xaiver这边，他那边发现有script有问题怎么执行？怎么找到对应的index呢？
//     // 解决方案： 研究下原来的实现里是怎构造Taptree 以及怎么生成 MerklePath的

//     fn new(scripts: Vec<Script>) -> Self;

//     fn combine(&self, other: Self) -> Self;

//     fn get_idx(&self,index: usize) -> (Tapleaf,MerklePath,Vec<BitComm>);

//     fn combine_script_into_stark() -> Self;

//     fn to_taproot_info() -> TaprootInfo;
// }

#[cfg(test)]
mod tests {

    use bitcomm::{BcManagerIns, BcOperator, SecretGenIns, Winternitz};
    use p3_baby_bear::BabyBear;
    use p3_field::AbstractField;
    use p3_matrix::dense::RowMajorMatrix;

    use super::*;
    type F = BabyBear;
    type BCS = Winternitz;
    type BCP = BcOperator<Winternitz>;
    type BM = BcManagerIns<SecretGenIns, BCS, BCP>;

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

        let manager = DefaultSyncBcManager::new();
        let inputs = vec![mat_1, mat_2, mat_3];
        let tcs = TCS::new(manager);
        let commit_data = tcs.commit_polys(inputs);

        (0..7).for_each(|index| {
            let (proof, opening) = tcs.open(index, &commit_data);
            assert!(tcs.verify(commit_data.commit_taptree.root().hash, &proof, opening));
        })
    }

    #[test]
    fn test_taptree_mmcs_with_multi_query() {
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

        let manager = DefaultSyncBcManager::new();
        let inputs = vec![mat_1, mat_2, mat_3];
        let tcs = TCS::new(manager);
        let query_times = 8;
        let commit_data = tcs.commit_poly_with_query_times::<BabyBear>(inputs, query_times);

        let roots: Vec<TapNodeHash> = commit_data
            .iter()
            .map(|data| data.commit_taptree.root().hash)
            .collect();

        (0..7).for_each(|index| {
            let (proof, opening) = tcs.open_with_query_times::<BabyBear>(
                vec![index; query_times],
                &commit_data,
                query_times,
            );
            assert!(tcs.verify_with_query_times(roots.clone(), &proof, opening, query_times));
        })
    }
}
