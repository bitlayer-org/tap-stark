use alloc::vec;
use alloc::vec::Vec;
use core::panic;

use bitcoin::taproot::TapLeaf;
use bitcoin::Script;
use itertools::izip;
use p3_challenger::{CanObserve, CanSample};
use p3_util::reverse_bits_len;
use primitives::challenger::BfGrindingChallenger;
use primitives::field::BfField;
use primitives::mmcs::bf_mmcs::BFMmcs;
use primitives::mmcs::point::{Point, PointsLeaf};
use primitives::mmcs::taptree_mmcs::CommitProof;
use script_manager::bc_assignment::{BCAssignment, DefaultBCAssignment};
use script_manager::script_info::ScriptInfo;
use scripts::execute_script_with_inputs;
use segment::SegmentLeaf;

use crate::error::{FriError, SVError};
use crate::fri_scripts::leaf::{
    CalNegXLeaf, IndexToROULeaf, ReductionLeaf, RevIndexLeaf, SquareFLeaf, VerifyFoldingLeaf,
};
use crate::verifier::*;
use crate::{BfQueryProof, FriConfig, FriGenericConfig, FriProof};

pub fn bf_verify_challenges<G, F, M, Witness>(
    g: &G,
    assign: &mut DefaultBCAssignment,
    config: &FriConfig<M>,
    proof: &FriProof<F, M, Witness, G::InputProof>,
    challenges: &FriChallenges<F>,
    script_manager: &mut Vec<ScriptInfo>,
    open_input: impl Fn(
        usize,
        &G::InputProof,
        &mut Vec<ScriptInfo>,
    ) -> Result<Vec<(usize, F)>, G::InputError>,
) -> Result<(), FriError<M::Error, G::InputError>>
where
    F: BfField,
    M: BFMmcs<F, Proof = CommitProof<F>>,
    G: FriGenericConfig<F>,
{
    let log_max_height = proof.commit_phase_commits.len() + config.log_blowup;
    for (&index, query_proof) in izip!(&challenges.query_indices, &proof.query_proofs,) {
        let ro = open_input(index, &query_proof.input_proof, script_manager)
            .map_err(|e| FriError::InputError(e))?;

        let folded_eval = bf_verify_query(
            g,
            assign,
            config,
            &proof.commit_phase_commits,
            index,
            query_proof,
            &challenges.betas,
            ro,
            log_max_height,
        )?;

        if folded_eval != proof.final_poly {
            return Err(FriError::FinalPolyMismatch);
        }
    }

    Ok(())
}

fn bf_verify_query<G, F, M>(
    g: &G,
    assign: &mut DefaultBCAssignment,
    config: &FriConfig<M>,
    commit_phase_commits: &[M::Commitment],
    mut index: usize,
    proof: &BfQueryProof<F, G::InputProof>,
    betas: &[F],
    reduced_openings: Vec<(usize, F)>,
    log_max_height: usize,
) -> Result<F, FriError<M::Error, G::InputError>>
where
    F: BfField,
    M: BFMmcs<F, Proof = CommitProof<F>>,
    G: FriGenericConfig<F>,
{
    let mut folded_eval = F::zero();
    let mut ro_iter = reduced_openings.into_iter().peekable();

    let rev_index = reverse_bits_len(index, log_max_height);
    let rev_index_leaf = RevIndexLeaf::new_from_assign(
        log_max_height as u32,
        index as u32,
        rev_index as u32,
        assign,
    );
    let exec_success = rev_index_leaf.execute_leaf_script();
    if !exec_success {
        return Err(FriError::ScriptVerifierError(
            SVError::VerifyReverseIndexScriptError,
        ));
    }

    let generator = F::two_adic_generator(log_max_height);
    let mut x = generator.exp_u64(rev_index as u64);
    let index_to_rou_leaf =
        IndexToROULeaf::<1, F>::new_from_assign(rev_index, log_max_height, x, assign);
    assert_eq!(index_to_rou_leaf.generator(), generator);
    let exec_success = index_to_rou_leaf.execute_leaf_script();
    if !exec_success {
        return Err(FriError::ScriptVerifierError(
            SVError::VerifyIndexToROUScriptError,
        ));
    }

    for (log_folded_height, commit, step, &beta) in izip!(
        (0..log_max_height).rev(),
        commit_phase_commits,
        &proof.commit_phase_openings,
        betas,
    ) {
        let point_index = index & 1;
        let index_sibling = point_index ^ 1;
        // let index_sibling = index ^ 1;
        let index_pair = index >> 1;

        if let Some((_, ro)) = ro_iter.next_if(|(lh, _)| *lh == log_folded_height + 1) {
            let reduction_leaf =
                ReductionLeaf::<1, F>::new_from_assign(folded_eval, ro, folded_eval + ro, assign);
            let exec_success = reduction_leaf.execute_leaf_script();
            if !exec_success {
                return Err(FriError::ScriptVerifierError(
                    SVError::VerifyReductionScriptError,
                ));
            }

            println!("ro:{}", ro);
            folded_eval += ro;
        }

        let poins_leaf: PointsLeaf<F> = step.points_leaf.clone();
        let challenge_point: Point<F> = poins_leaf.get_point_by_index(point_index).unwrap().clone();

        if log_folded_height < log_max_height - 1 {
            assert_eq!(folded_eval, challenge_point.y);
        }
        let sibling_point: Point<F> = poins_leaf
            .get_point_by_index(index_sibling)
            .unwrap()
            .clone();

        // assert_eq!(challenge_point.x, x);
        let neg_x = x * F::two_adic_generator(1);
        let cal_negx_leaf = CalNegXLeaf::<1, F>::new_from_assign(x, neg_x, assign);
        let exec_success = cal_negx_leaf.execute_leaf_script();
        if !exec_success {
            return Err(FriError::ScriptVerifierError(
                SVError::VerifyCalNegXScriptError,
            ));
        }
        // assert_eq!(sibling_point.x, neg_x);

        let mut evals = vec![folded_eval; 2];
        evals[index_sibling % 2] = sibling_point.y;

        let mut xs = vec![x; 2];
        xs[index_sibling % 2] = neg_x;

        let input = poins_leaf.witness();
        if let TapLeaf::Script(script, _ver) = step.leaf_node.leaf().clone() {
            assert_eq!(script, poins_leaf.recover_points_euqal_to_commited_point());
            let res = execute_script_with_inputs(
                poins_leaf.recover_points_euqal_to_commited_point(),
                input,
            );
            if !res.success {
                return Err(FriError::ScriptVerifierError(
                    SVError::VerifyCommitedPointError,
                ));
            }
            assert_eq!(res.success, true);
        } else {
            panic!("Invalid script")
        }

        config
            .mmcs
            .verify_taptree(step, commit)
            .map_err(FriError::CommitPhaseMmcsError)?;

        index = index_pair;
        folded_eval = g.fold_row(index, log_folded_height, beta, evals.into_iter());
        let folding_leaf = VerifyFoldingLeaf::<1, F>::new_from_assign(
            challenge_point.y,
            sibling_point.y,
            x,
            beta,
            folded_eval,
            assign,
        );
        let exec_success = folding_leaf.execute_leaf_script();
        if !exec_success {
            return Err(FriError::ScriptVerifierError(
                SVError::VerifyFoldingScriptError,
            ));
        }
        x = x.square();
        let square_leaf = SquareFLeaf::<1, F>::new_from_assign(x, x.square(), assign);
        let exec_success = square_leaf.execute_leaf_script();
        if !exec_success {
            return Err(FriError::ScriptVerifierError(
                SVError::VerifySquareFScriptError,
            ));
        }
    }

    debug_assert!(index < config.blowup(), "index was {}", index);
    debug_assert_eq!(x.exp_power_of_2(config.log_blowup), F::one());

    Ok(folded_eval)
}
