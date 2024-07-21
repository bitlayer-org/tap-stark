use alloc::vec;
use alloc::vec::Vec;
use core::panic;

use bitcoin::taproot::TapLeaf;
use bitcoin::Script;
use itertools::izip;
use p3_challenger::{CanObserve, CanSample};
use p3_field::AbstractField;
use p3_util::reverse_bits_len;
use primitives::challenger::BfGrindingChallenger;
use primitives::field::BfField;
use primitives::mmcs::bf_mmcs::BFMmcs;
use primitives::mmcs::point::{Point, PointsLeaf};
use primitives::mmcs::taptree_mmcs::CommitProof;
use script_expr::{Expression, FieldScriptExpression, NumScriptExpression};
use script_manager::bc_assignment::{BCAssignment, DefaultBCAssignment};
use script_manager::script_info::ScriptInfo;
use scripts::execute_script_with_inputs;
use segment::SegmentLeaf;
use tracing::field::Field;

use crate::error::{FriError, SVError};
use crate::verifier::*;
use crate::{BfQueryProof, FriConfig, FriGenericConfig, FriGenericConfigWithExpr, FriProof};

pub fn bf_verify_challenges<G, F, M, Witness>(
    g: &G,
    config: &FriConfig<M>,
    proof: &FriProof<F, M, Witness, G::InputProof>,
    challenges: &FriChallenges<F>,
    open_input: impl Fn(
        usize,
        &G::InputProof,
    ) -> Result<Vec<(usize, FieldScriptExpression<F>)>, G::InputError>,
) -> Result<Vec<FieldScriptExpression<F>>, FriError<M::Error, G::InputError>>
where
    F: BfField,
    M: BFMmcs<F, Proof = CommitProof<F>>,
    G: FriGenericConfigWithExpr<F, FieldScriptExpression<F>>,
{
    let log_max_height = proof.commit_phase_commits.len() + config.log_blowup;
    let mut fri_exprs = vec![];
    for (&index, query_proof) in izip!(&challenges.query_indices, &proof.query_proofs,) {
        let ro =
            open_input(index, &query_proof.input_proof).map_err(|e| FriError::InputError(e))?;

        let folded_eval = bf_verify_query(
            g,
            config,
            &proof.commit_phase_commits,
            index,
            query_proof,
            &challenges.betas,
            ro,
            log_max_height,
        )?;

        fri_exprs.push(folded_eval.equal_for_f(proof.final_poly));
    }

    Ok(fri_exprs)
}

fn bf_verify_query<G, F, M>(
    g: &G,
    config: &FriConfig<M>,
    commit_phase_commits: &[M::Commitment],
    mut index: usize,
    proof: &BfQueryProof<F, G::InputProof>,
    betas: &[F],
    reduced_openings: Vec<(usize, FieldScriptExpression<F>)>,
    log_max_height: usize,
) -> Result<FieldScriptExpression<F>, FriError<M::Error, G::InputError>>
where
    F: BfField,
    M: BFMmcs<F, Proof = CommitProof<F>>,
    G: FriGenericConfigWithExpr<F, FieldScriptExpression<F>>,
{
    let mut ro_iter = reduced_openings.into_iter().peekable();
    let mut folded_eval = FieldScriptExpression::<F>::zero();

    let rev_index = reverse_bits_len(index, log_max_height);
    let mut x = NumScriptExpression::from(rev_index as u32).index_to_rou(log_max_height as u32);

    // let generator = F::two_adic_generator(log_max_height);
    // let mut x = generator.exp_u64(rev_index as u64);

    for (log_folded_height, commit, step, &beta) in izip!(
        (0..log_max_height).rev(),
        commit_phase_commits,
        &proof.commit_phase_openings,
        betas,
    ) {
        let point_index = index & 1;
        let index_sibling = point_index ^ 1;
        let index_pair = index >> 1;

        if let Some((_, ro)) = ro_iter.next_if(|(lh, _)| *lh == log_folded_height + 1) {
            folded_eval += ro;
        }

        let poins_leaf: PointsLeaf<F> = step.points_leaf.clone();
        let challenge_point: Point<F> = poins_leaf.get_point_by_index(point_index).unwrap().clone();

        // if log_folded_height < log_max_height - 1 {
        //     assert_eq!(folded_eval, challenge_point.y);
        // }
        let sibling_point: Point<F> = poins_leaf
            .get_point_by_index(index_sibling)
            .unwrap()
            .clone();

        // assert_eq!(challenge_point.x, x);
        // let neg_x = x * F::two_adic_generator(1);
        // assert_eq!(sibling_point.x, neg_x);

        let mut evals = vec![folded_eval.clone(); 2];
        evals[index_sibling % 2] = sibling_point.y.into(); // sibling_point.y is field_script_expression::input_variable

        // let mut xs = vec![x; 2];
        // xs[index_sibling % 2] = neg_x;

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
        println!("log_folded_height:{}", log_folded_height);
        (folded_eval, _) = g.fold_row_with_expr(
            index,
            log_folded_height,
            folded_eval.clone(),
            sibling_point.y.into(),
            x.clone(),
            point_index,
            index_sibling,
            beta.into(),
        );

        // folded_eval_value = g.fold_row(index, log_folded_height, beta, evals.into_iter());
        // folded_eval.clone().equal_for_f(fold)
        if log_folded_height != 1 {
            x = x.clone() * x.clone();
        }
    }

    debug_assert!(index < config.blowup(), "index was {}", index);

    Ok(folded_eval)
}
