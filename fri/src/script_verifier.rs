use alloc::vec;
use alloc::vec::Vec;
use core::panic;
use std::collections::BTreeMap;
use std::sync::{Arc, Mutex, MutexGuard};

use bitcoin::taproot::TapLeaf;
use bitcoin_script_stack::stack::StackTracker;
use itertools::izip;
use p3_field::AbstractField;
use p3_util::reverse_bits_len;
use primitives::field::BfField;
use primitives::mmcs::bf_mmcs::BFMmcs;
use primitives::mmcs::point::{Point, PointsLeaf};
use primitives::mmcs::taptree_mmcs::CommitProof;
use script_expr::{Dsl, InputManager, ManagerAssign};
use scripts::u31_lib::{u31_equalverify, u31ext_equalverify, BabyBear4};
use scripts::{execute_script_with_inputs, BabyBear};
use tracing::{instrument, trace};

use crate::error::{FriError, SVError};
use crate::verifier::*;
use crate::{BfQueryProof, FriConfig, FriGenericConfigWithExpr, FriProof};

pub fn bf_verify_challenges<G, F, M, Witness>(
    g: &G,
    config: &FriConfig<M>,
    proof: &FriProof<F, M, Witness, G::InputProof>,
    challenges: &FriChallenges<F>,
    open_input: impl Fn(
        usize,
        &G::InputProof,
        MutexGuard<Box<InputManager>>,
    ) -> Result<Vec<(usize, Dsl<F>)>, G::InputError>,
) -> Result<ManagerAssign, FriError<M::Error, G::InputError>>
where
    F: BfField,
    M: BFMmcs<F, Proof = CommitProof<F>>,
    G: FriGenericConfigWithExpr<F>,
{
    let log_max_height = proof.commit_phase_commits.len() + config.log_blowup;
    let mut manager_assign = ManagerAssign::new();
    for (&index, query_proof) in izip!(&challenges.query_indices, &proof.query_proofs,) {
        let cur_manager = manager_assign
            .next_manager_with_name(format!("[fri-pcs-verify query_index:{}] ", index));
        let ro = {
            let mut manager: std::sync::MutexGuard<Box<InputManager>> = cur_manager.lock().unwrap();
            open_input(index, &query_proof.input_proof, manager)
                .map_err(|e| FriError::InputError(e))?
        };
        let folded_eval = bf_verify_query(
            g,
            config,
            &proof.commit_phase_commits,
            index,
            query_proof,
            &challenges.betas,
            ro,
            log_max_height,
            &cur_manager,
        )?;

        {
            let mut manager = cur_manager.lock().unwrap();
            let final_poly_input = manager.assign_input_f::<F>(proof.final_poly);
            manager.set_exec_dsl(folded_eval.equal(final_poly_input).into());
        }
    }

    Ok(manager_assign)
}

fn bf_verify_query<G, F, M>(
    g: &G,
    config: &FriConfig<M>,
    commit_phase_commits: &[M::Commitment],
    mut index: usize,
    proof: &BfQueryProof<F, G::InputProof>,
    betas: &[F],
    reduced_openings: Vec<(usize, Dsl<F>)>,
    log_max_height: usize,
    manager: &Arc<Mutex<Box<InputManager>>>,
) -> Result<Dsl<F>, FriError<M::Error, G::InputError>>
where
    F: BfField,
    M: BFMmcs<F, Proof = CommitProof<F>>,
    G: FriGenericConfigWithExpr<F>,
{
    let mut ro_iter = reduced_openings.into_iter().peekable();
    let mut folded_eval = Dsl::<F>::zero();

    let rev_index_dsl = Dsl::<F>::reverse_bits_len::<BabyBear>(index as u32, log_max_height as u32);

    let mut x = rev_index_dsl.index_to_rou_dsl(log_max_height as u32);

    let rev_index = reverse_bits_len(index, log_max_height);
    let mut x_hint = F::two_adic_generator(log_max_height).exp_u64(rev_index as u64);

    // let mut x = manager
    //     .lock()
    //     .unwrap()
    //     .assign_input::<F>(x_hint.as_u32_vec());

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
        let sibling_point: Point<F> = poins_leaf
            .get_point_by_index(index_sibling)
            .unwrap()
            .clone();

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

        trace!(
            "log_folded_height:{}; open_index:{}; open index_sibling:{}; point_index:{} ",
            log_folded_height,
            index,
            index_sibling,
            point_index
        );

        folded_eval = {
            let mut cur_manager: MutexGuard<Box<InputManager>> = manager.lock().unwrap();
            g.fold_row_with_expr(
                folded_eval,
                cur_manager.assign_input_f::<F>(sibling_point.y),
                x.clone(),
                x_hint,
                point_index,
                index_sibling,
                cur_manager.assign_input_f::<F>(beta),
                cur_manager,
            )
        };

        index = index_pair;
        if log_folded_height != 1 {
            x = x.square();
            x_hint = x_hint * x_hint;
        }
    }

    debug_assert!(index < config.blowup(), "index was {}", index);

    Ok(folded_eval)
}
