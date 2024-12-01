use alloc::vec::Vec;
use std::sync::{Arc, Mutex, MutexGuard};

use basic::field::BfField;
use basic::mmcs::bf_mmcs::BFMmcs;
use basic::tcs::{CommitedProof, B, BO};
use itertools::izip;
use p3_field::AbstractField;
use p3_util::reverse_bits_len;
use script_expr::{Dsl, InputManager, ManagerAssign};
use scripts::BabyBear;
use tracing::trace;

use crate::error::FriError;
use crate::verifier::*;
use crate::{BfQueryProof, FriConfig, FriGenericConfigWithExpr, FriProof};

pub fn bf_verify_challenges<G, F, M, Witness>(
    g: &G,
    config: &FriConfig<M>,
    proof: &FriProof<F, M, Witness, G::InputProof>,
    challenges: &FriChallenges<F>,
    open_input: impl Fn(
        usize,
        usize,
        &G::InputProof,
        MutexGuard<Box<InputManager>>,
    ) -> Result<Vec<(usize, Dsl<F>)>, G::InputError>,
) -> Result<ManagerAssign, FriError<M::Error, G::InputError>>
where
    F: BfField,
    M: BFMmcs<F, Proof = CommitedProof<BO, B>>,
    G: FriGenericConfigWithExpr<F>,
{
    let log_max_height = proof.commit_phase_commits.len() + config.log_blowup;
    let mut manager_assign = ManagerAssign::new();
    for (&(query_times_index, query_index), query_proof) in
        izip!(&challenges.query_indices, &proof.query_proofs,)
    {
        let cur_manager = manager_assign
            .next_manager_with_name(format!("[fri-pcs-verify query_index:{}] ", query_index));
        let ro = {
            let manager: std::sync::MutexGuard<Box<InputManager>> = cur_manager.lock().unwrap();
            open_input(
                query_times_index,
                query_index,
                &query_proof.input_proof,
                manager,
            )
            .map_err(FriError::InputError)?
        };
        let folded_eval = bf_verify_query(
            g,
            config,
            &proof.commit_phase_commits,
            query_index,
            query_times_index,
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
    mut query_index: usize,
    query_times_index: usize,
    proof: &BfQueryProof<F, G::InputProof>,
    betas: &[F],
    reduced_openings: Vec<(usize, Dsl<F>)>,
    log_max_height: usize,
    manager: &Arc<Mutex<Box<InputManager>>>,
) -> Result<Dsl<F>, FriError<M::Error, G::InputError>>
where
    F: BfField,
    M: BFMmcs<F, Proof = CommitedProof<BO, B>>,
    G: FriGenericConfigWithExpr<F>,
{
    let mut ro_iter = reduced_openings.into_iter().peekable();
    let mut folded_eval = Dsl::<F>::zero();

    let rev_index_dsl =
        Dsl::<F>::reverse_bits_len::<BabyBear>(query_index as u32, log_max_height as u32);

    let mut x = rev_index_dsl.index_to_rou_dsl(log_max_height as u32);

    let rev_index = reverse_bits_len(query_index, log_max_height);
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
        let point_index = query_index & 1;
        let index_sibling = point_index ^ 1;
        let index_pair = query_index >> 1;

        if let Some((_, ro)) = ro_iter.next_if(|(lh, _)| *lh == log_folded_height + 1) {
            folded_eval += ro;
        }

        // the opening values len should be 1, becuase we only commit one matrix.
        assert_eq!(step.0.len(), 1);
        let opening_values = step.0.clone();
        let commited_proof = step.1.clone();

        config
            .mmcs
            .verify_batch(query_times_index, &opening_values, &commited_proof, commit)
            .map_err(FriError::CommitPhaseMmcsError)?;
        trace!(
            "log_folded_height:{}; open_index:{}; open index_sibling:{}; point_index:{} ",
            log_folded_height,
            query_index,
            index_sibling,
            point_index
        );

        folded_eval = {
            let mut cur_manager: MutexGuard<Box<InputManager>> = manager.lock().unwrap();
            g.fold_row_with_expr(
                folded_eval,
                cur_manager.assign_input_f::<F>(opening_values[0][index_sibling]),
                x.clone(),
                x_hint,
                point_index,
                index_sibling,
                cur_manager.assign_input_f::<F>(beta),
                cur_manager,
            )
        };

        query_index = index_pair;
        if log_folded_height != 1 {
            x = x.square();
            x_hint = x_hint * x_hint;
        }
    }

    debug_assert!(query_index < config.blowup(), "index was {}", query_index);

    Ok(folded_eval)
}
