use alloc::vec;
use alloc::vec::Vec;

use scripts::{execute_script_with_inputs}; 
 use crate::fri_script::point::{Point, PointsLeaf};
use primitives::field::{BfField};
use bitcoin::taproot::TapLeaf;
use bitcoin::Script;
use itertools::izip;

use p3_challenger::{ CanObserve, CanSample};

use p3_util::reverse_bits_len;
use primitives::challenger::BfGrindingChallenger;
use crate::bf_mmcs::BFMmcs;
use crate::error::{BfError, FriError};
use crate::{BfCommitPhaseProofStep, BfQueryProof, FriConfig, FriProof};

#[derive(Debug)]
pub struct FriChallenges<F> {
    pub query_indices: Vec<usize>,
    pub(crate) betas: Vec<F>,
}

pub fn verify_shape_and_sample_challenges<F, M, Challenger>(
    config: &FriConfig<M>,
    proof: &FriProof<F, M, Challenger::Witness>,
    challenger: &mut Challenger,
) -> Result<FriChallenges<F>, FriError<M::Error>>
where
    F: BfField,
    M: BFMmcs<F, Proof = BfCommitPhaseProofStep<F>>,
    Challenger: BfGrindingChallenger + CanObserve<M::Commitment> + CanSample<F>,
{
    let betas: Vec<F> = proof
        .commit_phase_commits
        .iter()
        .map(|comm| {
            challenger.observe(comm.clone());
            challenger.sample()
        })
        .collect();

    if proof.query_proofs.len() != config.num_queries {
        return Err(FriError::InvalidProofShape);
    }

    // Check PoW.
    if !challenger.check_witness(config.proof_of_work_bits, proof.pow_witness) {
        return Err(FriError::InvalidPowWitness);
    }

    let log_max_height = proof.commit_phase_commits.len() + config.log_blowup;

    let query_indices: Vec<usize> = (0..config.num_queries)
        .map(|_| challenger.sample_bits(log_max_height))
        .collect();

    Ok(FriChallenges {
        query_indices,
        betas,
    })
}

pub fn verify_challenges<F, M, Witness>(
    config: &FriConfig<M>,
    proof: &FriProof<F, M, Witness>,
    challenges: &FriChallenges<F>,
    reduced_openings: &[[F; 32]],
) -> Result<(), FriError<M::Error>>
where
    F: BfField,
    M: BFMmcs<F, Proof = BfCommitPhaseProofStep<F>>,
{
    let log_max_height = proof.commit_phase_commits.len() + config.log_blowup;
    for (&index, query_proof, ro) in izip!(
        &challenges.query_indices,
        &proof.query_proofs,
        reduced_openings
    ) {
        let folded_eval = verify_query(
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

fn verify_query<F, M>(
    config: &FriConfig<M>,
    commit_phase_commits: &[M::Commitment],
    mut index: usize,
    proof: &BfQueryProof<F>,
    betas: &[F],
    reduced_openings: &[F; 32],
    log_max_height: usize,
) -> Result<F, FriError<M::Error>>
where
    F: BfField,
    M: BFMmcs<F, Proof = BfCommitPhaseProofStep<F>>,
{
    let mut folded_eval = F::zero();

    let mut x = F::two_adic_generator(log_max_height)
        .exp_u64(reverse_bits_len(index, log_max_height) as u64);

    for (log_folded_height, commit, step, &beta) in izip!(
        (0..log_max_height).rev(),
        commit_phase_commits,
        &proof.commit_phase_openings,
        betas,
    ) {
        let index_sibling = index ^ 1;
        let index_pair = index >> 1;

        let open_leaf: PointsLeaf<F> = step.points_leaf.clone();
        let challenge_point: Point<F> = open_leaf.get_point_by_index(index).unwrap().clone();

        let opening = reduced_openings[log_folded_height + 1];
        folded_eval = opening + folded_eval;

        if log_folded_height < log_max_height - 1 {
            assert_eq!(folded_eval, challenge_point.y);
        }
        let sibling_point: Point<F> = open_leaf.get_point_by_index(index_sibling).unwrap().clone();

        assert_eq!(challenge_point.x, x);
        let neg_x = x * F::two_adic_generator(1);
        assert_eq!(sibling_point.x, neg_x);

        let mut evals = vec![folded_eval; 2];
        evals[index_sibling % 2] = sibling_point.y;

        let mut xs = vec![x; 2];
        xs[index_sibling % 2] = neg_x;

        let input = open_leaf.signature();

        if let TapLeaf::Script(script, _ver) = step.leaf_node.leaf().clone() {
            assert_eq!(script, open_leaf.recover_points_euqal_to_commited_point());
            let res = execute_script_with_inputs(
                open_leaf.recover_points_euqal_to_commited_point(),
                input,
            );
            assert_eq!(res.success, true);
        } else {
            panic!("Invalid script")
        }

        config
            .mmcs
            .verify_taptree(step, commit)
            .map_err(FriError::CommitPhaseMmcsError)?;

        folded_eval = evals[0] + (beta - xs[0]) * (evals[1] - evals[0]) / (xs[1] - xs[0]);

        index = index_pair;
        x = x.square();
    }

    debug_assert!(index < config.blowup(), "index was {}", index);
    debug_assert_eq!(x.exp_power_of_2(config.log_blowup), F::one());

    Ok(folded_eval)
}
