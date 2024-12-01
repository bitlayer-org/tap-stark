use alloc::vec;
use alloc::vec::Vec;

use basic::challenger::BfGrindingChallenger;
use basic::field::BfField;
use basic::mmcs::bf_mmcs::BFMmcs;
use basic::tcs::{CommitedProof, DefaultSyncBcManager, B, BM, BO, SG};
use bitcoin::taproot::TapLeaf;
use itertools::izip;
use p3_challenger::{CanObserve, CanSample};
use scripts::execute_script_with_inputs;
use tracing::trace;

use crate::error::FriError;
use crate::{BfQueryProof, FriConfig, FriGenericConfig, FriProof};

#[derive(Debug)]
pub struct FriChallenges<F> {
    pub query_indices: Vec<(usize, usize)>,
    pub(crate) betas: Vec<F>,
}

pub fn verify_shape_and_sample_challenges<G, F, M, Challenger>(
    g: &G,
    config: &FriConfig<M>,
    proof: &FriProof<F, M, Challenger::Witness, G::InputProof>,
    challenger: &mut Challenger,
) -> Result<FriChallenges<F>, FriError<M::Error, G::InputError>>
where
    F: BfField,
    M: BFMmcs<F, Proof = CommitedProof<BO, B>>,
    Challenger: BfGrindingChallenger + CanObserve<M::Commitment> + CanSample<F>,
    G: FriGenericConfig<F>,
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

    let query_indices: Vec<(usize, usize)> = (0..config.num_queries)
        .map(|query_times_index| (query_times_index, challenger.sample_bits(log_max_height)))
        .collect();

    Ok(FriChallenges {
        query_indices,
        betas,
    })
}

pub fn verify_challenges<G, F, M, Witness>(
    g: &G,
    config: &FriConfig<M>,
    proof: &FriProof<F, M, Witness, G::InputProof>,
    challenges: &FriChallenges<F>,
    open_input: impl Fn(usize, usize, &G::InputProof) -> Result<Vec<(usize, F)>, G::InputError>,
) -> Result<(), FriError<M::Error, G::InputError>>
where
    F: BfField,
    M: BFMmcs<F, Proof = CommitedProof<BO, B>>,
    G: FriGenericConfig<F>,
{
    let log_max_height = proof.commit_phase_commits.len() + config.log_blowup;
    for (&(query_times_index, query_index), query_proof) in
        izip!(&challenges.query_indices, &proof.query_proofs,)
    {
        let ro = open_input(query_times_index, query_index, &query_proof.input_proof)
            .map_err(|e| FriError::InputError(e))?;
        let folded_eval = verify_query(
            g,
            config,
            &proof.commit_phase_commits,
            query_index,
            query_times_index,
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

fn verify_query<G, F, M>(
    g: &G,
    config: &FriConfig<M>,
    commit_phase_commits: &[M::Commitment],
    mut query_index: usize,
    query_times_index: usize,
    proof: &BfQueryProof<F, G::InputProof>,
    betas: &[F],
    reduced_openings: Vec<(usize, F)>,
    log_max_height: usize,
) -> Result<F, FriError<M::Error, G::InputError>>
where
    F: BfField,
    M: BFMmcs<F, Proof = CommitedProof<BO, B>>,
    G: FriGenericConfig<F>,
{
    let mut folded_eval = F::zero();
    let mut ro_iter = reduced_openings.into_iter().peekable();

    for (log_folded_height, commit, step, &beta) in izip!(
        (0..log_max_height).rev(),
        commit_phase_commits,
        &proof.commit_phase_openings, //  Vec<(Vec<Vec<F>>,CommitedProof<BO,B>)>,
        betas,
    ) {
        let point_index = query_index & 1;
        let index_sibling = point_index ^ 1;
        let index_pair = query_index >> 1;

        if let Some((_, ro)) = ro_iter.next_if(|(lh, _)| *lh == log_folded_height + 1) {
            trace!("ro:{}", ro);
            folded_eval += ro;
        }

        trace!(
            "ch point index:{}, sib point index:{}, index_pair:{}",
            point_index,
            index_sibling,
            index_pair
        );

        // the opening values len should be 1, becuase we only commit one matrix.
        assert_eq!(step.0.len(), 1);
        let commited_folded_eval = step.0[0][point_index];
        if log_folded_height < log_max_height - 1 {
            assert_eq!(folded_eval, commited_folded_eval);
        }

        config
            .mmcs
            .verify_batch(query_times_index, &step.0, &step.1, commit)
            .map_err(FriError::CommitPhaseMmcsError)?;

        query_index = index_pair;
        folded_eval = g.fold_row(
            query_index,
            log_folded_height,
            beta,
            step.0[0].clone().into_iter(),
        );
    }

    debug_assert!(query_index < config.blowup(), "index was {}", query_index);

    Ok(folded_eval)
}
