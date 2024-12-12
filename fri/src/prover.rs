use alloc::vec;
use alloc::vec::Vec;
use core::iter;

use basic::challenger::BfGrindingChallenger;
use basic::field::BfField;
use basic::mmcs::bf_mmcs::BFMmcs;
use basic::tcs::{CommitedProof, B, BO};
use itertools::{izip, Itertools};
use p3_challenger::{CanObserve, CanSample};
use p3_field::TwoAdicField;
use p3_matrix::dense::RowMajorMatrix;
use p3_util::log2_strict_usize;
use tracing::{info_span, instrument};

use crate::{BfQueryProof, FriConfig, FriGenericConfig, FriProof};

#[instrument(name = "FRI prover", skip_all)]
pub fn bf_prove<G, F, M, Challenger>(
    g: &G,
    config: &FriConfig<M>,
    inputs: Vec<Vec<F>>,
    challenger: &mut Challenger,
    open_input: impl Fn(usize, usize) -> G::InputProof,
) -> FriProof<F, M, Challenger::Witness, G::InputProof>
where
    F: BfField,
    M: BFMmcs<F, Proof = CommitedProof<BO, B>>,
    Challenger: BfGrindingChallenger + CanObserve<M::Commitment> + CanSample<F>,
    G: FriGenericConfig<F>,
{
    // check sorted descending
    assert!(inputs
        .iter()
        .tuple_windows()
        .all(|(l, r)| l.len() >= r.len()));

    // inputs input
    let log_max_height = log2_strict_usize(inputs[0].len());

    let commit_phase_result = bf_commit_phase(g, config, inputs, challenger);

    let pow_witness = challenger.grind(config.proof_of_work_bits);

    let query_proofs = info_span!("query phase").in_scope(|| {
        iter::repeat_with(|| challenger.sample_bits(log_max_height + g.extra_query_index_bits()))
            .take(config.num_queries)
            .enumerate()
            .map(|(query_times_index, query_index)| BfQueryProof {
                input_proof: open_input(query_times_index, query_index),
                commit_phase_openings: bf_answer_query(
                    config,
                    &commit_phase_result.data,
                    query_index >> g.extra_query_index_bits(),
                    query_times_index,
                ),
            })
            .collect()
    });

    FriProof {
        commit_phase_commits: commit_phase_result.commits,
        query_proofs,
        final_poly: commit_phase_result.final_poly,
        pow_witness,
    }
}

fn bf_answer_query<F, M>(
    config: &FriConfig<M>,
    commit_phase_commits: &[M::ProverData],
    query_index: usize,
    query_times_index: usize,
) -> Vec<(Vec<Vec<F>>, CommitedProof<BO, B>)>
where
    F: BfField,
    M: BFMmcs<F, Proof = CommitedProof<BO, B>>,
{
    let commit_phase_openings = commit_phase_commits
        .iter()
        .enumerate()
        .map(|(i, commit)| {
            let index_i = query_index >> i >> 1;

            config.mmcs.open_batch(query_times_index, index_i, commit)
        })
        .collect();

    commit_phase_openings
}

#[instrument(name = "commit phase", skip_all)]
fn bf_commit_phase<G, F, M, Challenger>(
    g: &G,
    config: &FriConfig<M>,
    inputs: Vec<Vec<F>>,
    challenger: &mut Challenger,
) -> CommitPhaseResult<F, M>
where
    F: TwoAdicField,
    M: BFMmcs<F>,
    Challenger: CanObserve<M::Commitment> + CanSample<F>,
    G: FriGenericConfig<F>,
{
    let mut inputs_iter = inputs.into_iter().peekable();
    let mut folded = inputs_iter.next().unwrap();

    let mut commits = vec![];
    let mut data = vec![];

    while folded.len() > config.blowup() {
        let leaves = RowMajorMatrix::new(folded.clone(), 2);
        let (commit, prover_data) = config.mmcs.commit_matrix(leaves);
        challenger.observe(commit.clone());

        let beta: F = challenger.sample();
        // We passed ownership of `current` to the MMCS, so get a reference to it
        let leaves = config.mmcs.get_matrices(&prover_data).pop().unwrap();
        folded = g.fold_matrix(beta, leaves.as_view());

        commits.push(commit);
        data.push(prover_data);

        if let Some(v) = inputs_iter.next_if(|v| v.len() == folded.len()) {
            izip!(&mut folded, v).for_each(|(c, x)| *c += x);
        }
    }

    // We should be left with `blowup` evaluations of a constant polynomial.
    assert_eq!(folded.len(), config.blowup());
    let final_poly = folded[0];
    for x in folded {
        assert_eq!(x, final_poly);
    }

    CommitPhaseResult {
        commits,
        data,
        final_poly,
    }
}

struct CommitPhaseResult<F: Send + Sync, M: BFMmcs<F>> {
    commits: Vec<M::Commitment>,
    data: Vec<M::ProverData>,
    final_poly: F,
}
