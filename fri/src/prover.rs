use alloc::vec;
use alloc::vec::Vec;
use core::cmp::Reverse;
use core::iter;

use itertools::{izip, Itertools};
use p3_challenger::{CanObserve, CanSample};
use p3_field::TwoAdicField;
use p3_matrix::dense::RowMajorMatrix;
use p3_util::log2_strict_usize;
use primitives::challenger::BfGrindingChallenger;
use primitives::field::BfField;
use primitives::mmcs::bf_mmcs::BFMmcs;
use primitives::mmcs::taptree_mmcs::{CommitProof, DEFAULT_MATRIX_WIDTH};
use tracing::{info_span, instrument};
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;

use crate::fold_even_odd::fold_even_odd;
use crate::{BfQueryProof, FriConfig, FriGenericConfig, FriProof};

#[instrument(name = "FRI prover", skip_all)]
pub fn bf_prove<G, F, M, Challenger>(
    g: &G,
    config: &FriConfig<M>,
    inputs: Vec<Vec<F>>,
    challenger: &mut Challenger,
    open_input: impl Fn(usize) -> G::InputProof,
) -> FriProof<F, M, Challenger::Witness, G::InputProof>
where
    F: BfField,
    M: BFMmcs<F, Proof = CommitProof<F>>,
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
            .map(|index| BfQueryProof {
                input_proof: open_input(index),
                commit_phase_openings: bf_answer_query(
                    config,
                    &commit_phase_result.data,
                    index >> g.extra_query_index_bits(),
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
    index: usize,
) -> Vec<CommitProof<F>>
where
    F: BfField,
    M: BFMmcs<F, Proof = CommitProof<F>>,
{
    let commit_phase_openings = commit_phase_commits
        .iter()
        .enumerate()
        .map(|(i, commit)| {
            let index_i = index >> i >> 1;

            let proof = config.mmcs.open_taptree(index_i, commit);
            proof
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

#[cfg(test)]
mod tests {

    use std::marker::PhantomData;

    use bitcoin::script;
    use itertools::Itertools;
    use p3_baby_bear::BabyBear;
    use p3_challenger::CanSampleBits;
    use p3_dft::{Radix2Dit, TwoAdicSubgroupDft};
    use p3_field::extension::BinomialExtensionField;
    use p3_field::AbstractField;
    use p3_matrix::util::reverse_matrix_index_bits;
    use p3_matrix::Matrix;
    use p3_symmetric::{CryptographicPermutation, Permutation};
    use p3_util::log2_strict_usize;
    use primitives::challenger::chan_field::U32;
    use primitives::challenger::{BfChallenger, Blake3Permutation};
    use primitives::mmcs::taptree_mmcs::TapTreeMmcs;
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;
    use script_manager::bc_assignment::{BCAssignment, DefaultBCAssignment};
    use script_manager::script_info::ScriptInfo;
    use tracing_subscriber::fmt;

    use super::*;
    use crate::script_verifier::bf_verify_challenges;
    use crate::two_adic_pcs::TwoAdicFriGenericConfig;
    use crate::verifier;

    type PF = U32;
    const WIDTH: usize = 16;
    type SpongeState = [PF; WIDTH];
    type F = BabyBear;
    #[derive(Clone)]
    struct TestPermutation {}

    impl Permutation<SpongeState> for TestPermutation {
        fn permute(&self, mut input: SpongeState) -> SpongeState {
            self.permute_mut(&mut input);
            input
        }

        fn permute_mut(&self, input: &mut SpongeState) {
            input.reverse();
        }
    }

    impl CryptographicPermutation<SpongeState> for TestPermutation {}
    type Val = BabyBear;
    type ValMmcs = TapTreeMmcs<Val>;
    type MyFriConfig = FriConfig<ValMmcs>;

    #[test]
    fn test_compelte_fri_process() {
        let mut script_manager: Vec<ScriptInfo> = Vec::new();
        let permutation = TestPermutation {};
        let mut challenger =
            BfChallenger::<F, PF, TestPermutation, WIDTH>::new(permutation).unwrap();
        let mmcs = ValMmcs::new();
        let fri_config = FriConfig {
            log_blowup: 1,
            num_queries: 10,
            proof_of_work_bits: 8,
            mmcs,
        };

        let dft = Radix2Dit::default();

        let shift = Val::generator();
        let mut rng = ChaCha20Rng::seed_from_u64(0);

        let ldes: Vec<RowMajorMatrix<Val>> = (1..10)
            .map(|deg_bits| {
                let evals = RowMajorMatrix::<Val>::rand_nonzero(&mut rng, 1 << deg_bits, 1);
                let mut lde = dft.coset_lde_batch(evals, 1, shift);
                reverse_matrix_index_bits(&mut lde);
                lde
            })
            .collect();

        let alpha = BabyBear::one();
        let input: [_; 32] = core::array::from_fn(|log_height| {
            let matrices_with_log_height: Vec<&RowMajorMatrix<Val>> = ldes
                .iter()
                .filter(|m| log2_strict_usize(m.height()) == log_height)
                .collect();
            if matrices_with_log_height.is_empty() {
                None
            } else {
                let reduced: Vec<BabyBear> = (0..(1 << log_height))
                    .map(|r| {
                        alpha
                            .powers()
                            .zip(matrices_with_log_height.iter().flat_map(|m| m.row(r)))
                            .map(|(alpha_pow, v)| alpha_pow * v)
                            .sum()
                    })
                    .collect();
                Some(reduced)
            }
        });

        let input: Vec<Vec<Val>> = input.into_iter().rev().flatten().collect();
        let log_max_height = log2_strict_usize(input[0].len());

        let proof = bf_prove(
            &TwoAdicFriGenericConfig::<Vec<(usize, Val)>, ()>(PhantomData),
            &fri_config,
            input.clone(),
            &mut challenger,
            |idx| {
                // As our "input opening proof", just pass through the literal reduced openings.
                let mut ro = vec![];
                for v in &input {
                    let log_height = log2_strict_usize(v.len());
                    ro.push((log_height, v[idx >> (log_max_height - log_height)]));
                }
                ro.sort_by_key(|(lh, _)| Reverse(*lh));
                ro
            },
        );
        let p_sample = challenger.sample_bits(8);

        let v_permutation = TestPermutation {};
        let mut v_challenger =
            BfChallenger::<F, PF, TestPermutation, WIDTH>::new(v_permutation).unwrap();
        let fri_challenges = verifier::verify_shape_and_sample_challenges(
            &TwoAdicFriGenericConfig::<Vec<(usize, Val)>, ()>(PhantomData),
            &fri_config,
            &proof,
            &mut v_challenger,
        )
        .expect("failed verify shape and sample");

        verifier::verify_challenges(
            &TwoAdicFriGenericConfig::<Vec<(usize, Val)>, ()>(PhantomData),
            &fri_config,
            &proof,
            &fri_challenges,
            &mut script_manager,
            |_index, proof,sm| Ok(proof.clone()),
        )
        .expect("failed verify challenges");

        assert_eq!(
            p_sample,
            v_challenger.sample_bits(8),
            "prover and verifier transcript have same state after FRI"
        );
    }

    #[test]
    fn test_script_verifier() {
        let mut script_manager: Vec<ScriptInfo> = Vec::new();
        let permutation = TestPermutation {};
        let mut challenger =
            BfChallenger::<F, PF, TestPermutation, WIDTH>::new(permutation).unwrap();
        let mmcs = ValMmcs::new();
        let fri_config = FriConfig {
            log_blowup: 1,
            num_queries: 10,
            proof_of_work_bits: 8,
            mmcs,
        };

        let mut assign = DefaultBCAssignment::new();

        let dft = Radix2Dit::default();

        let shift = Val::generator();
        let mut rng = ChaCha20Rng::seed_from_u64(0);

        let ldes: Vec<RowMajorMatrix<Val>> = (4..5)
            .map(|deg_bits| {
                let evals = RowMajorMatrix::<Val>::rand_nonzero(&mut rng, 1 << deg_bits, 1);
                let mut lde = dft.coset_lde_batch(evals, 1, shift);
                reverse_matrix_index_bits(&mut lde);
                lde
            })
            .collect();

        let alpha = BabyBear::one();
        let input: [_; 32] = core::array::from_fn(|log_height| {
            let matrices_with_log_height: Vec<&RowMajorMatrix<Val>> = ldes
                .iter()
                .filter(|m| log2_strict_usize(m.height()) == log_height)
                .collect();
            if matrices_with_log_height.is_empty() {
                None
            } else {
                let reduced: Vec<BabyBear> = (0..(1 << log_height))
                    .map(|r| {
                        alpha
                            .powers()
                            .zip(matrices_with_log_height.iter().flat_map(|m| m.row(r)))
                            .map(|(alpha_pow, v)| alpha_pow * v)
                            .sum()
                    })
                    .collect();
                Some(reduced)
            }
        });

        let input: Vec<Vec<Val>> = input.into_iter().rev().flatten().collect();
        let log_max_height = log2_strict_usize(input[0].len());

        let proof = bf_prove(
            &TwoAdicFriGenericConfig::<Vec<(usize, Val)>, ()>(PhantomData),
            &fri_config,
            input.clone(),
            &mut challenger,
            |idx| {
                // As our "input opening proof", just pass through the literal reduced openings.
                let mut ro = vec![];
                for v in &input {
                    let log_height = log2_strict_usize(v.len());
                    ro.push((log_height, v[idx >> (log_max_height - log_height)]));
                }
                ro.sort_by_key(|(lh, _)| Reverse(*lh));
                ro
            },
        );

        let p_sample = challenger.sample_bits(8);

        let v_permutation = TestPermutation {};
        let mut v_challenger =
            BfChallenger::<F, PF, TestPermutation, WIDTH>::new(v_permutation).unwrap();
        let fri_challenges = verifier::verify_shape_and_sample_challenges(
            &TwoAdicFriGenericConfig::<Vec<(usize, Val)>, ()>(PhantomData),
            &fri_config,
            &proof,
            &mut v_challenger,
        )
        .expect("failed verify shape and sample");

        verifier::verify_challenges(
            &TwoAdicFriGenericConfig::<Vec<(usize, Val)>, ()>(PhantomData),
            &fri_config,
            &proof,
            &fri_challenges,
            &mut script_manager,
            |_index, proof,sm| Ok(proof.clone()),
        )
        .expect("failed verify challenges");

        bf_verify_challenges(
            &TwoAdicFriGenericConfig::<Vec<(usize, Val)>, ()>(PhantomData),
            &mut assign,
            &fri_config,
            &proof,
            &fri_challenges,
            &mut script_manager,
            |_index, proof,sm| Ok(proof.clone()),
        )
        .expect("failed verify challenges");
        assert_eq!(
            p_sample,
            v_challenger.sample_bits(8),
            "prover and verifier transcript have same state after FRI"
        );
    }

    #[test]
    fn test_bf_prove_with_blake3_permutation() {
        // tracing_subscriber::registry().with(fmt::layer()).init(); // open some log information

        let mut script_manager: Vec<ScriptInfo> = Vec::new();
        let permutation = Blake3Permutation {};
        let mut challenger: BfChallenger<F, [u8; 4], Blake3Permutation, 16> =
            BfChallenger::<F, PF, Blake3Permutation, WIDTH>::new(permutation).unwrap();
        let mmcs = ValMmcs::new();
        let fri_config = FriConfig {
            log_blowup: 1,
            num_queries: 10,
            proof_of_work_bits: 8,
            mmcs,
        };

        let dft = Radix2Dit::default();

        let shift = Val::generator();
        let mut rng = ChaCha20Rng::seed_from_u64(0);

        let ldes: Vec<RowMajorMatrix<Val>> = (5..6)
            .map(|deg_bits| {
                let evals = RowMajorMatrix::<Val>::rand_nonzero(&mut rng, 1 << deg_bits, 1);
                let mut lde = dft.coset_lde_batch(evals, 1, shift);
                reverse_matrix_index_bits(&mut lde);
                lde
            })
            .collect();

        let alpha = BabyBear::one();
        let input: [_; 32] = core::array::from_fn(|log_height| {
            let matrices_with_log_height: Vec<&RowMajorMatrix<Val>> = ldes
                .iter()
                .filter(|m| log2_strict_usize(m.height()) == log_height)
                .collect();
            if matrices_with_log_height.is_empty() {
                None
            } else {
                let reduced: Vec<BabyBear> = (0..(1 << log_height))
                    .map(|r| {
                        alpha
                            .powers()
                            .zip(matrices_with_log_height.iter().flat_map(|m| m.row(r)))
                            .map(|(alpha_pow, v)| alpha_pow * v)
                            .sum()
                    })
                    .collect();
                Some(reduced)
            }
        });

        let input: Vec<Vec<Val>> = input.into_iter().rev().flatten().collect();
        let log_max_height = log2_strict_usize(input[0].len());

        let proof = bf_prove(
            &TwoAdicFriGenericConfig::<Vec<(usize, Val)>, ()>(PhantomData),
            &fri_config,
            input.clone(),
            &mut challenger,
            |idx| {
                // As our "input opening proof", just pass through the literal reduced openings.
                let mut ro = vec![];
                for v in &input {
                    let log_height = log2_strict_usize(v.len());
                    ro.push((log_height, v[idx >> (log_max_height - log_height)]));
                }
                ro.sort_by_key(|(lh, _)| Reverse(*lh));
                ro
            },
        );

        let permutation = Blake3Permutation {};
        let mut v_challenger: BfChallenger<F, [u8; 4], Blake3Permutation, 16> =
            BfChallenger::<F, PF, Blake3Permutation, WIDTH>::new(permutation).unwrap();
        let fri_challenges = verifier::verify_shape_and_sample_challenges(
            &TwoAdicFriGenericConfig::<Vec<(usize, Val)>, ()>(PhantomData),
            &fri_config,
            &proof,
            &mut v_challenger,
        )
        .expect("failed verify shape and sample");

        verifier::verify_challenges(
            &TwoAdicFriGenericConfig::<Vec<(usize, Val)>, ()>(PhantomData),
            &fri_config,
            &proof,
            &fri_challenges,
            &mut script_manager,
            |_index, proof,sm| Ok(proof.clone()),
        )
        .expect("failed verify challenges");

        // verifier::verify_challenges(&fri_config, &proof, &fri_challenges, &reduced_openings)
        //     .expect("failed verify challenges");
    }
}

#[cfg(test)]
mod tests2 {

    use std::marker::PhantomData;

    use itertools::Itertools;
    use p3_baby_bear::BabyBear;
    use p3_challenger::CanSampleBits;
    use p3_dft::{Radix2Dit, TwoAdicSubgroupDft};
    use p3_field::extension::BinomialExtensionField;
    use p3_field::AbstractField;
    use p3_matrix::util::reverse_matrix_index_bits;
    use p3_matrix::Matrix;
    use p3_symmetric::{CryptographicPermutation, Permutation};
    use p3_util::log2_strict_usize;
    use primitives::challenger::chan_field::U32;
    use primitives::challenger::{BfChallenger, Blake3Permutation};
    use primitives::mmcs::taptree_mmcs::{TapTreeMmcs, ROOT_WIDTH};
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;
    use script_manager::bc_assignment::{BCAssignment, DefaultBCAssignment};
    use script_manager::script_info::ScriptInfo;
    use tracing_subscriber::fmt;

    use super::*;
    use crate::two_adic_pcs::TwoAdicFriGenericConfig;
    use crate::{bf_verify_challenges, verifier};

    type PF = U32;
    const WIDTH: usize = 16;
    type SpongeState = [PF; WIDTH];
    type F = BinomialExtensionField<BabyBear, 4>;
    #[derive(Clone)]
    struct TestPermutation {}

    impl Permutation<SpongeState> for TestPermutation {
        fn permute(&self, mut input: SpongeState) -> SpongeState {
            self.permute_mut(&mut input);
            input
        }

        fn permute_mut(&self, input: &mut SpongeState) {
            input.reverse();
        }
    }

    impl CryptographicPermutation<SpongeState> for TestPermutation {}
    type Val = F;
    type ValMmcs = TapTreeMmcs<Val>;
    type MyFriConfig = FriConfig<ValMmcs>;

    #[test]
    fn test_compelte_fri_process_with_ext_babybear() {
        let mut script_manager :Vec<ScriptInfo> = Vec::new();
        let permutation = TestPermutation {};
        let mut challenger =
            BfChallenger::<F, PF, TestPermutation, WIDTH>::new(permutation).unwrap();
        let mmcs = ValMmcs::new();
        let fri_config = FriConfig {
            log_blowup: 1,
            num_queries: 10,
            proof_of_work_bits: 8,
            mmcs,
        };

        let dft = Radix2Dit::default();

        let shift = Val::generator();
        let mut rng = ChaCha20Rng::seed_from_u64(0);

        let ldes: Vec<RowMajorMatrix<Val>> = (1..10)
            .map(|deg_bits| {
                let evals = RowMajorMatrix::<Val>::rand_nonzero(&mut rng, 1 << deg_bits, 1);
                let mut lde = dft.coset_lde_batch(evals, 1, shift);
                reverse_matrix_index_bits(&mut lde);
                lde
            })
            .collect();

        let alpha = F::one();
        let input: [_; 32] = core::array::from_fn(|log_height| {
            let matrices_with_log_height: Vec<&RowMajorMatrix<Val>> = ldes
                .iter()
                .filter(|m| log2_strict_usize(m.height()) == log_height)
                .collect();
            if matrices_with_log_height.is_empty() {
                None
            } else {
                let reduced: Vec<F> = (0..(1 << log_height))
                    .map(|r| {
                        alpha
                            .powers()
                            .zip(matrices_with_log_height.iter().flat_map(|m| m.row(r)))
                            .map(|(alpha_pow, v)| alpha_pow * v)
                            .sum()
                    })
                    .collect();
                Some(reduced)
            }
        });

        // let (proof, idxs) = bf_prove(&fri_config, &input, &mut challenger);
        let input: Vec<Vec<Val>> = input.into_iter().rev().flatten().collect();
        let log_max_height = log2_strict_usize(input[0].len());

        let proof = bf_prove(
            &TwoAdicFriGenericConfig::<Vec<(usize, Val)>, ()>(PhantomData),
            &fri_config,
            input.clone(),
            &mut challenger,
            |idx| {
                // As our "input opening proof", just pass through the literal reduced openings.
                let mut ro = vec![];
                for v in &input {
                    let log_height = log2_strict_usize(v.len());
                    ro.push((log_height, v[idx >> (log_max_height - log_height)]));
                }
                ro.sort_by_key(|(lh, _)| Reverse(*lh));
                ro
            },
        );
        let p_sample = challenger.sample_bits(8);

        let v_permutation = TestPermutation {};
        let mut v_challenger =
            BfChallenger::<F, PF, TestPermutation, WIDTH>::new(v_permutation).unwrap();
        let fri_challenges = verifier::verify_shape_and_sample_challenges(
            &TwoAdicFriGenericConfig::<Vec<(usize, Val)>, ()>(PhantomData),
            &fri_config,
            &proof,
            &mut v_challenger,
        )
        .expect("failed verify shape and sample");

        verifier::verify_challenges(
            &TwoAdicFriGenericConfig::<Vec<(usize, Val)>, ()>(PhantomData),
            &fri_config,
            &proof,
            &fri_challenges,
            &mut script_manager,
            |_index, proof,sm| Ok(proof.clone()),
        )
        .expect("failed verify challenges");

        assert_eq!(
            p_sample,
            v_challenger.sample_bits(8),
            "prover and verifier transcript have same state after FRI"
        );
    }

    #[test]
    fn test_script_verifier() {
        let mut script_manager :Vec<ScriptInfo> = Vec::new();
        let permutation = TestPermutation {};
        let mut challenger =
            BfChallenger::<F, PF, TestPermutation, WIDTH>::new(permutation).unwrap();
        let mmcs = ValMmcs::new();
        let fri_config = FriConfig {
            log_blowup: 1,
            num_queries: 10,
            proof_of_work_bits: 8,
            mmcs,
        };

        let mut assign = DefaultBCAssignment::new();

        let dft = Radix2Dit::default();

        let shift = Val::generator();
        let mut rng = ChaCha20Rng::seed_from_u64(0);

        let ldes: Vec<RowMajorMatrix<Val>> = (2..3)
            .map(|deg_bits| {
                let evals = RowMajorMatrix::<Val>::rand_nonzero(&mut rng, 1 << deg_bits, 1);
                let mut lde = dft.coset_lde_batch(evals, 1, shift);
                reverse_matrix_index_bits(&mut lde);
                lde
            })
            .collect();

        let alpha = F::one();
        let input: [_; 32] = core::array::from_fn(|log_height| {
            let matrices_with_log_height: Vec<&RowMajorMatrix<Val>> = ldes
                .iter()
                .filter(|m| log2_strict_usize(m.height()) == log_height)
                .collect();
            if matrices_with_log_height.is_empty() {
                None
            } else {
                let reduced: Vec<F> = (0..(1 << log_height))
                    .map(|r| {
                        alpha
                            .powers()
                            .zip(matrices_with_log_height.iter().flat_map(|m| m.row(r)))
                            .map(|(alpha_pow, v)| alpha_pow * v)
                            .sum()
                    })
                    .collect();
                Some(reduced)
            }
        });

        let input: Vec<Vec<Val>> = input.into_iter().rev().flatten().collect();
        let log_max_height = log2_strict_usize(input[0].len());

        let proof = bf_prove(
            &TwoAdicFriGenericConfig::<Vec<(usize, Val)>, ()>(PhantomData),
            &fri_config,
            input.clone(),
            &mut challenger,
            |idx| {
                // As our "input opening proof", just pass through the literal reduced openings.
                let mut ro = vec![];
                for v in &input {
                    let log_height = log2_strict_usize(v.len());
                    ro.push((log_height, v[idx >> (log_max_height - log_height)]));
                }
                ro.sort_by_key(|(lh, _)| Reverse(*lh));
                ro
            },
        );

        let p_sample = challenger.sample_bits(8);

        // let _alpha: Challenge = challenger.sample_ext_element();
        let v_permutation = TestPermutation {};
        let mut v_challenger =
            BfChallenger::<F, PF, TestPermutation, WIDTH>::new(v_permutation).unwrap();
        let fri_challenges = verifier::verify_shape_and_sample_challenges(
            &TwoAdicFriGenericConfig::<Vec<(usize, Val)>, ()>(PhantomData),
            &fri_config,
            &proof,
            &mut v_challenger,
        )
        .expect("failed verify shape and sample");

        verifier::verify_challenges(
            &TwoAdicFriGenericConfig::<Vec<(usize, Val)>, ()>(PhantomData),
            &fri_config,
            &proof,
            &fri_challenges,
            &mut script_manager,
            |_index, proof, sm| Ok(proof.clone()),
        )
        .expect("failed verify challenges");

        bf_verify_challenges(
            &TwoAdicFriGenericConfig::<Vec<(usize, Val)>, ()>(PhantomData),
            &mut assign,
            &fri_config,
            &proof,
            &fri_challenges,
            &mut script_manager,
            |_index, proof,sm| Ok(proof.clone()),
        )
        .expect("failed verify challenges");
        assert_eq!(
            p_sample,
            v_challenger.sample_bits(8),
            "prover and verifier transcript have same state after FRI"
        );
    }
}
