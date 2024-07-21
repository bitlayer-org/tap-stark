#[cfg(test)]
mod tests {

    use core::cmp::Reverse;
    use std::marker::PhantomData;

    use fri::prover::bf_prove;
    // use super::*;
    use fri::script_verifier::bf_verify_challenges;
    use fri::two_adic_pcs::TwoAdicFriGenericConfig;
    use fri::{verifier, FriConfig};
    use itertools::Itertools;
    use p3_baby_bear::BabyBear;
    use p3_challenger::CanSampleBits;
    use p3_dft::{Radix2Dit, TwoAdicSubgroupDft};
    use p3_field::extension::BinomialExtensionField;
    use p3_field::AbstractField;
    use p3_matrix::dense::RowMajorMatrix;
    use p3_matrix::util::reverse_matrix_index_bits;
    use p3_matrix::Matrix;
    use p3_symmetric::{CryptographicPermutation, Permutation};
    use p3_util::log2_strict_usize;
    use primitives::challenger::chan_field::U32;
    use primitives::challenger::{BfChallenger, Blake3Permutation};
    use primitives::mmcs::taptree_mmcs::TapTreeMmcs;
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;
    use script_expr::{Expression, FieldScriptExpression};
    use script_manager::bc_assignment::{BCAssignment, DefaultBCAssignment};
    use script_manager::script_info::ScriptInfo;

    extern crate alloc;
    use alloc::collections::BTreeMap;

    use bitcoin_script_stack::stack::StackTracker;
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
            |_index, proof| Ok(proof.clone()),
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

        let ldes: Vec<RowMajorMatrix<Val>> = vec![2]
            .iter()
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
            |_index, proof| Ok(proof.clone()),
        )
        .expect("failed verify challenges");

        let fri_exprs = bf_verify_challenges(
            &TwoAdicFriGenericConfig::<Vec<(usize, Val)>, ()>(PhantomData),
            &fri_config,
            &proof,
            &fri_challenges,
            |_index, proof| {
                Ok(proof
                    .iter()
                    .map(|(lh, v)| (*lh, v.clone().into()))
                    .collect())
            },
        )
        .expect("failed verify challenges");
        let mut stack = StackTracker::new();
        let mut input_variables = BTreeMap::new();
        fri_exprs.iter().for_each(|expr| {
            let script = expr.express_to_script(&mut stack, &mut input_variables);
            println!("================== script_len{} ===========", script.len());
            // stack.debug();
            let res = stack.run();
            if !res.success {
                println!("res error: {:?}", res.error);
                println!("res error_msg: {:?}", res.error_msg);
                println!("res error_msg: {:?}", res.last_opcode);
            }
            assert!(res.success);
        });
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
            |_index, proof| Ok(proof.clone()),
        )
        .expect("failed verify challenges");
    }
}

#[cfg(test)]
mod tests2 {

    use core::cmp::Reverse;
    use std::marker::PhantomData;

    use fri::prover::bf_prove;
    use fri::script_verifier::bf_verify_challenges;
    use fri::two_adic_pcs::TwoAdicFriGenericConfig;
    use fri::{verifier, FriConfig};
    use itertools::Itertools;
    use p3_baby_bear::BabyBear;
    use p3_challenger::CanSampleBits;
    use p3_dft::{Radix2Dit, TwoAdicSubgroupDft};
    use p3_field::extension::BinomialExtensionField;
    use p3_field::AbstractField;
    use p3_matrix::dense::RowMajorMatrix;
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
    // use crate::{bf_verify_challenges, verifier};

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
            |_index, proof| Ok(proof.clone()),
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
            |_index, proof| Ok(proof.clone()),
        )
        .expect("failed verify challenges");

        bf_verify_challenges(
            &TwoAdicFriGenericConfig::<Vec<(usize, Val)>, ()>(PhantomData),
            &fri_config,
            &proof,
            &fri_challenges,
            |_index, proof| {
                Ok(proof
                    .iter()
                    .map(|(index, value)| (*index, value.clone().into()))
                    .collect())
            },
        )
        .expect("failed verify challenges");
        assert_eq!(
            p_sample,
            v_challenger.sample_bits(8),
            "prover and verifier transcript have same state after FRI"
        );
    }
}
