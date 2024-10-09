use std::fmt::Debug;
use std::marker::PhantomData;
use fri::{FriConfig, TwoAdicFriPcs};
use itertools::Itertools;
use p3_air::{Air, AirBuilder, BaseAir};
use p3_baby_bear::{BabyBear, DiffusionMatrixBabyBear};

use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{AbstractField, Field};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
// use p3_merkle_tree::FieldMerkleTreeMmcs;
use p3_symmetric::{
    CompressionFunctionFromHasher, PaddingFreeSponge, SerializingHasher32, TruncatedPermutation,
};
use primitives::challenger::chan_field::U32;
use primitives::challenger::{BfChallenger, Blake3Permutation};
use rand::distributions::{Distribution, Standard};
use rand::{thread_rng, Rng};
use primitives::mmcs::taptree_mmcs::TapTreeMmcs;
use script_expr::BfChallengerExpr;
use uni_stark::{
    gen_symbolic_builder, generate_script_verifier, prove, symbolic_prove, symbolic_verify, verify, StarkConfig, SymbolicAirBuilder
};

/// How many `a * b = c` operations to do per row in the AIR.
const REPETITIONS: usize = 20;
const TRACE_WIDTH: usize = REPETITIONS * 3;

/*
In its basic form, asserts a^(self.degree-1) * b = c
(so that the total constraint degree is self.degree)

If `uses_transition_constraints`, checks that on transition rows, the first a = row number
*/
pub struct MulAir {
    degree: u64,
    uses_boundary_constraints: bool,
    uses_transition_constraints: bool,
}

impl Default for MulAir {
    fn default() -> Self {
        MulAir {
            degree: 3,
            uses_boundary_constraints: true,
            uses_transition_constraints: true,
        }
    }
}

impl MulAir {
    pub fn random_valid_trace<F: Field>(&self, rows: usize, valid: bool) -> RowMajorMatrix<F>
    where
        Standard: Distribution<F>,
    {
        let mut rng = thread_rng();
        let mut trace_values = vec![F::default(); rows * TRACE_WIDTH];
        for (i, (a, b, c)) in trace_values.iter_mut().tuples().enumerate() {
            let row = i / REPETITIONS;

            *a = if self.uses_transition_constraints {
                F::from_canonical_usize(i)
            } else {
                rng.gen()
            };
            *b = if self.uses_boundary_constraints && row == 0 {
                a.square() + F::one()
            } else {
                rng.gen()
            };
            *c = a.exp_u64(self.degree - 1) * *b;

            if !valid {
                // make it invalid
                *c *= F::two();
            }
        }
        RowMajorMatrix::new(trace_values, TRACE_WIDTH)
    }
}

impl<F> BaseAir<F> for MulAir {
    fn width(&self) -> usize {
        TRACE_WIDTH
    }
}

impl<AB: AirBuilder> Air<AB> for MulAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let main_local = main.row_slice(0);
        let main_next = main.row_slice(1);

        for i in 0..REPETITIONS {
            let start = i * 3;
            let a = main_local[start];
            let b = main_local[start + 1];
            let c = main_local[start + 2];
            builder.assert_zero(a.into().exp_u64(self.degree - 1) * b - c);
            if self.uses_boundary_constraints {
                builder
                    .when_first_row()
                    .assert_eq(a * a + AB::Expr::one(), b);
            }
            if self.uses_transition_constraints {
                let next_a = main_next[start];
                builder
                    .when_transition()
                    .assert_eq(a + AB::Expr::from_canonical_usize(REPETITIONS), next_a);
            }
        }
    }
}


fn do_test_bb_twoadic(log_blowup: usize, degree: u64, log_n: usize)  {
  
    type PF = U32;
    const WIDTH: usize = 16;

    type Val = BabyBear;
    type Challenge = BinomialExtensionField<Val, 4>;
    type ValMmcs = TapTreeMmcs<Val>;
    type ChallengeMmcs = TapTreeMmcs<Challenge>;
    type Challenger = BfChallenger<Challenge, PF, Blake3Permutation, WIDTH>;

    type Dft = Radix2DitParallel;
    type MyPcs = TwoAdicFriPcs<Val, Dft, ValMmcs, ChallengeMmcs>;
    type MyConfig = StarkConfig<MyPcs, Challenge, Challenger, BfChallengerExpr<Challenge, U32, 64>>;


    let val_mmcs = ValMmcs::new();
    let challenge_mmcs = ChallengeMmcs::new();
    let dft = Dft {};

    let fri_config = FriConfig {
        log_blowup,
        num_queries: 40,
        proof_of_work_bits: 8,
        mmcs: challenge_mmcs,
    };
    type Pcs = TwoAdicFriPcs<Val, Dft, ValMmcs, ChallengeMmcs>;
    let pcs = Pcs::new(dft, val_mmcs, fri_config);

    let config = MyConfig::new(pcs);

    let air = MulAir {
        degree,
        ..Default::default()
    };

    let permutation = Blake3Permutation {};
    let mut challenger = Challenger::new(permutation).unwrap();

    let trace = air.random_valid_trace(1 << log_n, true);

    let mut p_challenger = challenger.clone();
    let proof = prove(&config, &air, &mut p_challenger, trace, &vec![]);
}

#[test]
fn prove_bb_twoadic_deg2() {
    do_test_bb_twoadic(1, 2, 7)
}

#[test]
fn prove_bb_twoadic_deg3() {
    do_test_bb_twoadic(1, 3, 7)
}

#[test]
fn prove_bb_twoadic_deg4() {
    do_test_bb_twoadic(2, 4, 6)
}

#[test]
fn prove_bb_twoadic_deg5()  {
    do_test_bb_twoadic(2, 5, 6)
}



fn do_test_bb_twoadic_optimize(log_blowup: usize, degree: u64, log_n: usize)  {
  
    type PF = U32;
    const WIDTH: usize = 16;

    type Val = BabyBear;
    type Challenge = BinomialExtensionField<Val, 4>;
    type ValMmcs = TapTreeMmcs<Val>;
    type ChallengeMmcs = TapTreeMmcs<Challenge>;
    type Challenger = BfChallenger<Challenge, PF, Blake3Permutation, WIDTH>;

    type Dft = Radix2DitParallel;
    type MyPcs = TwoAdicFriPcs<Val, Dft, ValMmcs, ChallengeMmcs>;
    type MyConfig = StarkConfig<MyPcs, Challenge, Challenger, BfChallengerExpr<Challenge, U32, 64>>;


    let val_mmcs = ValMmcs::new();
    let challenge_mmcs = ChallengeMmcs::new();
    let dft = Dft {};

    let fri_config = FriConfig {
        log_blowup,
        num_queries: 40,
        proof_of_work_bits: 8,
        mmcs: challenge_mmcs,
    };
    type Pcs = TwoAdicFriPcs<Val, Dft, ValMmcs, ChallengeMmcs>;
    let pcs = Pcs::new(dft, val_mmcs, fri_config);

    let config = MyConfig::new(pcs);

    let air = MulAir {
        degree,
        ..Default::default()
    };

    let permutation = Blake3Permutation {};
    let mut challenger = Challenger::new(permutation).unwrap();

    let trace = air.random_valid_trace(1 << log_n, true);

    let mut p_challenger = challenger.clone();
    let constraint_builder = gen_symbolic_builder(&air,0,0);
    let proof = symbolic_prove(&config, constraint_builder, &mut p_challenger, trace, &vec![]);
}

#[test]
fn prove_bb_twoadic_deg2_optimize() {
    do_test_bb_twoadic_optimize(2, 5, 6)
}
