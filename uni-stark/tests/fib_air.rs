use std::borrow::Borrow;

use fri::{FriConfig, TwoAdicFriPcs};
use itertools::Itertools;
use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir};
use p3_baby_bear::{BabyBear, DiffusionMatrixBabyBear};
use p3_commit::{ExtensionMmcs, PolynomialSpace, TwoAdicMultiplicativeCoset};
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{
    AbstractExtensionField, AbstractField, ExtensionField, Field, PrimeField64, TwoAdicField,
};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_merkle_tree::FieldMerkleTreeMmcs;
use p3_poseidon2::{Poseidon2, Poseidon2ExternalMatrixGeneral};
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use primitives::bf_pcs::Pcs;
use primitives::challenger::chan_field::U32;
// use p3_challenger::DuplexChallenger;
use primitives::challenger::{BfChallenger, Blake3Permutation};
use primitives::mmcs::taptree_mmcs::TapTreeMmcs;
use rand::{thread_rng, Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;
use script_manager::bc_assignment::DefaultBCAssignment;
use scripts::execute_script_with_inputs;
use uni_stark::{
    compute_quotient_zeta_script, get_log_quotient_degree, prove, verify, Proof, StarkConfig,
};

/// For testing the public values feature

pub struct FibonacciAir {}

impl<F> BaseAir<F> for FibonacciAir {
    fn width(&self) -> usize {
        NUM_FIBONACCI_COLS
    }
}

impl<AB: AirBuilderWithPublicValues> Air<AB> for FibonacciAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let pis = builder.public_values();

        let a = pis[0];
        let b = pis[1];
        let x = pis[2];

        let (local, next) = (main.row_slice(0), main.row_slice(1));
        let local: &FibonacciRow<AB::Var> = (*local).borrow();
        let next: &FibonacciRow<AB::Var> = (*next).borrow();

        let mut when_first_row = builder.when_first_row();

        when_first_row.assert_eq(local.left, a);
        when_first_row.assert_eq(local.right, b);

        let mut when_transition = builder.when_transition();

        // a' <- b
        when_transition.assert_eq(local.right, next.left);

        // b' <- a + b
        when_transition.assert_eq(local.left + local.right, next.right);

        builder.when_last_row().assert_eq(local.right, x);
    }
}

pub fn generate_trace_rows<F: PrimeField64>(a: u64, b: u64, n: usize) -> RowMajorMatrix<F> {
    assert!(n.is_power_of_two());

    let mut trace =
        RowMajorMatrix::new(vec![F::zero(); n * NUM_FIBONACCI_COLS], NUM_FIBONACCI_COLS);

    let (prefix, rows, suffix) = unsafe { trace.values.align_to_mut::<FibonacciRow<F>>() };
    assert!(prefix.is_empty(), "Alignment should match");
    assert!(suffix.is_empty(), "Alignment should match");
    assert_eq!(rows.len(), n);

    rows[0] = FibonacciRow::new(F::from_canonical_u64(a), F::from_canonical_u64(b));

    for i in 1..n {
        rows[i].left = rows[i - 1].right;
        rows[i].right = rows[i - 1].left + rows[i - 1].right;
    }

    trace
}

const NUM_FIBONACCI_COLS: usize = 2;

pub struct FibonacciRow<F> {
    pub left: F,
    pub right: F,
}

impl<F> FibonacciRow<F> {
    const fn new(left: F, right: F) -> FibonacciRow<F> {
        FibonacciRow { left, right }
    }
}

impl<F> Borrow<FibonacciRow<F>> for [F] {
    fn borrow(&self) -> &FibonacciRow<F> {
        debug_assert_eq!(self.len(), NUM_FIBONACCI_COLS);
        let (prefix, shorts, suffix) = unsafe { self.align_to::<FibonacciRow<F>>() };
        debug_assert!(prefix.is_empty(), "Alignment should match");
        debug_assert!(suffix.is_empty(), "Alignment should match");
        debug_assert_eq!(shorts.len(), 1);
        &shorts[0]
    }
}

type PF = U32;
const WIDTH: usize = 16;

type Val = BabyBear;
type Challenge = BinomialExtensionField<Val, 4>;
type ValMmcs = TapTreeMmcs<Val>;
type ChallengeMmcs = TapTreeMmcs<Challenge>;
type Challenger = BfChallenger<Challenge, PF, Blake3Permutation, WIDTH>;

type Dft = Radix2DitParallel;
type MyPcs = TwoAdicFriPcs<Val, Dft, ValMmcs, ChallengeMmcs>;
type MyConfig = StarkConfig<MyPcs, Challenge, Challenger>;

#[test]
fn test_public_value() {
    let val_mmcs = ValMmcs::new();
    let challenge_mmcs = ChallengeMmcs::new();
    let dft = Dft {};
    let trace = generate_trace_rows::<Val>(0, 1, 1 << 3);
    let fri_config = FriConfig {
        log_blowup: 2,
        num_queries: 28,
        proof_of_work_bits: 8,
        mmcs: challenge_mmcs,
    };
    let pcs = MyPcs::new(dft, val_mmcs, fri_config);
    let config = MyConfig::new(pcs);
    let permutation = Blake3Permutation {};
    let mut challenger = Challenger::new(permutation).unwrap();
    let pis = vec![
        BabyBear::from_canonical_u64(0),
        BabyBear::from_canonical_u64(1),
        BabyBear::from_canonical_u64(21),
    ];
    let proof = prove(&config, &FibonacciAir {}, &mut challenger, trace, &pis);

    let permutation = Blake3Permutation {};
    let mut challenger = Challenger::new(permutation).unwrap();
    let mut script_manager = vec![];
    verify(
        &config,
        &FibonacciAir {},
        &mut challenger,
        &proof,
        &pis,
        &mut script_manager,
    )
    .expect("verification failed");
}

#[test]
fn test_quotient_zeta() {
    let val_mmcs = ValMmcs::new();
    let challenge_mmcs = ChallengeMmcs::new();
    let dft = Dft {};
    let trace = generate_trace_rows::<Val>(0, 1, 1 << 3);
    let fri_config = FriConfig {
        log_blowup: 2,
        num_queries: 28,
        proof_of_work_bits: 8,
        mmcs: challenge_mmcs,
    };
    let pcs = MyPcs::new(dft, val_mmcs, fri_config);
    let config = MyConfig::new(pcs);
    let permutation = Blake3Permutation {};
    let mut challenger = Challenger::new(permutation).unwrap();

    let pis = vec![
        BabyBear::from_canonical_u64(0),
        BabyBear::from_canonical_u64(1),
        BabyBear::from_canonical_u64(21),
    ];
    let proof = prove(&config, &FibonacciAir {}, &mut challenger, trace, &pis);

    let Proof {
        commitments,
        opened_values,
        opening_proof,
        degree_bits,
    } = proof;

    let degree = 1 << degree_bits;
    let log_quotient_degree =
        get_log_quotient_degree::<Val, FibonacciAir>(&FibonacciAir {}, 0, pis.len());
    let quotient_degree = 1 << log_quotient_degree;

    let trace_domain = TwoAdicMultiplicativeCoset {
        log_n: degree_bits,
        shift: Val::one(),
    };
    let quotient_domain =
        trace_domain.create_disjoint_domain(1 << (degree_bits + log_quotient_degree));
    let quotient_chunks_domains = quotient_domain.split_domains(quotient_degree);

    let mut rng = ChaCha20Rng::seed_from_u64(0u64);

    let zeta = rng.gen::<Challenge>();

    let a = Val::generator().try_inverse().unwrap();

    let generator = Val::two_adic_generator(quotient_domain.log_n);

    let quotient_chunk_nums = quotient_chunks_domains.len();

    let zps = quotient_chunks_domains
        .iter()
        .enumerate()
        .map(|(i, domain)| {
            quotient_chunks_domains
                .iter()
                .enumerate()
                .filter(|(j, _)| *j != i)
                .map(|(_, other_domain)| {
                    other_domain.zp_at_point(zeta)
                        * other_domain.zp_at_point(domain.first_point()).inverse()
                })
                .product::<Challenge>()
        })
        .collect_vec();

    let quotient = opened_values
        .quotient_chunks
        .iter()
        .enumerate()
        .map(|(ch_i, ch)| {
            ch.iter()
                .enumerate()
                .map(|(e_i, &c)| {
                    zps[ch_i]
                        * <BinomialExtensionField<BabyBear, 4> as AbstractExtensionField<
                            BabyBear,
                        >>::monomial(e_i)
                        * c
                })
                .sum::<Challenge>()
        })
        .sum::<Challenge>();

    let mut bc_assigner = DefaultBCAssignment::new();
    let mut exec_script_info = compute_quotient_zeta_script::<Val, Challenge>(
        quotient_chunk_nums,
        zps,
        opened_values.quotient_chunks,
        quotient,
    );

    exec_script_info.gen(&mut bc_assigner);

    let res =
        execute_script_with_inputs(exec_script_info.get_eq_script(), exec_script_info.witness());
    assert!(res.success);

    let res = execute_script_with_inputs(
        exec_script_info.get_neq_script(),
        exec_script_info.witness(),
    );
    assert!(!res.success);
}
// #[cfg(debug_assertions)]
// #[test]
// #[should_panic(expected = "assertion `left == right` failed: constraints had nonzero value")]
// fn test_incorrect_public_value() {
//     let perm = Perm::new_from_rng_128(
//         Poseidon2ExternalMatrixGeneral,
//         DiffusionMatrixBabyBear,
//         &mut thread_rng(),
//     );
//     let hash = MyHash::new(perm.clone());
//     let compress = MyCompress::new(perm.clone());
//     let val_mmcs = ValMmcs::new(hash, compress);
//     let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
//     let dft = Dft {};
//     let fri_config = FriConfig {
//         log_blowup: 2,
//         num_queries: 28,
//         proof_of_work_bits: 8,
//         mmcs: challenge_mmcs,
//     };
//     let trace = generate_trace_rows::<Val>(0, 1, 1 << 3);
//     let pcs = Pcs::new(dft, val_mmcs, fri_config);
//     let config = MyConfig::new(pcs);
//     let mut challenger = Challenger::new(perm.clone());
//     let pis = vec![
//         BabyBear::from_canonical_u64(0),
//         BabyBear::from_canonical_u64(1),
//         BabyBear::from_canonical_u64(123_123), // incorrect result
//     ];
//     prove(&config, &FibonacciAir {}, &mut challenger, trace, &pis);
// }
