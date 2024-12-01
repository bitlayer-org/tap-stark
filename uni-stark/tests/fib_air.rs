use core::num;
use std::borrow::Borrow;

use basic::challenger::chan_field::U32;
// use p3_challenger::DuplexChallenger;
use basic::challenger::{BfChallenger, Blake3Permutation};
use basic::mmcs::taptree_mmcs::TapTreeMmcs;
use basic::tcs::DefaultSyncBcManager;
use fri::{FriConfig, TwoAdicFriPcs};
use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir};
use p3_baby_bear::BabyBear;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{AbstractField, PrimeField64};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use script_expr::BfChallengerExpr;
use uni_stark::{generate_script_verifier, prove, verify, StarkConfig};

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
type MyConfig = StarkConfig<MyPcs, Challenge, Challenger, BfChallengerExpr<Challenge, U32, 64>>;

#[test]
fn test_public_value() {
    let num_queries = 28;
    let val_mmcs = ValMmcs::new(DefaultSyncBcManager::new(), num_queries);
    let challenge_mmcs = ChallengeMmcs::new(DefaultSyncBcManager::new(), num_queries);
    let dft = Dft {};
    let trace = generate_trace_rows::<Val>(0, 1, 1 << 3);
    let fri_config = FriConfig {
        log_blowup: 2,
        num_queries,
        proof_of_work_bits: 8,
        mmcs: challenge_mmcs,
    };
    let pcs = MyPcs::new(dft, val_mmcs, fri_config);
    let config = MyConfig::new(pcs);
    let permutation = Blake3Permutation {};
    let mut challenger = Challenger::new(permutation).unwrap();

    let len = trace.values.len();
    let output = trace.values[len - 1].clone();
    let pis = vec![
        BabyBear::from_canonical_u64(0),
        BabyBear::from_canonical_u64(1),
        output,
    ];

    // assert_eq!(BabyBear::from_canonical_u64(21),trace.clone().values[len-1]);
    let proof = prove(&config, &FibonacciAir {}, &mut challenger, trace, &pis);

    let permutation = Blake3Permutation {};
    let mut challenger = Challenger::new(permutation).unwrap();
    verify(&config, &FibonacciAir {}, &mut challenger, &proof, &pis).expect("verification failed");
}

#[test]
fn test_generate_script_expr() {
    let num_queries = 16;
    let val_mmcs = ValMmcs::new(DefaultSyncBcManager::new(), num_queries);
    let challenge_mmcs = ChallengeMmcs::new(DefaultSyncBcManager::new(), num_queries);
    let dft = Dft {};
    let trace = generate_trace_rows::<Val>(0, 1, 1 << 3);
    let fri_config = FriConfig {
        log_blowup: 2,
        num_queries,
        proof_of_work_bits: 8,
        mmcs: challenge_mmcs,
    };
    let pcs = MyPcs::new(dft, val_mmcs, fri_config);
    let config = MyConfig::new(pcs);
    let permutation = Blake3Permutation {};
    let mut challenger = Challenger::new(permutation).unwrap();

    let len = trace.values.len();
    let output = trace.values[len - 1].clone();
    let mut challenger_dsl = BfChallengerExpr::<Challenge, U32, 64>::new().unwrap();

    let pis = vec![
        BabyBear::from_canonical_u64(0),
        BabyBear::from_canonical_u64(1),
        output,
    ];

    let proof = prove(&config, &FibonacciAir {}, &mut challenger, trace, &pis);

    let permutation = Blake3Permutation {};
    let mut challenger = Challenger::new(permutation).unwrap();
    generate_script_verifier(
        &config,
        &FibonacciAir {},
        &mut challenger,
        &mut challenger_dsl,
        &proof,
        &pis,
    )
    .expect("verification failed");
}

// #[test]
// fn test_quotient_zeta() {
//     let val_mmcs = ValMmcs::new();
//     let challenge_mmcs = ChallengeMmcs::new();
//     let dft = Dft {};
//     let trace = generate_trace_rows::<Val>(0, 1, 1 << 3);
//     let fri_config = FriConfig {
//         log_blowup: 2,
//         num_queries: 28,
//         proof_of_work_bits: 8,
//         mmcs: challenge_mmcs,
//     };
//     let pcs = MyPcs::new(dft, val_mmcs, fri_config);
//     let config = MyConfig::new(pcs);
//     let permutation = Blake3Permutation {};
//     let mut challenger = Challenger::new(permutation).unwrap();

//     let pis = vec![
//         BabyBear::from_canonical_u64(0),
//         BabyBear::from_canonical_u64(1),
//         BabyBear::from_canonical_u64(21),
//     ];
//     let proof = prove(&config, &FibonacciAir {}, &mut challenger, trace, &pis);

//     let Proof {
//         commitments,
//         opened_values,
//         opening_proof,
//         degree_bits,
//     } = proof;

//     let degree = 1 << degree_bits;
//     let log_quotient_degree =
//         get_log_quotient_degree::<Val, FibonacciAir>(&FibonacciAir {}, 0, pis.len());
//     let quotient_degree = 1 << log_quotient_degree;

//     let trace_domain = TwoAdicMultiplicativeCoset {
//         log_n: degree_bits,
//         shift: Val::one(),
//     };
//     let quotient_domain =
//         trace_domain.create_disjoint_domain(1 << (degree_bits + log_quotient_degree));
//     let quotient_chunks_domains = quotient_domain.split_domains(quotient_degree);

//     let mut rng = ChaCha20Rng::seed_from_u64(0u64);

//     let zeta = rng.gen::<Challenge>();

//     let a = Val::generator().try_inverse().unwrap();

//     let generator = Val::two_adic_generator(quotient_domain.log_n);

//     let quotient_chunk_nums = quotient_chunks_domains.len();

//     let zps = quotient_chunks_domains
//         .iter()
//         .enumerate()
//         .map(|(i, domain)| {
//             quotient_chunks_domains
//                 .iter()
//                 .enumerate()
//                 .filter(|(j, _)| *j != i)
//                 .map(|(_, other_domain)| {
//                     other_domain.zp_at_point(zeta)
//                         * other_domain.zp_at_point(domain.first_point()).inverse()
//                 })
//                 .product::<Challenge>()
//         })
//         .collect_vec();

//     let quotient = opened_values
//         .quotient_chunks
//         .iter()
//         .enumerate()
//         .map(|(ch_i, ch)| {
//             ch.iter()
//                 .enumerate()
//                 .map(|(e_i, &c)| {
//                     zps[ch_i]
//                         * <BinomialExtensionField<BabyBear, 4> as AbstractExtensionField<
//                             BabyBear,
//                         >>::monomial(e_i)
//                         * c
//                 })
//                 .sum::<Challenge>()
//         })
//         .sum::<Challenge>();
//     let denomiator_inverse = quotient_chunks_domains
//         .iter()
//         .enumerate()
//         .map(|(i, domain)| {
//             quotient_chunks_domains
//                 .iter()
//                 .enumerate()
//                 .filter(|(j, _)| *j != i)
//                 .map(|(_, other_domain)| {
//                     other_domain
//                         .zp_at_point(domain.first_point())
//                         .inverse()
//                         .into()
//                 })
//                 .product::<Val>()
//         })
//         .collect_vec();

//     let mut manager_assign = ManagerAssign::new();
//     let manager = manager_assign.next_manager();

//     let zeta_dsl = Dsl::from(zeta);
//     compute_quotient_expr::<Val, Challenge>(
//         zeta_dsl,
//         degree,
//         generator,
//         quotient_chunk_nums,
//         opened_values.quotient_chunks,
//         denomiator_inverse,
//         quotient,
//         manager.lock().unwrap(),
//     );

//     {
//         let mut m = manager.lock().unwrap();
//         m.embed_hint_verify::<BabyBear>();
//         m.run(false);
//     }
// }

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
