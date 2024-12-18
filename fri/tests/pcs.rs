use basic::bf_pcs::{Pcs, PcsExpr};
use basic::challenger::chan_field::U32;
use basic::challenger::{BfChallenger, Blake3Permutation};
use basic::field::BfField;
use basic::mmcs::taptree_mmcs::TapTreeMmcs;
use fri::{FriConfig, TwoAdicFriPcs};
use itertools::{izip, Itertools};
use p3_baby_bear::BabyBear;
use p3_challenger::{CanObserve, CanSample};
use p3_commit::PolynomialSpace;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{ExtensionField, Field};
use p3_matrix::dense::RowMajorMatrix;
use rand::distributions::{Distribution, Standard};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;
use script_expr::{Dsl, ManagerAssign};

extern crate alloc;

fn seeded_rng() -> impl Rng {
    ChaCha20Rng::seed_from_u64(0)
}

fn do_test_fri_pcs<Val, Challenge, Challenger, ChallengerDsl, P>(
    (pcs, challenger, challenger_dsl): &(P, Challenger, ChallengerDsl),
    log_degrees_by_round: &[&[usize]],
) where
    P: PcsExpr<Challenge, Challenger, ChallengerDsl, ManagerAssign>,
    P::Domain: PolynomialSpace<Val = Val>,
    Val: Field + BfField,
    Standard: Distribution<Val>,
    Challenge: BfField + ExtensionField<Val>,
    Challenger: Clone + CanObserve<P::Commitment> + CanSample<Challenge>,
    ChallengerDsl: Clone + CanObserve<P::Commitment> + CanSample<Dsl<Challenge>>,
{
    let num_rounds = log_degrees_by_round.len();
    let mut rng = seeded_rng();

    let mut p_challenger = challenger.clone();
    let mut p_challenger_dsl = challenger_dsl.clone();

    let domains_and_polys_by_round = log_degrees_by_round
        .iter()
        .map(|log_degrees| {
            log_degrees
                .iter()
                .map(|&log_degree| {
                    let d = 1 << log_degree;
                    // random width 5-15
                    let width = 2 + rng.gen_range(0..=2);
                    (
                        pcs.natural_domain_for_degree(d),
                        RowMajorMatrix::<Val>::rand(&mut rng, d, width),
                    )
                })
                .collect_vec()
        })
        .collect_vec();

    let (commits_by_round, data_by_round): (Vec<_>, Vec<_>) = domains_and_polys_by_round
        .iter()
        .map(|domains_and_polys| pcs.commit(domains_and_polys.clone()))
        .unzip();
    assert_eq!(commits_by_round.len(), num_rounds);
    assert_eq!(data_by_round.len(), num_rounds);
    p_challenger.observe_slice(&commits_by_round);
    p_challenger_dsl.observe_slice(&commits_by_round);

    let zeta: Challenge = p_challenger.sample();
    let zeta_dsl: Dsl<Challenge> = p_challenger_dsl.sample();

    let points_by_round = log_degrees_by_round
        .iter()
        .map(|log_degrees| vec![vec![zeta]; log_degrees.len()])
        .collect_vec();
    let data_and_points = data_by_round.iter().zip(points_by_round).collect();
    let (opening_by_round, proof) = pcs.open(data_and_points, &mut p_challenger);
    assert_eq!(opening_by_round.len(), num_rounds);

    // Verify the proof.
    let mut v_challenger = challenger.clone();
    let mut v_challenger_dsl = challenger_dsl.clone();

    v_challenger.observe_slice(&commits_by_round);
    v_challenger_dsl.observe_slice(&commits_by_round);

    let verifier_zeta: Challenge = v_challenger.sample();
    let verifier_zeta_dsl: Dsl<Challenge> = v_challenger_dsl.sample();

    assert_eq!(verifier_zeta, zeta);

    let commits_and_claims_by_round = izip!(
        commits_by_round,
        domains_and_polys_by_round,
        opening_by_round
    )
    .map(|(commit, domains_and_polys, openings)| {
        let claims = domains_and_polys
            .iter()
            .zip(openings)
            .map(|((domain, _), mat_openings)| (*domain, vec![(zeta, mat_openings[0].clone())]))
            .collect_vec();
        (commit, claims)
    })
    .collect_vec();
    assert_eq!(commits_and_claims_by_round.len(), num_rounds);

    let (manager_assign, to_check_dsls) = pcs
        .generate_verify_expr(
            commits_and_claims_by_round,
            &proof,
            &mut v_challenger,
            &mut v_challenger_dsl,
        )
        .unwrap();

    manager_assign
        .managers()
        .iter()
        .enumerate()
        .for_each(|(manager_index, manager)| {
            manager.lock().unwrap().embed_hint_verify::<Val>();
            manager.lock().unwrap().run(false);
            println!(
                "||optimize script_len {}-kb ||",
                manager.lock().unwrap().get_script_len() / 1024
            );
        });
}

// Set it up so we create tests inside a module for each pcs, so we get nice error reports
// specific to a failing PCS.
macro_rules! make_tests_for_pcs {
    ($p:expr) => {
        #[test]
        fn single() {
            let p = $p;
            for i in 3..6 {
                $crate::do_test_fri_pcs(&p, &[&[i]]);
            }
        }

        #[test]
        fn small() {
            let p = $p;
            $crate::do_test_fri_pcs(&p, &[&[2, 1]]);
        }

        #[test]
        fn many_equal() {
            let p = $p;
            for i in 2..3 {
                $crate::do_test_fri_pcs(&p, &[&[i; 5]]);
            }
        }

        #[test]
        fn many_different_rev() {
            let p = $p;
            for i in 1..3 {
                let degrees = (3..3 + i).rev().collect::<Vec<_>>();
                $crate::do_test_fri_pcs(&p, &[&degrees]);
            }
        }

        #[test]
        fn multiple_rounds() {
            let p = $p;
            $crate::do_test_fri_pcs(&p, &[&[3]]);
            $crate::do_test_fri_pcs(&p, &[&[3], &[3]]);
            $crate::do_test_fri_pcs(&p, &[&[3], &[2]]);
            $crate::do_test_fri_pcs(&p, &[&[2], &[3]]);
            // $crate::do_test_fri_pcs(&p, &[&[3, 4], &[3, 4]]);
            $crate::do_test_fri_pcs(&p, &[&[4, 2], &[4, 2]]);
            $crate::do_test_fri_pcs(&p, &[&[2, 2], &[3, 3]]);
            $crate::do_test_fri_pcs(&p, &[&[3, 3], &[2, 2]]);
            $crate::do_test_fri_pcs(&p, &[&[2], &[3, 3]]);
        }
    };
}

mod babybear_fri_pcs {
    use basic::tcs::DefaultSyncBcManager;
    use script_expr::BfChallengerExpr;

    use super::*;

    type PF = U32;
    const WIDTH: usize = 16;

    type Val = BabyBear;
    type Challenge = BinomialExtensionField<Val, 4>;
    type ValMmcs = TapTreeMmcs<Val>;
    type ChallengeMmcs = TapTreeMmcs<Challenge>;
    type Dft = Radix2DitParallel;
    type Challenger = BfChallenger<Challenge, PF, Blake3Permutation, WIDTH>;
    type ChallengerDsl = BfChallengerExpr<Challenge, PF, 64>; // 64 = 4 x width
    type MyPcs = TwoAdicFriPcs<Val, Dft, ValMmcs, ChallengeMmcs>;

    fn get_pcs(log_blowup: usize) -> (MyPcs, Challenger, ChallengerDsl) {
        let num_queries = 2;
        let val_mmcs = ValMmcs::new(DefaultSyncBcManager::new(), num_queries);
        let challenge_mmscs = ChallengeMmcs::new(DefaultSyncBcManager::new(), num_queries);
        let fri_config = FriConfig {
            log_blowup,
            num_queries,
            proof_of_work_bits: 8,
            mmcs: challenge_mmscs,
        };

        let permutation = Blake3Permutation {};
        let challenger = Challenger::new(permutation).unwrap();
        let challenger_dsl = ChallengerDsl::new().unwrap();
        let pcs = MyPcs::new(Dft {}, val_mmcs, fri_config);
        (pcs, challenger, challenger_dsl)
    }

    mod blowup_1 {
        make_tests_for_pcs!(super::get_pcs(1));
    }

    mod blowup_2 {
        make_tests_for_pcs!(super::get_pcs(2));
    }
}
