use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;

use bitcoin_script_stack::stack::StackTracker;
use itertools::Itertools;
use p3_air::{Air, BaseAir};
use p3_challenger::{CanObserve, CanSample};
use p3_commit::PolynomialSpace;
use p3_field::{AbstractExtensionField, AbstractField, Field, TwoAdicField};
use p3_matrix::dense::{RowMajorMatrix, RowMajorMatrixView};
use p3_matrix::stack::VerticalPair;
use p3_util::log2_strict_usize;
use primitives::bf_pcs::{Pcs, PcsExpr};
use primitives::field::BfField;
use script_expr::{
    selectors_at_point_expr, Dsl, InputManager, ManagerAssign, ScriptConstraintBuilder,
    ValueCounter,
};
use serde::de::value;
use tracing::instrument;

use crate::symbolic_builder::{self, get_log_quotient_degree, SymbolicAirBuilder};
use crate::{
    compute_quotient_expr, PcsError, Proof, StarkGenericConfig, Val, VerifierConstraintFolder,
};

#[instrument(skip_all)]
pub fn generate_script_verifier<SC, A>(
    config: &SC,
    air: &A,
    challenger: &mut SC::Challenger,
    proof: &Proof<SC>,
    public_values: &Vec<Val<SC>>,
) -> Result<(), VerificationError<PcsError<SC>>>
where
    SC: StarkGenericConfig,
    A: Air<SymbolicAirBuilder<Val<SC>>>
        + for<'a> Air<VerifierConstraintFolder<'a, SC>>
        + Air<ScriptConstraintBuilder<SC::Challenge>>,
    Val<SC>: BfField,
    SC::Challenge: BfField,
{
    let Proof {
        commitments,
        opened_values,
        opening_proof,
        degree_bits,
    } = proof;

    let degree = 1 << degree_bits;
    let log_quotient_degree = get_log_quotient_degree::<Val<SC>, A>(air, 0, public_values.len());
    let quotient_degree = 1 << log_quotient_degree;

    let pcs = config.pcs();
    let trace_domain = pcs.natural_domain_for_degree(degree);
    let quotient_domain =
        trace_domain.create_disjoint_domain(1 << (degree_bits + log_quotient_degree));
    let quotient_chunks_domains = quotient_domain.split_domains(quotient_degree);

    let air_width = <A as BaseAir<Val<SC>>>::width(air);
    let valid_shape = opened_values.trace_local.len() == air_width
        && opened_values.trace_next.len() == air_width
        && opened_values.quotient_chunks.len() == quotient_degree
        && opened_values
            .quotient_chunks
            .iter()
            .all(|qc| qc.len() == <SC::Challenge as AbstractExtensionField<Val<SC>>>::D);
    if !valid_shape {
        return Err(VerificationError::InvalidProofShape);
    }

    // Observe the instance.    // TODO: recover observe when we have CanObserve<F> trait
    // challenger.observe(Val::<SC>::from_canonical_usize(proof.degree_bits));
    // TODO: Might be best practice to include other instance data here in the transcript, like some
    // encoding of the AIR. This protects against transcript collisions between distinct instances.
    // Practically speaking though, the only related known attack is from failing to include public
    // values. It's not clear if failing to include other instance data could enable a transcript
    // collision, since most such changes would completely change the set of satisfying witnesses.

    challenger.observe(commitments.trace.clone());
    // challenger.observe_slice(public_values);
    let alpha: SC::Challenge = challenger.sample();
    challenger.observe(commitments.quotient_chunks.clone());

    let zeta: SC::Challenge = challenger.sample();
    let zeta_next = trace_domain.next_point(zeta).unwrap();

    let mut manager_assign = pcs
        .generate_verify_expr(
            vec![
                (
                    commitments.trace.clone(),
                    vec![(
                        trace_domain,
                        vec![
                            (zeta, opened_values.trace_local.clone()),
                            (zeta_next, opened_values.trace_next.clone()),
                        ],
                    )],
                ),
                (
                    commitments.quotient_chunks.clone(),
                    quotient_chunks_domains
                        .iter()
                        .zip(&opened_values.quotient_chunks)
                        .map(|(domain, values)| (*domain, vec![(zeta, values.clone())]))
                        .collect_vec(),
                ),
            ],
            opening_proof,
            challenger,
        )
        .map_err(VerificationError::InvalidOpeningArgument)?;

    println!(
        "[Counter Trace u32-Len] local {}-u32 next {}-u32",
        opened_values.trace_local.len() * 4,
        opened_values.trace_next.len() * 4
    );
    opened_values
        .quotient_chunks
        .iter()
        .enumerate()
        .for_each(|(index, chunk)| {
            println!(
                "[Counter quotient_chunk-{} u32-Len] local {}-u32 next {}-u32",
                index,
                chunk.len() * 4,
                chunk.len() * 4
            );
        });

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
                        * other_domain
                            .zp_at_point(domain.first_point())
                            .inverse()
                            .into()
                })
                .product::<SC::Challenge>()
        })
        .collect_vec();

    let quotient = opened_values
        .quotient_chunks
        .iter()
        .enumerate()
        .map(|(ch_i, ch)| {
            ch.iter()
                .enumerate()
                .map(|(e_i, &c)| zps[ch_i] * SC::Challenge::monomial(e_i) * c)
                .sum::<SC::Challenge>()
        })
        .sum::<SC::Challenge>();
    let denomiator_inverse = quotient_chunks_domains
        .iter()
        .enumerate()
        .map(|(i, domain)| {
            quotient_chunks_domains
                .iter()
                .enumerate()
                .filter(|(j, _)| *j != i)
                .map(|(_, other_domain)| {
                    other_domain
                        .zp_at_point(domain.first_point())
                        .inverse()
                        .into()
                })
                .product::<Val<SC>>()
        })
        .collect_vec();
    let generator = Val::<SC>::two_adic_generator(degree_bits + log_quotient_degree);

    let quotient_chunk_nums = quotient_chunks_domains.len();

    let manager_for_quotient =
        manager_assign.next_manager_with_name("[compute quotient]".to_string());
    {
        let manager = manager_for_quotient.lock().unwrap();
        compute_quotient_expr::<Val<SC>, SC::Challenge>(
            zeta,
            degree,
            generator,
            quotient_chunk_nums,
            opened_values.quotient_chunks.clone(),
            denomiator_inverse,
            quotient,
            manager,
        );
    }

    let total_script_len =
        manager_assign
            .managers()
            .iter()
            .enumerate()
            .fold(0, |acc, (manager_index, manager)| {
                manager.lock().unwrap().embed_hint_verify::<Val<SC>>();
                manager.lock().unwrap().run(false);
                acc + manager.lock().unwrap().print_script_len()
            });
    println!("total script: {:?}-kb", total_script_len);
    let mut value_count = ValueCounter::new();
    manager_assign.set_value_count(&mut value_count);
    println!("u32_count: {}", value_count.get_value_num());

    let sels = trace_domain.selectors_at_point(zeta);

    let main = VerticalPair::new(
        RowMajorMatrixView::new_row(&opened_values.trace_local),
        RowMajorMatrixView::new_row(&opened_values.trace_next),
    );

    let mut folder = VerifierConstraintFolder {
        main,
        public_values,
        is_first_row: sels.is_first_row,
        is_last_row: sels.is_last_row,
        is_transition: sels.is_transition,
        alpha,
        accumulator: SC::Challenge::zero(),
    };
    air.eval(&mut folder);
    let folded_constraints = folder.accumulator;

    // Finally, check that
    //     folded_constraints(zeta) / Z_H(zeta) = quotient(zeta)
    if folded_constraints * sels.inv_zeroifier != quotient {
        return Err(VerificationError::OodEvaluationMismatch);
    }

    let log_n = log2_strict_usize(degree);
    let sels_expr = selectors_at_point_expr(Val::<SC>::one(), zeta, log_n);
    let mut script_folder = ScriptConstraintBuilder::new_with_expr(
        opened_values.trace_local.clone(),
        opened_values.trace_next.clone(),
        public_values.len(),
        sels_expr.is_first_row,
        sels_expr.is_last_row,
        sels_expr.is_transition,
        alpha.into(),
    );

    air.eval(&mut script_folder);
    let mut stack = StackTracker::new();
    let mut var_getter = BTreeMap::new();
    let mut optimize = BTreeMap::new();
    script_folder.set_variable_values(public_values, &mut var_getter, &mut stack);

    let acc_expr = script_folder.get_accmulator_expr();
    let equal_expr = acc_expr.equal_verify_for_f(folder.accumulator);
    equal_expr.simulate_express(&mut optimize);
    equal_expr.express_to_script(&mut stack, &mut var_getter, &mut optimize, true);
    script_folder.drop_variable_values(&mut var_getter, &mut stack);
    stack.op_true();
    let res = stack.run();
    assert!(res.success);
    println!(
        "[compute trace open] optimize script: {:?}-kb",
        stack.get_script().len() / 1024
    );

    script_folder.set_value_count(&mut value_count);
    println!("value_count: {}", value_count.get_value_num());
    Ok(())
}

#[derive(Debug)]
pub enum VerificationError<PcsErr> {
    InvalidProofShape,
    /// An error occurred while verifying the claimed openings.
    InvalidOpeningArgument(PcsErr),
    /// Out-of-domain evaluation mismatch, i.e. `constraints(zeta)` did not match
    /// `quotient(zeta) Z_H(zeta)`.
    OodEvaluationMismatch,
}
