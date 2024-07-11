use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;
use core::cell::Cell;

use bitcoin_script_stack::stack::StackTracker;
use itertools::Itertools;
use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir};
use p3_challenger::{CanObserve, CanSample};
use p3_commit::PolynomialSpace;
use p3_field::{AbstractExtensionField, AbstractField, Field};
use p3_matrix::dense::{RowMajorMatrix, RowMajorMatrixView};
use p3_matrix::stack::VerticalPair;
use primitives::bf_pcs::Pcs;
use script_manager::bc_assignment::DefaultBCAssignment;
use script_manager::script_info::ScriptInfo;
use scripts::execute_script_with_inputs;
use tracing::instrument;

use primitives::field::BfField;
use scripts::u31_lib::{u31ext_equalverify, BabyBear4};

use crate::scripts_expression::{
    get_constrains_log_degree, get_symbolic_builder, ScriptExpression,
};
use crate::symbolic_builder::{self, get_log_quotient_degree, SymbolicAirBuilder};
use crate::{
    Expression, PcsError, Proof, ScriptConstraintBuilder, StarkGenericConfig, Val,
    VerifierConstraintFolder,
};

#[instrument(skip_all)]
pub fn verify<SC, A>(
    config: &SC,
    air: &A,
    challenger: &mut SC::Challenger,
    proof: &Proof<SC>,
    public_values: &Vec<Val<SC>>,
    script_managers: &mut Vec<ScriptInfo>,
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
    // let sym_main = sym_builder.main(); // two row matrix
    // let exp_constraints = sym_builder.constraints();
    // let log_quotient_degree = get_constrains_log_degree(&exp_constraints);
    // let constraints_script: Vec<ScriptExpression<Val<SC>>> = exp_constraints
    //     .iter()
    //     .map(|item| ScriptExpression::from(item))
    //     .collect();
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

    pcs.verify(
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
        script_managers,
    )
    .map_err(VerificationError::InvalidOpeningArgument)?;

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
    //SC::Challenge::monomial(e_i) * c
    //quotient value is EF, but we use EF as base_slice for commit.  width from 1 to 4.

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

    let mut script_folder = ScriptConstraintBuilder::new(
        opened_values.trace_local.clone(),
        opened_values.trace_next.clone(),
        public_values.len(),
        sels.is_first_row,
        sels.is_last_row,
        sels.is_transition,
        alpha,
    );

    air.eval(&mut script_folder);
    let mut stack = StackTracker::new();
    let mut bmap = BTreeMap::new();
    script_folder.set_variable_values(public_values, &mut bmap, &mut stack);

    let acc_expr = script_folder.get_accmulator_expr();
    acc_expr.express_to_script(&mut stack, &bmap);

    stack.bignumber(folder.accumulator.as_u32_vec());
    stack.custom(
        u31ext_equalverify::<BabyBear4>(),
        2,
        false,
        0,
        "u31ext_equalverify",
    );
    stack.debug();
    script_folder.drop_variable_values(&mut bmap, &mut stack);
    stack.op_true();
    let res = stack.run();
    assert!(res.success);
    Ok(())
}

// pub fn verify_script<SC, A>(
//     config: &SC,
//     air: &A,
//     challenger: &mut SC::Challenger,
//     proof: &Proof<SC>,
//     public_values: &Vec<Val<SC>>,
//     script_managers: &mut Vec<ScriptInfo>,
// ) -> Result<(), VerificationError<PcsError<SC>>>
// where
//     SC: StarkGenericConfig,
//     A: Air<SymbolicAirBuilder<Val<SC>>> + for<'a> Air<VerifierConstraintFolder<'a, SC>>,
// {
//     let Proof {
//         commitments,
//         opened_values,
//         opening_proof,
//         degree_bits,
//     } = proof;

//     let degree = 1 << degree_bits;
//     let log_quotient_degree = get_log_quotient_degree::<Val<SC>, A>(air, 0, public_values.len());
//     let quotient_degree = 1 << log_quotient_degree;

//     let pcs = config.pcs();
//     let trace_domain = pcs.natural_domain_for_degree(degree);
//     let quotient_domain =
//         trace_domain.create_disjoint_domain(1 << (degree_bits + log_quotient_degree));
//     let quotient_chunks_domains = quotient_domain.split_domains(quotient_degree);

//     let air_width = <A as BaseAir<Val<SC>>>::width(air);
//     let valid_shape = opened_values.trace_local.len() == air_width
//         && opened_values.trace_next.len() == air_width
//         && opened_values.quotient_chunks.len() == quotient_degree
//         && opened_values
//             .quotient_chunks
//             .iter()
//             .all(|qc| qc.len() == <SC::Challenge as AbstractExtensionField<Val<SC>>>::D);
//     if !valid_shape {
//         return Err(VerificationError::InvalidProofShape);
//     }

//     // Observe the instance.    // TODO: recover observe when we have CanObserve<F> trait
//     // challenger.observe(Val::<SC>::from_canonical_usize(proof.degree_bits));
//     // TODO: Might be best practice to include other instance data here in the transcript, like some
//     // encoding of the AIR. This protects against transcript collisions between distinct instances.
//     // Practically speaking though, the only related known attack is from failing to include public
//     // values. It's not clear if failing to include other instance data could enable a transcript
//     // collision, since most such changes would completely change the set of satisfying witnesses.

//     challenger.observe(commitments.trace.clone());
//     // challenger.observe_slice(public_values);
//     let alpha: SC::Challenge = challenger.sample();
//     challenger.observe(commitments.quotient_chunks.clone());

//     let zeta: SC::Challenge = challenger.sample();
//     let zeta_next = trace_domain.next_point(zeta).unwrap();

//     pcs.verify(
//         vec![
//             (
//                 commitments.trace.clone(),
//                 vec![(
//                     trace_domain,
//                     vec![
//                         (zeta, opened_values.trace_local.clone()),
//                         (zeta_next, opened_values.trace_next.clone()),
//                     ],
//                 )],
//             ),
//             (
//                 commitments.quotient_chunks.clone(),
//                 quotient_chunks_domains
//                     .iter()
//                     .zip(&opened_values.quotient_chunks)
//                     .map(|(domain, values)| (*domain, vec![(zeta, values.clone())]))
//                     .collect_vec(),
//             ),
//         ],
//         opening_proof,
//         challenger,
//         script_managers,
//     )
//     .map_err(VerificationError::InvalidOpeningArgument)?;

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
//                 .product::<SC::Challenge>()
//         })
//         .collect_vec();

//     let quotient = opened_values
//         .quotient_chunks
//         .iter()
//         .enumerate()
//         .map(|(ch_i, ch)| {
//             ch.iter()
//                 .enumerate()
//                 .map(|(e_i, &c)| zps[ch_i] * SC::Challenge::monomial(e_i) * c)
//                 .sum::<SC::Challenge>()
//         })
//         .sum::<SC::Challenge>();

//     let mut bc_assigner = DefaultBCAssignment::new();
//     let mut exec_script_info = compute_quotient_zeta_script::<>(
//         quotient_degree,
//         zps,
//         opened_values.quotient_chunks,
//         quotient
//     );

//     exec_script_info.gen(&mut bc_assigner);

//     let res = execute_script_with_inputs(
//         exec_script_info.get_eq_script(),
//         exec_script_info.witness(),
//     );
//     assert!(res.success);

//     Ok(())
// }

#[derive(Debug)]
pub enum VerificationError<PcsErr> {
    InvalidProofShape,
    /// An error occurred while verifying the claimed openings.
    InvalidOpeningArgument(PcsErr),
    /// Out-of-domain evaluation mismatch, i.e. `constraints(zeta)` did not match
    /// `quotient(zeta) Z_H(zeta)`.
    OodEvaluationMismatch,
}
