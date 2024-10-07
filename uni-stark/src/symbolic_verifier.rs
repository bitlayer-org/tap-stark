use std::iter;

use alloc::vec;
use alloc::vec::Vec;

use itertools::Itertools;
use p3_air::{Air, BaseAir};
use p3_challenger::{CanObserve, CanSample};
use p3_commit::PolynomialSpace;
use p3_field::{AbstractExtensionField, AbstractField, Field};
use p3_matrix::dense::{RowMajorMatrix, RowMajorMatrixView};
use p3_matrix::stack::VerticalPair;
use p3_util::log2_ceil_usize;
use primitives::bf_pcs::Pcs;
use primitives::field::BfField;
use tracing::instrument;

use primitives::air::{AirConstraintBuilder,AirTraceBuilder};
use crate::symbolic_builder::{get_log_quotient_degree, SymbolicAirBuilder};
use crate::{PcsError, Proof, StarkGenericConfig, SymbolicAirTraceBuilder, Val, VerifierConstraintFolder};

#[instrument(skip_all)]
pub fn symbolic_verify<SC>(
    config: &SC,
    air:  SymbolicAirBuilder<SC::Challenge>,
    challenger: &mut SC::Challenger,
    proof: &Proof<SC>,
    public_values: &Vec<Val<SC>>,
) -> Result<(), VerificationError<PcsError<SC>>>
where
    SC: StarkGenericConfig,
    Val<SC>: BfField,
    SC::Challenge: BfField,
{
    let Proof {
        commitments,
        opened_values,
        opening_proof,        degree_bits,
    } = proof;

    let degree = 1 << degree_bits;
    let log_quotient_degree =  log2_ceil_usize( air.get_max_constraint_degree()-1);
    let quotient_degree = 1 << log_quotient_degree;

    let pcs = config.pcs();
    let trace_domain = pcs.natural_domain_for_degree(degree);
    let quotient_domain =
        trace_domain.create_disjoint_domain(1 << (degree_bits + log_quotient_degree));
    let quotient_chunks_domains = quotient_domain.split_domains(quotient_degree);

    // todo: verify the air width
    let air_width = air.main_width();
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

    let width = opened_values.trace_local.len();
    let main = RowMajorMatrix::new(
        iter::empty().chain(opened_values.trace_local.clone()).chain(opened_values.trace_next.clone()).collect_vec(),
        width, 
    );

    let mut air_trace_builder = SymbolicAirTraceBuilder::new(&air);
    air_trace_builder.set_public_trace(public_values.clone());
    air_trace_builder.set_main_trace(main); 
    air_trace_builder.set_selectors(vec![sels.is_first_row,sels.is_last_row,sels.is_transition]); // challenge
    let folded_constraints = air_trace_builder.apply_constraint(alpha);

    // Finally, check that
    //     folded_constraints(zeta) / Z_H(zeta) = quotient(zeta)
    if folded_constraints * sels.inv_zeroifier != quotient {
        return Err(VerificationError::OodEvaluationMismatch);
    }
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
