use alloc::vec;
use alloc::vec::Vec;
use core::iter;

use itertools::{izip, Itertools};
use p3_air::Air;
use p3_challenger::{CanObserve, CanSample};
use p3_commit::PolynomialSpace;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_maybe_rayon::prelude::*;
use p3_util::{log2_ceil_usize, log2_strict_usize};
use primitives::bf_pcs::Pcs;
use tracing::{info_span, instrument};

use primitives::air::{AirConstraintBuilder,AirTraceBuilder};
use crate::symbolic_builder::{get_log_quotient_degree, SymbolicAirBuilder};
use crate::{
    Commitments, Domain, OpenedValues, PackedChallenge, Proof, StarkGenericConfig, SymbolicAirTraceBuilder, Val
};


#[instrument(skip_all)]
#[allow(clippy::multiple_bound_locations)] // cfg not supported in where clauses?
pub fn symbolic_prove<SC>(
    config: &SC,
    air: SymbolicAirBuilder<Val<SC>>,
    challenger: &mut SC::Challenger,
    trace: RowMajorMatrix<Val<SC>>,
    public_values: &Vec<Val<SC>>,
) -> Proof<SC>
where
    SC: StarkGenericConfig,
{

    let degree = trace.height();
    let log_degree = log2_strict_usize(degree);

    let log_quotient_degree =  log2_ceil_usize( air.get_max_constraint_degree()-1);
    let quotient_degree = 1 << log_quotient_degree;

    let pcs = config.pcs();
    let trace_domain = pcs.natural_domain_for_degree(degree);

    let (trace_commit, trace_data) =
        info_span!("commit to trace data").in_scope(|| pcs.commit(vec![(trace_domain, trace)]));

    // Observe the instance.
    // TODO: recover observe when we have CanObserve<F>
    // challenger.observe(Val::<SC>::from_canonical_usize(log_degree));
    // TODO: Might be best practice to include other instance data here; see verifier comment.

    challenger.observe(trace_commit.clone());
    // challenger.observe_slice(public_values);

    let alpha: SC::Challenge = challenger.sample();

    let quotient_domain =
        trace_domain.create_disjoint_domain(1 << (log_degree + log_quotient_degree));

    let trace_on_quotient_domain = pcs.get_evaluations_on_domain(&trace_data, 0, quotient_domain);

    let quotient_values = quotient_values::<SC>(
        air,
        public_values,
        trace_domain,
        quotient_domain,
        trace_on_quotient_domain,
        alpha,
    );
    let quotient_flat = RowMajorMatrix::new_col(quotient_values).flatten_to_base();
    let quotient_chunks = quotient_domain.split_evals(quotient_degree, quotient_flat);
    let qc_domains = quotient_domain.split_domains(quotient_degree);

    let (quotient_commit, quotient_data) = info_span!("commit to quotient poly chunks")
        .in_scope(|| pcs.commit(izip!(qc_domains, quotient_chunks).collect_vec()));
    challenger.observe(quotient_commit.clone());

    let commitments = Commitments {
        trace: trace_commit,
        quotient_chunks: quotient_commit,
    };

    let zeta: SC::Challenge = challenger.sample();
    let zeta_next = trace_domain.next_point(zeta).unwrap();

    let (opened_values, opening_proof) = pcs.open(
        vec![
            (&trace_data, vec![vec![zeta, zeta_next]]),
            (
                &quotient_data,
                // open every chunk at zeta
                (0..quotient_degree).map(|_| vec![zeta]).collect_vec(),
            ),
        ],
        challenger,
    );
    let trace_local = opened_values[0][0][0].clone();
    let trace_next = opened_values[0][0][1].clone();
    let quotient_chunks = opened_values[1].iter().map(|v| v[0].clone()).collect_vec();
    let opened_values = OpenedValues {
        trace_local,
        trace_next,
        quotient_chunks,
    };
    Proof {
        commitments,
        opened_values,
        opening_proof,
        degree_bits: log_degree,
    }
}

#[instrument(name = "compute quotient polynomial", skip_all)]
fn quotient_values<SC>(
    air: SymbolicAirBuilder<Val<SC>>,
    public_values: &Vec<Val<SC>>,
    trace_domain: Domain<SC>,   
    quotient_domain: Domain<SC>,
    trace_on_quotient_domain: impl Matrix<Val<SC>>,
    alpha: SC::Challenge,
) -> Vec<SC::Challenge>
where
    SC: StarkGenericConfig,
{

    let quotient_size = quotient_domain.size();
    let width = trace_on_quotient_domain.width();
    let sels = trace_domain.selectors_on_coset(quotient_domain);

    let qdb = log2_strict_usize(quotient_domain.size()) - log2_strict_usize(trace_domain.size());
    let next_step = 1 << qdb;

    (0..quotient_size)
        .into_par_iter()
        .map(|i_start| {

            let mut air_trace_builder = SymbolicAirTraceBuilder::new(&air);
            air_trace_builder.set_public_trace(public_values.clone());
            let is_first_row = sels.is_first_row[i_start];
            let is_last_row = sels.is_last_row[i_start];
            let is_transition =  sels.is_transition[i_start];
            let inv_zeroifier = sels.inv_zeroifier[i_start];

            air_trace_builder.set_selectors(vec![is_first_row, is_last_row, is_transition]);

            let main = RowMajorMatrix::new(
                iter::empty()
                    .chain(trace_on_quotient_domain.row(i_start))
                    .chain(trace_on_quotient_domain.row(i_start+next_step))
                    .collect_vec(),
                width,
            );

            air_trace_builder.set_main_trace(main);
            let accumulator = air_trace_builder.apply_constraint(alpha);
            let quotient = accumulator * inv_zeroifier;
            quotient
        })
        .collect()
}
