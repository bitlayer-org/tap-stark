use std::cell::Cell;
use std::collections::BTreeMap;
use std::sync::Arc;

use bitcoin_script_stack::stack::{StackTracker, StackVariable};
use itertools::Itertools;
use p3_field::ExtensionField;
use primitives::field::BfField;
use script_expr::{Expression, FieldScriptExpression};
use scripts::u31_lib::u31_equalverify;

use crate::get_table;

pub fn compute_quotient_expr<Val: BfField, Challenge: BfField + ExtensionField<Val>>(
    zeta: Challenge,
    trace_degree: usize,
    generator: Val,
    quotient_chunk_nums: usize,
    //verify by pcs
    open_values: Vec<Vec<Challenge>>,
    //hint
    denominator_inverse: Vec<Val>,
) -> (
    FieldScriptExpression<Challenge>,
    Vec<FieldScriptExpression<Val>>,
) {
    assert_eq!(open_values.len(), quotient_chunk_nums);
    assert_eq!(denominator_inverse.len(), quotient_chunk_nums);

    let open_values = open_values
        .iter()
        .map(|inner_v| {
            inner_v
                .iter()
                .map(|v| FieldScriptExpression::from(*v))
                .collect_vec()
        })
        .collect_vec();
    let denominator_inverse = denominator_inverse
        .iter()
        .map(|v| FieldScriptExpression::from(*v))
        .collect_vec();

    let zeta = FieldScriptExpression::from(zeta);
    //babybear generator inverse constant
    let inverse_a = FieldScriptExpression::from(Val::from_u32(64944062 as u32));
    let zeta_div_a = inverse_a.mul_ext(zeta);

    let table = FieldScriptExpression::from_table(&get_table(generator, quotient_chunk_nums));

    let mut numerator = vec![];
    for i in 0..quotient_chunk_nums {
        let mut acc_numerator = FieldScriptExpression::from(Challenge::one());
        for j in 0..quotient_chunk_nums {
            if j != i {
                let w_j = table.clone().lookup(
                    (quotient_chunk_nums - 1 - j) as u32,
                    2 * quotient_chunk_nums - 1,
                );
                let zeta_div_a_mul_w = w_j.mul_ext(zeta_div_a.clone());
                let prev_exp_n = zeta_div_a_mul_w.exp_constant(trace_degree as u32);
                let prev_exp_n_minus_one =
                    prev_exp_n.sub_ext(FieldScriptExpression::from(Challenge::one()));
                acc_numerator = acc_numerator.mul_ext(prev_exp_n_minus_one);
            }
        }
        numerator.push(acc_numerator);
    }

    let mut hint_verify = vec![];
    for i in 0..quotient_chunk_nums {
        let mut acc_denominator = FieldScriptExpression::from(Val::one());
        for j in 0..quotient_chunk_nums {
            if j != i {
                let w_j = table.clone().lookup(
                    (i + quotient_chunk_nums - 1 - j) as u32,
                    2 * quotient_chunk_nums - 1,
                );
                let prev_exp_n = w_j.exp_constant(trace_degree as u32);
                let prev_exp_n_minus_one =
                    prev_exp_n.sub_base(FieldScriptExpression::from(Val::one()));
                acc_denominator = acc_denominator.mul_base(prev_exp_n_minus_one);
            }
        }

        //verify hint
        hint_verify.push(
            (acc_denominator * denominator_inverse[i].clone()).equal_verify_for_f(Val::one()),
        );
    }

    let mut quotient_zeta = FieldScriptExpression::from(Challenge::zero());
    for i in 0..quotient_chunk_nums {
        let zps_i = denominator_inverse[i].mul_ext(numerator[i].clone());
        let mut acc = FieldScriptExpression::from(Challenge::zero());
        for j in 0..4 {
            acc = acc
                + (open_values[i][j].clone() * FieldScriptExpression::from(Challenge::monomial(j)));
        }
        quotient_zeta = quotient_zeta + (acc * zps_i);
    }

    (quotient_zeta, hint_verify)
}
