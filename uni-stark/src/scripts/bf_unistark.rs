use std::sync::MutexGuard;

use basic::field::BfField;
use itertools::Itertools;
use p3_field::ExtensionField;
use script_expr::{Dsl, InputManager};

use crate::get_table;

pub fn compute_quotient_expr<Val: BfField, Challenge: BfField + ExtensionField<Val>>(
    zeta_dsl: Dsl<Challenge>,
    trace_degree: usize,
    generator: Val,
    quotient_chunk_nums: usize,
    //verify by pcs
    open_values: Vec<Vec<Challenge>>,
    //hint
    denominator_inverse: Vec<Val>,
    quotient_res: Challenge,
    mut manager: MutexGuard<Box<InputManager>>,
) {
    assert_eq!(open_values.len(), quotient_chunk_nums);
    assert_eq!(denominator_inverse.len(), quotient_chunk_nums);

    let open_values = open_values
        .iter()
        .map(|inner_v| {
            inner_v
                .iter()
                .map(|v| manager.assign_input_f(*v))
                .collect_vec()
        })
        .collect_vec();
    let denominator_inverse = denominator_inverse
        .iter()
        .map(|v| manager.assign_hint_input_f(*v))
        .collect_vec();

    // todo: replace the constant as input
    // let zeta_dsl = manager.assign_input_f(zeta);
    // let zeta_dsl = Dsl::from(zeta);
    //babybear generator inverse constant
    let inverse_a = Dsl::from(Val::from_u32(64944062_u32));
    let zeta_div_a = inverse_a.mul_ext(zeta_dsl);

    let table = Dsl::from_table(&get_table(generator, quotient_chunk_nums));

    let mut numerator = vec![];
    for i in 0..quotient_chunk_nums {
        let mut acc_numerator = Dsl::from(Challenge::one());
        for j in 0..quotient_chunk_nums {
            if j != i {
                let w_j = table.clone().lookup(
                    (quotient_chunk_nums - 1 - j) as u32,
                    2 * quotient_chunk_nums - 1,
                );
                let zeta_div_a_mul_w = w_j.mul_ext(zeta_div_a.clone());
                let prev_exp_n = zeta_div_a_mul_w.exp_constant(trace_degree as u32);
                let prev_exp_n_minus_one = prev_exp_n.sub_ext(Dsl::from(Challenge::one()));
                acc_numerator = acc_numerator.mul_ext(prev_exp_n_minus_one);
            }
        }
        numerator.push(acc_numerator);
    }

    for i in 0..quotient_chunk_nums {
        let mut acc_denominator = Dsl::from(Val::one());
        for j in 0..quotient_chunk_nums {
            if j != i {
                let w_j = table.clone().lookup(
                    (i + quotient_chunk_nums - 1 - j) as u32,
                    2 * quotient_chunk_nums - 1,
                );
                let prev_exp_n = w_j.exp_constant(trace_degree as u32);
                let prev_exp_n_minus_one = prev_exp_n.sub_base(Dsl::from(Val::one()));
                acc_denominator = acc_denominator.mul_base(prev_exp_n_minus_one);
            }
        }

        //verify hint
        manager.add_hint_verify(
            (acc_denominator * denominator_inverse[i].clone())
                .equal_for_f(Val::one())
                .into(),
        );
    }

    let mut quotient_zeta = Dsl::from(Challenge::zero());
    for i in 0..quotient_chunk_nums {
        let zps_i = denominator_inverse[i].clone().mul_ext(numerator[i].clone());
        let mut acc = Dsl::from(Challenge::zero());
        for j in 0..4 {
            acc += open_values[i][j].clone() * Dsl::from(Challenge::monomial(j));
        }
        quotient_zeta += acc * zps_i;
    }

    manager.set_exec_dsl(quotient_zeta.equal_for_f(quotient_res).into());
}
