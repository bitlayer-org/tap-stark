use alloc::collections::BTreeMap;
use p3_air::{Air, AirBuilder};
use std::{collections::HashSet, marker::PhantomData};
use std::rc::Rc;

use p3_field::Field as P3Field;
use risc0_core::field::{Elem, ExtElem, Field};
use risc0_zkp::adapter::{MixState, PolyExtStep, PolyExtStepDef, Var};

use crate::symbolic_expression::SymbolicExpression;
use crate::{Entry, SymbolicVariable};

/// Convert risc0 PolyExtStep to SymbolicExpression
pub fn convert<F: Field, P3F: P3Field>(
    mix: &F::ExtElem,
    u: &[F::ExtElem],
    args: &[&[F::Elem]],
    var_index_to_polystep: &BTreeMap<usize, PolyExtStep>,
    mix_var_index_to_polystep: &BTreeMap<usize, PolyExtStep>,
    fp_vars: &Vec<F::ExtElem>,
    mix_vars: &Vec<MixState<F::ExtElem>>,
    ret: usize,
) -> R0Recursive<P3F>{
    let mut var_index_to_expr: BTreeMap<usize, SymbolicExpression<P3F>> = BTreeMap::new();
    let mut mix_index_to_constraint_set: BTreeMap<usize, Vec<SymbolicExpression<P3F>>> = BTreeMap::new();
    let mut final_expr = HashSet::new();

    for index in 0..fp_vars.len() {
        final_expr.insert(index);
    }
    for (index, var) in fp_vars.iter().rev().enumerate() {
        let poly_ext_step = var_index_to_polystep.get(&index).unwrap();
        // we need to consider two case: one is this var has been expressed as symbolic_expression, the other is the var has been not expressed as symbolic_expression
        // get symbolic_expression from index_to_expr
        let expr = var_index_to_expr.get(&index);
        if expr.is_some() {
            continue;
        }

        // get symbolic_expression by execute convert_step
        convert_step::<F, P3F>(
            index,
            poly_ext_step,
            args,
            fp_vars,
            var_index_to_polystep,
            &mut var_index_to_expr,
            &mut final_expr,
        );
    }

    for (mix_index, var) in mix_vars.iter().rev().enumerate() {
        let poly_ext_step = mix_var_index_to_polystep.get(&mix_index).unwrap();
        // we need to consider two case: one is this var has been expressed as symbolic_expression, the other is the var has been not expressed as symbolic_expression
        // get symbolic_expression from index_to_expr
        let expr = mix_index_to_constraint_set.get(&mix_index);
        if expr.is_some() {
            continue;
        }

        mix_convert_step::<F, P3F>(mix_index, poly_ext_step, args, &mut var_index_to_expr, mix_var_index_to_polystep, &mut mix_index_to_constraint_set);
    } 
    // todo: finally deal the value for SymbolicVariable
    let cs = mix_index_to_constraint_set.get(&ret).unwrap();
    // cs.clone()

    R0Recursive{
        constraints: cs.clone(),
    }

    // get final symbolic_expression
    // final_expr.iter().map(|index|{
    //     var_index_to_expr.get(index).unwrap().clone()
    // }).collect::<Vec<SymbolicExpression<P3F>>>()



}

fn mix_convert_step<F: Field, P3F: P3Field>(
    mix_index: usize,
    step: &PolyExtStep,
    args: &[&[F::Elem]],
    var_index_to_expr: &mut BTreeMap<usize, SymbolicExpression<P3F>>,
    mix_var_index_to_polystep: &BTreeMap<usize, PolyExtStep>,
    mix_index_to_constraint_set:&mut BTreeMap<usize, Vec<SymbolicExpression<P3F>>>,
) {
    match step {
        PolyExtStep::True => {
            let init_constraint = vec![SymbolicExpression::<P3F>::Constant(P3F::from_canonical_u32(0))];
            assert_eq!(mix_index,0);
            mix_index_to_constraint_set.insert(0,init_constraint);
        }
        PolyExtStep::AndEqz(prev_mix_index, var_index) => {
            let mut constraint_set = mix_index_to_constraint_set.get(prev_mix_index).unwrap().clone();
            let add_constraint = var_index_to_expr.get(var_index).unwrap().clone();
            constraint_set.push(add_constraint);
            mix_index_to_constraint_set.insert(mix_index,constraint_set);
        }
        PolyExtStep::AndCond(prev_mix_index_1, var_index, prev_mix_index_2) => {
            let mut constraint_set_1 = mix_index_to_constraint_set.get(prev_mix_index_1).unwrap().clone();
            let constraint_set_2 = mix_index_to_constraint_set.get(prev_mix_index_2).unwrap().clone();
            let add_constraint = var_index_to_expr.get(var_index).unwrap().clone();
            let mut cs_2: Vec<SymbolicExpression<P3F>> = constraint_set_2.iter().map(|expr| {
                expr.clone() * add_constraint.clone()
            }).collect();
            constraint_set_1.append(&mut cs_2);
            mix_index_to_constraint_set.insert(mix_index,constraint_set_1);
        }
        _ => panic!("Not implemented"),
    }
}

fn convert_step<F: Field, P3F: P3Field>(
    index: usize,
    step: &PolyExtStep,
    args: &[&[F::Elem]],
    fp_vars: &Vec<F::ExtElem>,
    fp_vars_relation: &BTreeMap<usize, PolyExtStep>,
    var_index_to_expr: &mut BTreeMap<usize, SymbolicExpression<P3F>>,
    final_expr: &mut HashSet<usize>,
) -> Option<SymbolicExpression<P3F>> {
    match step {
        PolyExtStep::Const(value) => {
            let symbolic_expression =
                SymbolicExpression::<P3F>::Constant(P3F::from_canonical_u32(*value));
            var_index_to_expr.insert(index, symbolic_expression.clone());
            Some(symbolic_expression)
        }
        // get from eval_u 
        PolyExtStep::Get(tap) => {
            // Notice: risc0-air only use one row to apply the constraints, therefore the offset of the Entry::Main must be 0.
            let symbolic_expression =
                SymbolicExpression::<P3F>::Variable(SymbolicVariable::new(Entry::Main { offset:0 }, *tap));
            var_index_to_expr.insert(index, symbolic_expression.clone());
            Some(symbolic_expression)
        }
        PolyExtStep::GetGlobal(base, offset) => {
            // compute index for Entry::Public
            let mut index = 0;
            for i in 0..*base{
                index += args[i].len();
            }
            let symbolic_expression =
            SymbolicExpression::<P3F>::Variable(SymbolicVariable::new(Entry::Public, index+offset ));
            var_index_to_expr.insert(index, symbolic_expression.clone());
            Some(symbolic_expression)
        }
        PolyExtStep::Add(a, b) => {
            let a_step = fp_vars_relation.get(a).unwrap();
            final_expr.remove(a);
            let a_expr =
                convert_step::<F, P3F>(*a, a_step, args, fp_vars, fp_vars_relation, var_index_to_expr, final_expr).unwrap();
            
            let b_step = fp_vars_relation.get(b).unwrap();
            final_expr.remove(b);
            let b_expr =
                convert_step::<F, P3F>(*b, b_step, args, fp_vars, fp_vars_relation, var_index_to_expr, final_expr).unwrap();
            let degree = a_expr.degree_multiple().max(b_expr.degree_multiple());
            let expr = SymbolicExpression::Add {
                x: Rc::new(a_expr),
                y: Rc::new(b_expr),
                degree_multiple: degree,
            };
            var_index_to_expr.insert(index, expr.clone());
            Some(expr)
        }
        PolyExtStep::Mul(a, b) => {
            let a_step = fp_vars_relation.get(a).unwrap();
            final_expr.remove(a);
            let a_expr =
                convert_step::<F, P3F>(*a, a_step, args, fp_vars, fp_vars_relation, var_index_to_expr, final_expr).unwrap();
            let b_step = fp_vars_relation.get(b).unwrap();
            final_expr.remove(b);
            let b_expr =
                convert_step::<F, P3F>(*b, b_step, args, fp_vars, fp_vars_relation, var_index_to_expr, final_expr).unwrap();
            let degree = a_expr.degree_multiple() + b_expr.degree_multiple();
            let expr = SymbolicExpression::Mul {
                x: Rc::new(a_expr),
                y: Rc::new(b_expr),
                degree_multiple: degree,
            };
            var_index_to_expr.insert(index, expr.clone());
            Some(expr)
        }
        PolyExtStep::Sub(a, b) => {
            let a_step = fp_vars_relation.get(a).unwrap();
            final_expr.remove(a);
            let a_expr =
                convert_step::<F, P3F>(*a, a_step, args, fp_vars, fp_vars_relation, var_index_to_expr, final_expr).unwrap();
            let b_step = fp_vars_relation.get(b).unwrap();
            final_expr.remove(b);
            let b_expr =
                convert_step::<F, P3F>(*b, b_step, args, fp_vars, fp_vars_relation, var_index_to_expr, final_expr).unwrap();
            let degree = a_expr.degree_multiple().max(b_expr.degree_multiple());
            let expr = SymbolicExpression::Sub {
                x: Rc::new(a_expr),
                y: Rc::new(b_expr),
                degree_multiple: degree,
            };
            var_index_to_expr.insert(index, expr.clone());
            Some(expr)
        }
        _ => panic!("Not implemented"),
    }
}

pub struct R0Recursive<F: P3Field>{
    constraints: Vec<SymbolicExpression<F>>,
}


// impl <AB: AirBuilder> Air<AB> for R0Recursive<AB::F>{
//     fn eval(&self, builder: &mut AB) {
//         self.constraints.iter().for_each(|constraint|{
//             builder.assert_zero(x);
//         })
//     }
// }
#[cfg(test)]
mod tests{
    use super::{PolyExtStepDef,PolyExtStep};
    use super::convert;
    use common::BinomialExtensionField;
    use risc0_core::field::baby_bear;
    use p3_baby_bear::BabyBear;
    type EF = BinomialExtensionField<BabyBear,4>;
    #[test]
    fn test_convert(){
        let def = PolyExtStepDef{
            block: &[
                PolyExtStep::Const(1), // var[0]
                PolyExtStep::Const(2), // var[1]
                PolyExtStep::Add(0, 1), // var[2]
                PolyExtStep::Mul(1, 2), // var[3]
                PolyExtStep::Sub(1, 2), // var[4]
                PolyExtStep::Const(1), // var[5]
                PolyExtStep::True, // mix_var[0]
                PolyExtStep::AndEqz(0, 3), // mix_var[1]
                PolyExtStep::AndEqz(0, 4), // mix_var[2]
                PolyExtStep::AndCond(1, 5, 2) // mix_var[3]
            ],
            ret: 3,
        };

        let args = vec![];
        let mix = baby_bear::ExtElem::from_u32(1);
        let u = vec![baby_bear::ExtElem::from_u32(1)];
        let m = def.step_and_record::<baby_bear::BabyBear>(&baby_bear::ExtElem::from_u32(0), &u, &args);
        let result = convert::<baby_bear::BabyBear, EF>(&mix,&u,&args,&m.2,&m.3,&m.0,&m.1,def.ret);
        // assert_eq!(result.len(), 2);
        result.constraints.iter().for_each(|item|{
            println!("{:?}", item);
        });
        

    }
}