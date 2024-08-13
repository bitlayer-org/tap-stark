extern crate alloc;

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use alloc::vec::Vec;
use std::fmt::Debug;

use bitcoin_script_stack::debugger::StepResult;
use bitcoin_script_stack::stack::{StackTracker, StackVariable};
use primitives::field::BfField;
use script_gen::StandardOpcodeId;
use tracing::{error, info, instrument, trace, warn};
mod script_builder;
mod variable;
pub use variable::{ValueVariable, Variable};
mod script_helper;
pub use script_builder::*;
mod lagrange;
pub use lagrange::*;

pub mod opcode;
pub use opcode::*;
pub mod script_gen;
pub use script_gen::*;
pub mod alias;
pub use alias::*;
pub mod input_manager;
pub use input_manager::*;
pub mod value_manager;
pub use value_manager::*;

mod challenger_expr;
pub use challenger_expr::BfChallengerExpr;

#[derive(Debug, Clone, Copy)]
pub enum ScriptExprError {
    DoubleCopy,
    ReadLockError,
    WriteLockError,
    InvalidExpression,
    InvalidScript,
}
#[derive(Debug, Clone)]
pub struct IdCount {
    count: u32,
    copied: u32,
    stack_var: Option<StackVariable>,
}

impl IdCount {
    fn new(count: u32) -> Self {
        Self {
            count,
            copied: 0,
            stack_var: None,
        }
    }
}

pub(crate) const DYNAMIC_INPUT_OR_OUTPUT: usize = 4294967295;

pub trait Expression: Debug {
    fn as_expr_ptr(self) -> ExprPtr;

    #[instrument]
    fn simulate_express(&self, id_mapper: &mut BTreeMap<u32, IdCount>) {
        let id = self.get_id();
        let count = id_mapper
            .entry(id)
            .and_modify(|count| (*count).count += 1)
            .or_insert(IdCount::new(1))
            .count;
        trace!("insert id:{:?}; count:{:?}", id, count);
        if count > 1 {
            trace!("insert id:{:?} and find the same op_id, just copy", id);
        } else {
            // 1. simulate execution
            self.get_ops().iter().for_each(|op| {
                op.as_ref().read().unwrap().simulate_express(id_mapper);
            });
        }
    }

    #[instrument]
    fn express_to_script(
        &self,
        stack: &mut StackTracker,
        var_getter: &BTreeMap<Variable, StackVariable>,
        id_mapper: &mut BTreeMap<u32, IdCount>,
        optimize: bool,
    ) -> Vec<StackVariable> {
        let id = self.get_id();
        if optimize && self.get_output_number() == 1 {
            let mut id_count = id_mapper.get(&id).unwrap().clone();
            if id_count.count > 1 && id_count.stack_var.is_some() {
                if id_count.copied == id_count.count - 2 {
                    trace!("id:{:?}  copy and drop form stack_var {:?}", id, id_count);
                    let top_var = stack.move_var_from_altstack(id_count.stack_var.unwrap());
                    stack.rename(top_var, "move_var");
                    let id_count = id_mapper.get(&id).unwrap().clone();
                    trace!(
                        "id:{:?}  copy and drop ending {:?} get the new stack_var {:?}",
                        id,
                        id_count,
                        top_var
                    );
                    return vec![top_var];
                } else {
                    trace!("id:{:?}  copy form stack_var {:?}", id, id_count);
                    let top_var = stack.copy_var_from_altstack(id_count.stack_var.unwrap());
                    id_count.copied += 1;
                    id_mapper.insert(id, id_count.clone());
                    let id_count = id_mapper.get(&id).unwrap().clone();
                    trace!(
                        "id:{:?}  copy and drop ending {:?} get the new stack_var {:?}",
                        id,
                        id_count,
                        top_var
                    );
                    return vec![top_var];
                }
            }
        }

        self.check_input_number();

        // 2. express
        let vars_size: Vec<u32> = self
            .get_ops()
            .iter()
            .map(|op| {
                op.as_ref()
                    .read()
                    .unwrap()
                    .express_to_script(stack, var_getter, id_mapper, optimize);
                op.as_ref().read().unwrap().var_size()
            })
            .collect();

        // 3. generate script
        let mut vars = (self.generate_script_fn())(vars_size, stack, var_getter);

        self.check_output_number(vars.len());

        // 4. set copy var to copy
        if optimize && self.get_output_number() == 1 {
            let id_count = id_mapper.get_mut(&id).unwrap();
            if id_count.count > 1 && id_count.stack_var.is_none() && id_count.copied == 0 {
                stack.copy_var(vars[0]);
                let copy_var = stack.to_altstack();
                (*id_count).stack_var = Some(copy_var);
                vars = vec![vars[0]];
            }
        }

        if self.is_debug() == true {
            stack.debug();
        }
        vars
    }

    fn get_input_number(&self) -> usize;
    fn get_output_number(&self) -> usize;

    fn check_input_number(&self) {
        let num = self.get_input_number();
        if num == DYNAMIC_INPUT_OR_OUTPUT {
            // for dynamic input
        } else {
            assert_eq!(self.get_ops().len(), num);
        }
    }

    fn check_output_number(&self, output_num: usize) {
        let num = self.get_output_number();
        if num == DYNAMIC_INPUT_OR_OUTPUT {
            // for dynamic output
        } else {
            assert_eq!(output_num, num);
        }
    }
    fn get_ops(&self) -> &Vec<ExprPtr>;
    fn generate_script_fn(&self) -> Arc<Box<StandardOpScriptGen>>;
    fn var_size(&self) -> u32;
    fn get_id(&self) -> u32;

    #[allow(unused)]
    fn set_debug(&self);

    fn is_debug(&self) -> bool;

    fn opcode(&self) -> StandardOpcodeId;
}

pub fn run_dsl<F: BfField>(expr: Dsl<F>, value: F) -> StepResult {
    let assert_expr = expr.equal_for_f(value);
    let mut stack = StackTracker::new();
    let mut inputs = BTreeMap::new();
    assert_expr.express(&mut stack, &mut inputs);
    stack.run()
}

pub fn assert_dsl<F: BfField>(expr: Dsl<F>, value: F) {
    let res = run_dsl(expr, value);
    assert!(res.success);
}

pub fn debug_assert_dsl<F: BfField>(expr: Dsl<F>, value: F) {
    let res = run_dsl(expr, value);
    debug_assert!(res.success);
}
