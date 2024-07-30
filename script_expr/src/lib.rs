extern crate alloc;

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::cell::Cell;
use std::fmt::Debug;
use std::ops::{Add, Mul, Neg, Sub};
use std::sync::RwLock;

use bitcoin_script_stack::debugger::StepResult;
use bitcoin_script_stack::stack::{StackTracker, StackVariable};
use primitives::field::BfField;
use script_gen::OpcodeId;
use scripts::treepp::*;
mod script_builder;
mod variable;
pub use variable::{ValueVariable, Variable};
mod num_script_expr;
pub use num_script_expr::*;
mod field_script_expr;
pub use field_script_expr::*;
mod script_helper;
pub use script_builder::*;
mod fraction_expr;
pub use fraction_expr::*;
mod lagrange;
pub use lagrange::*;

pub mod opcode;
pub use opcode::*;
pub mod script_gen;
pub use script_gen::*;
pub mod alias;
pub use alias::*;
pub mod std_expr;
pub use std_expr::*;

#[derive(Debug, Clone, Copy)]
pub enum ScriptExprError {
    DoubleCopy,
    ReadLockError,
    WriteLockError,
    InvalidExpression,
    InvalidScript,
}
pub struct Executor<F: BfField> {
    to_exec_expr: FieldScriptExpression<F>,
    bmap: BTreeMap<Variable, StackVariable>,
    stack: StackTracker,
}

pub trait Expression: Debug {
    fn to_copy(&self) -> Result<ExprPtr, ScriptExprError> {
        unimplemented!()
    }

    fn set_copy_var(&self, var: StackVariable) {
        unimplemented!()
    }
    fn as_expr_ptr(self) -> ExprPtr;
    fn express_to_script(
        &self,
        stack: &mut StackTracker,
        input_variables: &BTreeMap<Variable, StackVariable>,
    ) -> Vec<StackVariable>;

    fn var_size(&self) -> u32;

    #[allow(unused)]
    fn set_debug(&self);

    fn opcode(&self) -> OpcodeId;
}

// pub trait Dsl: Expression + Add<ExprPtr> + Sub<ExprPtr> + Mul<ExprPtr> + Neg {

// }

pub fn run_expr<F: BfField>(expr: FieldScriptExpression<F>, value: F) -> StepResult {
    let assert_expr = expr.equal_for_f(value);
    let mut stack = StackTracker::new();
    let mut inputs = BTreeMap::new();
    assert_expr.express_to_script(&mut stack, &mut inputs);
    stack.run()
}

pub fn assert_field_expr<F: BfField>(expr: FieldScriptExpression<F>, value: F) {
    let res = run_expr(expr, value);
    assert!(res.success);
}

pub fn debug_assert_field_expr<F: BfField>(expr: FieldScriptExpression<F>, value: F) {
    let res = run_expr(expr, value);
    debug_assert!(res.success);
}
