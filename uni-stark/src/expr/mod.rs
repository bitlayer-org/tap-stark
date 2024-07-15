use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::cell::Cell;

use bitcoin_script_stack::stack::{StackTracker, StackVariable};
use num_script_expr::NumScriptExpression;
use primitives::field::BfField;
use scripts::treepp::*;

use crate::SymbolicExpression::{self, *};

mod script_builder;
pub use script_builder::*;
mod variable;
pub use variable::{ValueVariable, Variable};
mod num_script_expr;
// pub use num_script_expr::*;
mod field_script_expr;
pub use field_script_expr::*;
mod script_helper;

pub struct Executor<F: BfField> {
    to_exec_expr: FieldScriptExpression<F>,
    bmap: BTreeMap<Variable, StackVariable>,
    stack: StackTracker,
}

pub trait Expression {
    fn express_to_script(
        &self,
        stack: &mut StackTracker,
        input_variables: &BTreeMap<Variable, StackVariable>,
    ) -> Script;

    fn var_size(&self) -> u32;

    #[allow(unused)]
    fn set_debug(&self);

    fn get_var(&self) -> Option<Vec<&StackVariable>>;
}
