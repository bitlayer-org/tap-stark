use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use alloc::vec::Vec;
use alloc::{format, vec};
use core::cell::Cell;
use core::fmt::Debug;
use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use std::cell::RefCell;
use std::ops::Div;
use std::sync::{Mutex, RwLock};

use bitcoin::consensus::serde::hex::Case;
use bitcoin_script_stack::stack::{StackTracker, StackVariable};
use common::AbstractField;
use p3_util::log2_strict_usize;
use primitives::field::BfField;
use scripts::treepp::*;
use scripts::u31_lib::{
    u31_add, u31_mul, u31_neg, u31_sub, u31_sub_u31ext, u31_to_u31ext, u31ext_add, u31ext_add_u31,
    u31ext_equalverify, u31ext_mul, u31ext_mul_u31, u31ext_neg, u31ext_sub, u31ext_sub_u31,
    u32_to_u31, BabyBear4, BabyBearU31,
};

use super::num_script_expr::NumScriptExpression;
use super::variable::{ValueVariable, Variable};
use super::Expression;
use crate::opcode::Opcode;
use crate::script_helper::{index_to_rou, value_exp_n};
use crate::{op_mul, Fraction, OpcodeId, ScriptExprError};

pub(crate) struct CopyVar {
    to_copy_var: Cell<StackVariable>,
    var: Cell<StackVariable>,
    debug: Cell<bool>,
    var_size: u32,
    to_copy: RefCell<Option<Arc<RwLock<Box<dyn Expression>>>>>,
}

impl CopyVar {
    pub(crate) fn new(var_size: u32) -> Self {
        CopyVar {
            to_copy_var: Cell::new(StackVariable::null()),
            var: Cell::new(StackVariable::null()),
            debug: Cell::new(false),
            var_size: var_size,
            to_copy: RefCell::new(None),
        }
    }
}

impl Clone for CopyVar {
    fn clone(&self) -> Self {
        CopyVar {
            to_copy_var: Cell::new(self.to_copy_var.get()),
            var: Cell::new(self.var.get()),
            debug: Cell::new(self.debug.get()),
            var_size: self.var_size,
            to_copy: RefCell::new(None),
        }
    }
}

impl Debug for CopyVar {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("CopyVar")
            .field("to_copy_var", &self.to_copy_var.get())
            .field("var", &self.var.get())
            .field("debug", &self.debug.get())
            .field("var_size", &self.var_size)
            .finish()
    }
}

impl Expression for CopyVar {
    fn to_copy(&self) -> Result<Arc<RwLock<Box<dyn Expression>>>, ScriptExprError> {
        if self.to_copy.borrow().is_some() {
            return Err(ScriptExprError::DoubleCopy);
        }

        let self_copy = CopyVar::new(self.var_size());

        let copy_expr = Arc::new(RwLock::new(Box::new(self_copy) as Box<dyn Expression>));

        *self.to_copy.borrow_mut() = Some(copy_expr.clone());
        Ok(copy_expr)
    }

    fn set_copy_var(&self, var: StackVariable) {
        self.to_copy_var.set(var);
    }

    fn as_expr_ptr(self) -> Arc<RwLock<Box<dyn Expression>>> {
        Arc::new(RwLock::new(Box::new(self)))
    }

    fn set_debug(&self) {
        self.debug.set(true);
    }

    fn express_to_script(
        &self,
        stack: &mut StackTracker,
        _input_variables: &BTreeMap<Variable, StackVariable>,
    ) -> Vec<StackVariable> {
        assert!(self.to_copy_var.get().is_null() == false);
        let var1: StackVariable = stack.move_var(self.to_copy_var.get());
        let to_copy = self.to_copy.borrow();

        if to_copy.is_none() {
            self.var.set(var1);
            return vec![var1];
        }

        let var_top = stack.copy_var(var1); // var_top stay at the top of the stack
        to_copy.as_ref().unwrap().read().unwrap().set_copy_var(var1);
        self.var.set(var_top);
        vec![var_top]
    }

    fn var_size(&self) -> u32 {
        self.var_size
    }
}
