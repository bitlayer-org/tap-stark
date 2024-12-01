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
use basics::field::BfField;
use scripts::treepp::*;
use scripts::u31_lib::{
    u31_add, u31_mul, u31_neg, u31_sub, u31_sub_u31ext, u31_to_u31ext, u31ext_add, u31ext_add_u31,
    u31ext_equalverify, u31ext_mul, u31ext_mul_u31, u31ext_neg, u31ext_sub, u31ext_sub_u31,
    u32_to_u31, BabyBear4, BabyBearU31,
};

use super::variable::{ValueVariable, Variable};
use super::Expression;
use crate::opcode::Opcode;
use crate::script_gen::StandardOpcodeId;
use crate::script_helper::{index_to_rou, value_exp_n};
use crate::{
    op_mul, CopyVar, CustomOpcode, CustomOpcodeId, Dsl, ExprPtr, IdCount, InputOpcode, ScriptExprError, StandardOpcode, StandardOpcodeId
};

pub enum FieldScriptExpression<F: BfField> {
    Table {
        table: Vec<F>,
        debug: Cell<bool>,
        var: StackVariable,
    },
}

impl<F: BfField> Debug for FieldScriptExpression<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FieldScriptExpression::Table { table, debug, var } => {
                write!(f, "Table: {:?}, Debug: {:?}, Var: {:?}", table, debug, var)
            }
        }
    }
}

impl<F: BfField> Expression for FieldScriptExpression<F> {

    fn opcode(&self) -> StandardOpcodeId {
        match self {
            Self::Table { table, debug, var } => StandardOpcodeId::Table,
        }
    }

    fn as_expr_ptr(self) -> ExprPtr {
        Arc::new(RwLock::new(Box::new(self)))
    }

    fn set_debug(&self) {
        match self {
            FieldScriptExpression::Table { debug, .. } => {
                debug.set(true);
            }
        };
    }

    fn express_to_script(
        &self,
        stack: &mut StackTracker,
        input_variables: &BTreeMap<Variable, StackVariable>,
        id_mapper: &mut BTreeMap<u32,IdCount>,
        optimize: bool,
    ) -> Vec<StackVariable> {
        match self {
     
            FieldScriptExpression::Table {
                table,
                mut var,
                debug,
            } => {
                //push table
                let mut vars = vec![];
                for f in table.iter().rev() {
                    let v = f.as_u32_vec();
                    vars.push(stack.bignumber(v));
                }
                if debug.get() == true {
                    stack.debug();
                }
                vars
            }
        }
    }

    fn var_size(&self) -> u32 {
        F::U32_SIZE as u32
    }
}


impl<F: BfField> FieldScriptExpression<F> {
    pub fn from_table(table: &[F]) -> Self {
        Self::Table {
            table: table.into(),
            debug: Cell::new(false),
            var: StackVariable::null(),
        }
    }
}
