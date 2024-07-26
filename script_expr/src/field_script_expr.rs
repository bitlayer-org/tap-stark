use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use alloc::vec::Vec;
use alloc::{format, vec};
use bitcoin::opcodes::OP_TOALTSTACK;
use scripts::blake3::blake3_var_length;
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
use crate::script_helper::{index_to_rou, value_exp_n, value_exp_7};
use crate::{
    op_mul, CopyVar, CustomOpcode, CustomOpcodeId, ExprPtr, Fraction, ScriptExprError,
    StandardOpcode, StandardOpcodeId,
};

pub enum FieldScriptExpression<F: BfField> {
    ValueVariable {
        v: ValueVariable<F>,
        debug: Cell<bool>,
        var: StackVariable,
    },
    InputVariable {
        sv: Variable,
        debug: Cell<bool>,
        var: StackVariable,
    },
    Constant(CustomOpcode<0, 1, F>),
    Table {
        table: Vec<F>,
        debug: Cell<bool>,
        var: StackVariable,
    },
    Add(StandardOpcode<2, 1>),
    Sub(StandardOpcode<2, 1>),
    Neg(StandardOpcode<1, 1>),
    Mul(StandardOpcode<2, 1>),
    EqualVerify(StandardOpcode<2, 0>),
    Equal(StandardOpcode<2, 1>),
    ExpConstant(CustomOpcode<1, 1, F>),
    IndexToROU(CustomOpcode<1, 1, F>),
    NumToField {
        x: Arc<Box<dyn Expression>>,
        var: StackVariable,
        debug: Cell<bool>,
    },
    Lookup {
        x: Arc<Box<dyn Expression>>,
        y: Arc<Box<dyn Expression>>,
        len: usize,
        var: StackVariable,
        debug: Cell<bool>,
    },
    Blake3Perm {
        x: Arc<Box<dyn Expression>>,
        num_bytes: usize,
        var: StackVariable,
        debug: Cell<bool>,
    },
    Exp7 {
        x: Arc<Box<dyn Expression>>,
        var: StackVariable,
        debug: Cell<bool>,
    },
    Add16 {
        x: Vec<Arc<Box<dyn Expression>>>,
        var: StackVariable,
        debug: Cell<bool>,
    } 
}

impl<F: BfField> FieldScriptExpression<F> {
    pub(crate) fn new_mul_from_expr_ptr(x: ExprPtr, y: ExprPtr) -> Self {
        let var_size = x
            .read()
            .unwrap()
            .var_size()
            .max(y.read().unwrap().var_size());
        Self::Mul(StandardOpcode::new(
            vec![x, y],
            var_size,
            StandardOpcodeId::Mul,
        ))
    }

    pub(crate) fn new_mul(x: Self, y: Self) -> Self {
        let var_size = x.var_size().max(y.var_size());
        Self::Mul(StandardOpcode::new(
            vec![x.as_expr_ptr(), y.as_expr_ptr()],
            var_size,
            StandardOpcodeId::Mul,
        ))
    }

    pub(crate) fn new_add(x: Self, y: Self) -> Self {
        let var_size = x.var_size().max(y.var_size());
        Self::Add(StandardOpcode::new(
            vec![x.as_expr_ptr(), y.as_expr_ptr()],
            var_size,
            StandardOpcodeId::Add,
        ))
    }

    pub(crate) fn new_sub(x: Self, y: Self) -> Self {
        let var_size = x.var_size().max(y.var_size());
        Self::Sub(StandardOpcode::new(
            vec![x.as_expr_ptr(), y.as_expr_ptr()],
            var_size,
            StandardOpcodeId::Sub,
        ))
    }

    pub(crate) fn new_neg(x: Self) -> Self {
        let var_size = x.var_size();
        Self::Neg(StandardOpcode::new(
            vec![x.as_expr_ptr()],
            var_size,
            StandardOpcodeId::Neg,
        ))
    }

    pub(crate) fn new_expconst(x: ExprPtr, power: u32) -> Self {
        let var_size = x.read().unwrap().var_size();
        Self::ExpConstant(CustomOpcode::new(
            vec![power],
            vec![x],
            var_size,
            CustomOpcodeId::ExpConst,
        ))
    }

    pub(crate) fn new_indextorou(x: ExprPtr, sub_group_bits: u32) -> Self {
        let var_size = x.read().unwrap().var_size();
        Self::IndexToROU(CustomOpcode::new(
            vec![sub_group_bits],
            vec![x],
            var_size,
            CustomOpcodeId::IndexToRou,
        ))
    }

    pub(crate) fn new_constant(value: F) -> Self {
        Self::Constant(CustomOpcode::new(
            value.as_u32_vec(),
            vec![],
            F::U32_SIZE as u32,
            CustomOpcodeId::Constant,
        ))
    }

    pub fn add_ext<EF: BfField>(self, rhs: FieldScriptExpression<EF>) -> FieldScriptExpression<EF> {
        assert_eq!(F::U32_SIZE, 1);
        assert_eq!(EF::U32_SIZE, 4);
        FieldScriptExpression::<EF>::Add(StandardOpcode::new(
            vec![self.as_expr_ptr(), rhs.as_expr_ptr()],
            EF::U32_SIZE as u32,
            StandardOpcodeId::Add,
        ))
    }

    pub fn add_base<Base: BfField>(self, rhs: FieldScriptExpression<Base>) -> Self {
        assert_eq!(F::U32_SIZE, 4);
        assert_eq!(Base::U32_SIZE, 1);
        Self::Add(StandardOpcode::new(
            vec![self.as_expr_ptr(), rhs.as_expr_ptr()],
            F::U32_SIZE as u32,
            StandardOpcodeId::Add,
        ))
    }

    pub fn mul_ext<EF: BfField>(self, rhs: FieldScriptExpression<EF>) -> FieldScriptExpression<EF> {
        assert_eq!(F::U32_SIZE, 1);
        assert_eq!(EF::U32_SIZE, 4);
        FieldScriptExpression::<EF>::Mul(StandardOpcode::new(
            vec![self.as_expr_ptr(), rhs.as_expr_ptr()],
            EF::U32_SIZE as u32,
            StandardOpcodeId::Mul,
        ))
    }

    pub fn mul_base<Base: BfField>(self, rhs: FieldScriptExpression<Base>) -> Self {
        assert_eq!(F::U32_SIZE, 4);
        assert_eq!(Base::U32_SIZE, 1);
        Self::Mul(StandardOpcode::new(
            vec![self.as_expr_ptr(), rhs.as_expr_ptr()],
            F::U32_SIZE as u32,
            StandardOpcodeId::Mul,
        ))
    }

    pub fn sub_ext<EF: BfField>(self, rhs: FieldScriptExpression<EF>) -> FieldScriptExpression<EF> {
        assert_eq!(F::U32_SIZE, 1);
        assert_eq!(EF::U32_SIZE, 4);
        FieldScriptExpression::<EF>::Sub(StandardOpcode::new(
            vec![self.as_expr_ptr(), rhs.as_expr_ptr()],
            EF::U32_SIZE as u32,
            StandardOpcodeId::Sub,
        ))
    }

    pub fn sub_base<Base: BfField>(self, rhs: FieldScriptExpression<Base>) -> Self {
        assert_eq!(F::U32_SIZE, 4);
        assert_eq!(Base::U32_SIZE, 1);
        Self::Sub(StandardOpcode::new(
            vec![self.as_expr_ptr(), rhs.as_expr_ptr()],
            F::U32_SIZE as u32,
            StandardOpcodeId::Sub,
        ))
    }

    pub fn exp_constant(self, power: u32) -> Self {
        Self::new_expconst(self.as_expr_ptr(), power)
    }

    pub fn equal(self, rhs: Self) -> Self {
        FieldScriptExpression::Equal(StandardOpcode::new(
            vec![self.as_expr_ptr(), rhs.as_expr_ptr()],
            F::U32_SIZE as u32,
            StandardOpcodeId::Equal,
        ))
    }

    pub fn equal_for_f(self, rhs: F) -> Self {
        FieldScriptExpression::Equal(StandardOpcode::new(
            vec![self.as_expr_ptr(), Self::from(rhs).as_expr_ptr()],
            F::U32_SIZE as u32,
            StandardOpcodeId::Equal,
        ))
    }

    pub fn equal_verify(self, rhs: Self) -> Self {
        FieldScriptExpression::EqualVerify(StandardOpcode::new(
            vec![self.as_expr_ptr(), Self::from(rhs).as_expr_ptr()],
            F::U32_SIZE as u32,
            StandardOpcodeId::EqualVerify,
        ))
    }

    pub fn equal_verify_for_f(self, rhs: F) -> Self {
        FieldScriptExpression::EqualVerify(StandardOpcode::new(
            vec![self.as_expr_ptr(), Self::from(rhs).as_expr_ptr()],
            F::U32_SIZE as u32,
            StandardOpcodeId::EqualVerify,
        ))
    }

    pub fn index_to_rou(index: u32, sub_group_bits: u32) -> Self {
        Self::new_indextorou(
            NumScriptExpression::from(index).as_expr_ptr(),
            sub_group_bits,
        )
    }

    pub fn num_index_to_rou(index: NumScriptExpression, sub_group_bits: u32) -> Self {
        Self::new_indextorou(index.as_expr_ptr(), sub_group_bits)
    }

    pub fn debug(self) -> Self {
        self.set_debug();
        self
    }
}

impl<F: BfField> Expression for FieldScriptExpression<F> {
    fn to_copy(&self) -> Result<ExprPtr, ScriptExprError> {
        match self {
            FieldScriptExpression::Add(op) => op.to_copy(),
            FieldScriptExpression::Mul(op) => op.to_copy(),
            FieldScriptExpression::Sub(op) => op.to_copy(),
            FieldScriptExpression::Neg(op) => op.to_copy(),
            FieldScriptExpression::Constant(op) => op.to_copy(),
            FieldScriptExpression::ExpConstant(op) => op.to_copy(),
            FieldScriptExpression::IndexToROU(op) => op.to_copy(),
            FieldScriptExpression::Equal(op) => op.to_copy(),
            _ => panic!("no support to_copy()"),
        }
    }

    fn as_expr_ptr(self) -> ExprPtr {
        Arc::new(RwLock::new(Box::new(self)))
    }

    fn set_debug(&self) {
        match self {
            FieldScriptExpression::ValueVariable { debug, .. } => {
                debug.set(true);
            }
            FieldScriptExpression::InputVariable { debug, .. } => {
                debug.set(true);
            }
            FieldScriptExpression::Constant(op) => op.set_debug(),
            FieldScriptExpression::Table { debug, .. } => {
                debug.set(true);
            }
            FieldScriptExpression::Add(op) => op.set_debug(),
            FieldScriptExpression::Sub(op) => op.set_debug(),
            FieldScriptExpression::Neg(op) => op.set_debug(),
            FieldScriptExpression::Mul(op) => op.set_debug(),
            FieldScriptExpression::EqualVerify(op) => op.set_debug(),
            FieldScriptExpression::Equal(op) => op.set_debug(),
            FieldScriptExpression::ExpConstant(op) => op.set_debug(),
            FieldScriptExpression::IndexToROU(op) => op.set_debug(),
            FieldScriptExpression::NumToField { debug, .. } => {
                debug.set(true);
            }
            FieldScriptExpression::Lookup { debug, .. } => {
                debug.set(true);
            }
            FieldScriptExpression::Blake3Perm { debug, .. } => {
                debug.set(true);
            }
            FieldScriptExpression::Exp7 { debug, .. } => {
                debug.set(true);
            }
            FieldScriptExpression::Add16 { debug, .. } => {
                debug.set(true);
            }
        };
    }

    fn express_to_script(
        &self,
        stack: &mut StackTracker,
        input_variables: &BTreeMap<Variable, StackVariable>,
    ) -> Vec<StackVariable> {
        match self {
            FieldScriptExpression::ValueVariable { v, debug, mut var } => {
                let intput_var = input_variables.get(v.get_var()).unwrap();
                var = stack.copy_var(intput_var.clone());
                if debug.get() == true {
                    stack.debug();
                }
                if v.get_var().get_var_size().is_some() {
                    assert_eq!(var.size(), v.get_var().get_var_size().unwrap());
                }
                vec![var]
            }
            FieldScriptExpression::InputVariable { sv, debug, mut var } => {
                let intput_var = input_variables.get(sv).unwrap();
                var = stack.copy_var(intput_var.clone());
                if debug.get() == true {
                    stack.debug();
                }
                if sv.get_var_size().is_some() {
                    assert_eq!(var.size(), sv.get_var_size().unwrap());
                }
                vec![var]
            }
            FieldScriptExpression::Constant(op) => op.express_to_script(stack, input_variables),
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
            FieldScriptExpression::Add(op) => op.express_to_script(stack, input_variables),
            FieldScriptExpression::Sub(op) => op.express_to_script(stack, input_variables),
            FieldScriptExpression::Neg(op) => op.express_to_script(stack, input_variables),
            FieldScriptExpression::Mul(op) => op.express_to_script(stack, input_variables),
            FieldScriptExpression::EqualVerify(op) => op.express_to_script(stack, input_variables),
            FieldScriptExpression::Equal(op) => op.express_to_script(stack, input_variables),
            FieldScriptExpression::ExpConstant(op) => op.express_to_script(stack, input_variables),
            FieldScriptExpression::IndexToROU(op) => op.express_to_script(stack, input_variables),
            FieldScriptExpression::NumToField { x, var, debug } => {
                x.express_to_script(stack, input_variables);
                let vars = stack
                    .custom1(
                        script! {
                            if F::U32_SIZE == 1 {
                                {u32_to_u31()}
                            } else {
                                {u32_to_u31()}
                                {u31_to_u31ext::<BabyBear4>()}
                            }
                        },
                        1,
                        1,
                        0,
                        F::U32_SIZE as u32,
                        "FieldExpr::NumToField",
                    )
                    .unwrap();

                if debug.get() == true {
                    stack.debug();
                }
                vars
            }
            FieldScriptExpression::Lookup {
                x,
                y,
                len,
                debug,
                mut var,
            } => {
                x.express_to_script(stack, input_variables);
                // todo: check y is the NumScriptExpression
                y.express_to_script(stack, input_variables);
                let vars = stack.custom1(
                    script! {
                        OP_PICK
                    },
                    1,
                    1,
                    0,
                    F::U32_SIZE as u32,
                    "ExprLookup_Result",
                );
                stack.to_altstack();
                for _ in 0..(*len) {
                    stack.op_drop();
                }
                var = stack.from_altstack();

                vec![var]
            }
            FieldScriptExpression::Blake3Perm {
                x,
                num_bytes,
                debug,
                mut var,
            } => {
                x.express_to_script(stack, input_variables);
                let vars = stack.custom1(
                    blake3_var_length(*num_bytes),
                    *num_bytes as u32,
                    //TODO:
                    32,
                    0,
                    F::U32_SIZE as u32,
                    "ExprBlake3Perm_Result",
                ).unwrap();
                vars
            }
            FieldScriptExpression::Exp7 {
                x,
                debug,
                mut var,
            } => {
                x.express_to_script(stack, input_variables);

                let vars = stack
                    .custom1(
                        value_exp_7::<F>(),
                        1,
                        1,
                        0,
                        x.var_size(),
                        "FieldExpr::Exp7",
                    )
                    .unwrap();
                var = vars[0];

                if debug.get() == true {
                    stack.debug();
                }
                vec![var]
            }
            FieldScriptExpression::Add16 { 
                x,
                debug,
                mut var,
            } => {
                let len = x.len();
                for expr in x {
                    expr.express_to_script(stack, input_variables);
                }
                let vars = stack
                .custom1(
                    script! {
                        for _ in 0..len - 1 {
                            if F::U32_SIZE == 1{
                                {u31_add::<BabyBearU31>()}
                            }else{
                                {u31ext_add::<BabyBear4>()}
                            }
                        }
                    },
                    len as u32,
                    1,
                    0,
                    F::U32_SIZE as u32,
                    "ExprADD_Result",
                )
                .unwrap();
                var = vars[0];
                vec![var]
            }
        }
    }

    fn var_size(&self) -> u32 {
        F::U32_SIZE as u32
    }
}

impl<F: BfField> Default for FieldScriptExpression<F> {
    fn default() -> Self {
        Self::zero()
    }
}

impl<F: BfField> From<F> for FieldScriptExpression<F> {
    fn from(value: F) -> Self {
        Self::new_constant(value)
    }
}

impl<F: BfField> Debug for FieldScriptExpression<F> {
    fn fmt(&self, fm: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            FieldScriptExpression::ValueVariable { v, .. } => fm
                .debug_struct("ScriptExpression::ValueVariable")
                .field("var", v)
                .finish(),
            FieldScriptExpression::InputVariable { sv, .. } => fm
                .debug_struct("ScriptExpression::InputVariable")
                .field("sv", sv)
                .finish(),
            FieldScriptExpression::Constant(op) => op.fmt(fm),
            FieldScriptExpression::Table { table, .. } => fm
                .debug_struct("ScriptExpression::Table")
                .field("table", table)
                .finish(),
            FieldScriptExpression::Add(op) => op.fmt(fm),
            FieldScriptExpression::Sub(op) => op.fmt(fm),
            FieldScriptExpression::Mul(op) => op.fmt(fm),
            FieldScriptExpression::Neg(op) => op.fmt(fm),
            FieldScriptExpression::EqualVerify(op) => op.fmt(fm),
            FieldScriptExpression::Equal(op) => op.fmt(fm),
            FieldScriptExpression::ExpConstant(op) => op.fmt(fm),
            FieldScriptExpression::IndexToROU(op) => op.fmt(fm),
            FieldScriptExpression::NumToField { debug, var, .. } => fm
                .debug_struct("ScriptExpression::Exp")
                .field("variable", var)
                .finish(),
            FieldScriptExpression::Lookup {
                x,
                y,
                len,
                debug,
                var,
            } => fm
                .debug_struct("ScriptExpression::Lookup")
                .field("variable", var)
                .finish(),
            FieldScriptExpression::Blake3Perm {
                x,
                num_bytes,
                debug,
                var,
            } => fm
                .debug_struct("ScriptExpression::Blake3Perm")
                .field("variable", var)
                .finish(),
            FieldScriptExpression::Exp7 { x, debug, var } => fm
                .debug_struct("ScriptExpression::Exp7")
                .field("variable", var)
                .finish(),
            FieldScriptExpression::Add16 { x, debug, var } => fm
                .debug_struct("ScriptExpression::Add16")
                .field("variable", var)
                .finish(),
        }
    }
}

impl<F: BfField> Clone for FieldScriptExpression<F> {
    fn clone(&self) -> Self {
        match self {
            FieldScriptExpression::ValueVariable { v, debug, var } => {
                FieldScriptExpression::ValueVariable {
                    v: v.clone(),
                    debug: debug.clone(),
                    var: var.clone(),
                }
            }
            FieldScriptExpression::InputVariable { sv, debug, var } => {
                FieldScriptExpression::InputVariable {
                    sv: sv.clone(),
                    debug: debug.clone(),
                    var: var.clone(),
                }
            }
            FieldScriptExpression::Constant(op) => FieldScriptExpression::Constant(op.clone()),
            FieldScriptExpression::Table { table, debug, var } => FieldScriptExpression::Table {
                table: table.clone(),
                debug: debug.clone(),
                var: var.clone(),
            },
            FieldScriptExpression::Add(op) => FieldScriptExpression::Add(op.clone()),
            FieldScriptExpression::Mul(op) => FieldScriptExpression::Mul(op.clone()),
            FieldScriptExpression::Sub(op) => FieldScriptExpression::Sub(op.clone()),
            FieldScriptExpression::Neg(op) => FieldScriptExpression::Neg(op.clone()),
            FieldScriptExpression::EqualVerify(op) => {
                FieldScriptExpression::EqualVerify(op.clone())
            }
            FieldScriptExpression::Equal(op) => FieldScriptExpression::Equal(op.clone()),
            FieldScriptExpression::ExpConstant(op) => {
                FieldScriptExpression::ExpConstant(op.clone())
            }
            FieldScriptExpression::IndexToROU(op) => FieldScriptExpression::IndexToROU(op.clone()),
            FieldScriptExpression::NumToField { x, debug, var } => {
                FieldScriptExpression::NumToField {
                    x: x.clone(),
                    debug: debug.clone(),
                    var: var.clone(),
                }
            }
            FieldScriptExpression::Lookup {
                x,
                y,
                len,
                debug,
                var,
            } => FieldScriptExpression::Lookup {
                x: x.clone(),
                y: y.clone(),
                len: len.clone(),
                debug: debug.clone(),
                var: var.clone(),
            },
            FieldScriptExpression::Blake3Perm { 
                x, 
                num_bytes, 
                var, 
                debug 
            } => FieldScriptExpression::Blake3Perm {
                x: x.clone(),
                num_bytes: num_bytes.clone(),
                var: var.clone(),
                debug: debug.clone(), 
            },
            FieldScriptExpression::Exp7 { x, debug, var } => {
                FieldScriptExpression::Exp7 {
                    x: x.clone(),
                    debug: debug.clone(),
                    var: var.clone(),
                }
            },
            FieldScriptExpression::Add16 { x, debug, var } => {
                FieldScriptExpression::Add16 {
                    x: x.clone(),
                    debug: debug.clone(),
                    var: var.clone(),
                }
            }
        }
    }
}

impl<F: BfField> AbstractField for FieldScriptExpression<F> {
    type F = F;

    fn zero() -> Self {
        Self::from(F::zero())
    }
    fn one() -> Self {
        Self::from(F::one())
    }
    fn two() -> Self {
        Self::from(F::two())
    }
    fn neg_one() -> Self {
        Self::from(F::neg_one())
    }

    #[inline]
    fn from_f(f: Self::F) -> Self {
        f.into()
    }

    fn from_bool(b: bool) -> Self {
        Self::from(F::from_bool(b))
    }

    fn from_canonical_u8(n: u8) -> Self {
        Self::from(F::from_canonical_u8(n))
    }

    fn from_canonical_u16(n: u16) -> Self {
        Self::from(F::from_canonical_u16(n))
    }

    fn from_canonical_u32(n: u32) -> Self {
        Self::from(F::from_canonical_u32(n))
    }

    fn from_canonical_u64(n: u64) -> Self {
        Self::from(F::from_canonical_u64(n))
    }

    fn from_canonical_usize(n: usize) -> Self {
        Self::from(F::from_canonical_usize(n))
    }

    fn from_wrapped_u32(n: u32) -> Self {
        Self::from(F::from_wrapped_u32(n))
    }

    fn from_wrapped_u64(n: u64) -> Self {
        Self::from(F::from_wrapped_u64(n))
    }

    fn generator() -> Self {
        Self::from(F::generator())
    }
}

impl<F: BfField> Add<Self> for FieldScriptExpression<F> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Self::new_add(self, rhs)
    }
}

impl<F: BfField> Add<F> for FieldScriptExpression<F> {
    type Output = Self;

    fn add(self, rhs: F) -> Self {
        self + Self::from(rhs)
    }
}

impl<F: BfField> Add<&Self> for FieldScriptExpression<F> {
    type Output = Self;

    fn add(self, rhs: &Self) -> Self {
        Self::new_add(self, rhs.clone())
    }
}

impl<F: BfField> AddAssign for FieldScriptExpression<F> {
    fn add_assign(&mut self, rhs: Self) {
        *self = self.clone() + rhs;
    }
}

impl<F: BfField> AddAssign<F> for FieldScriptExpression<F> {
    fn add_assign(&mut self, rhs: F) {
        *self += Self::from(rhs);
    }
}

impl<F: BfField> Sum for FieldScriptExpression<F> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|x, y| x + y).unwrap_or(Self::zero())
    }
}

impl<F: BfField> Sum<F> for FieldScriptExpression<F> {
    fn sum<I: Iterator<Item = F>>(iter: I) -> Self {
        iter.map(|x| Self::from(x)).sum()
    }
}

impl<F: BfField> Sub for FieldScriptExpression<F> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        Self::new_sub(self, rhs)
    }
}

impl<F: BfField> Sub<F> for FieldScriptExpression<F> {
    type Output = Self;

    fn sub(self, rhs: F) -> Self {
        self - Self::from(rhs)
    }
}

impl<F: BfField> SubAssign for FieldScriptExpression<F> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = self.clone() - rhs;
    }
}

impl<F: BfField> SubAssign<F> for FieldScriptExpression<F> {
    fn sub_assign(&mut self, rhs: F) {
        *self -= Self::from(rhs);
    }
}

impl<F: BfField> Neg for FieldScriptExpression<F> {
    type Output = Self;

    fn neg(self) -> Self {
        Self::new_neg(self)
    }
}

impl<F: BfField> Mul for FieldScriptExpression<F> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        #[allow(clippy::suspicious_arithmetic_impl)]
        Self::new_mul(self, rhs)
    }
}

impl<F: BfField> Mul<F> for FieldScriptExpression<F> {
    type Output = Self;

    fn mul(self, rhs: F) -> Self {
        self * Self::from(rhs)
    }
}

impl<F: BfField> Div for FieldScriptExpression<F> {
    type Output = Fraction<F>;

    fn div(self, rhs: Self) -> Fraction<F> {
        Fraction::<F>::new(self, rhs)
    }
}

impl<F: BfField> MulAssign for FieldScriptExpression<F> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.clone() * rhs;
    }
}

impl<F: BfField> MulAssign<F> for FieldScriptExpression<F> {
    fn mul_assign(&mut self, rhs: F) {
        *self *= Self::from(rhs);
    }
}

impl<F: BfField> Product for FieldScriptExpression<F> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|x, y| x * y).unwrap_or(Self::one())
    }
}

impl<F: BfField> Product<F> for FieldScriptExpression<F> {
    fn product<I: Iterator<Item = F>>(iter: I) -> Self {
        iter.map(|x| Self::from(x)).product()
    }
}

impl<F: BfField> FieldScriptExpression<F> {
    pub fn lookup(&self, index: u32, len: usize) -> Self {
        let index = NumScriptExpression::from(index);
        Self::Lookup {
            x: Arc::new(Box::new(self.clone())),
            y: Arc::new(Box::new(index)),
            len: len,
            debug: Cell::new(false),
            var: StackVariable::null(),
        }
    }
    pub fn from_table(table: &[F]) -> Self {
        Self::Table {
            table: table.into(),
            debug: Cell::new(false),
            var: StackVariable::null(),
        }
    }
    pub fn blake3(&self, num_bytes: usize) -> Self {
        Self::Blake3Perm { 
            x: Arc::new(Box::new(self.clone())),
            num_bytes, 
            debug: Cell::new(false),
            var: StackVariable::null(),
        }
    }
    pub fn exp7(&self) -> Self {
        Self::Exp7 { 
            x: Arc::new(Box::new(self.clone())),
            debug: Cell::new(false),
            var: StackVariable::null(),
         }
    }
    pub fn add_long(rhs: &[Self]) -> Self {
        let vec = rhs.iter().map(|x| Arc::new(Box::new(x.clone()) as Box<_>)).collect::<Vec<_>>();
        Self::Add16 { 
            x: vec, 
            debug: Cell::new(false),
            var: StackVariable::null() 
        }
    }
}

#[cfg(test)]
mod tests {
    use alloc::boxed::Box;
    use alloc::collections::BTreeMap;
    use alloc::sync::Arc;
    use alloc::vec::Vec;
    use bitcoin::constants;
    use bitcoin::hex::FromHex;
    use scripts::u32_std::u32_equalverify;
    use core::cell::{self, Cell};

    use bitcoin_script_stack::stack::{self, StackTracker, StackVariable};
    use common::{AbstractField, BabyBear, BinomialExtensionField};
    use p3_air::AirBuilder;
    use p3_field::{TwoAdicField, PrimeField};
    use p3_matrix::Matrix;
    use primitives::field::BfField;
    use scripts::treepp::*;
    use scripts::u31_lib::{u31_equalverify, u31ext_equalverify, BabyBear4};

    use super::{Expression, FieldScriptExpression, Variable, *};
    type EF = BinomialExtensionField<BabyBear, 4>;
    type F = BabyBear;

    #[test]
    fn test_field_expr_expconst() {
        {
            let bmap = BTreeMap::new();
            let mut stack = StackTracker::new();
            let a_value = BabyBear::two();
            let b_value = a_value.exp_u64(2);
            let a = FieldScriptExpression::from(a_value);
            let b = a.exp_constant(2);
            let equal = b.equal_verify_for_f(b_value);
            equal.express_to_script(&mut stack, &bmap);
            stack.op_true();
            let res = stack.run();
            assert!(res.success);
        }

        {
            let bmap = BTreeMap::new();
            let mut stack = StackTracker::new();
            let a_value = EF::two();
            let b_value = a_value.exp_u64(2);
            let a = FieldScriptExpression::from(a_value);
            let b = a.exp_constant(2);
            let equal = b.equal_verify_for_f(b_value);
            equal.express_to_script(&mut stack, &bmap);
            stack.op_true();
            let res = stack.run();
            assert!(res.success);
        }
    }

    #[test]
    fn test_field_expr_index_to_rou() {
        {
            let bmap = BTreeMap::new();
            let mut stack = StackTracker::new();
            let sub_group_bits = 10u32;
            let generator = BabyBear::two_adic_generator(sub_group_bits as usize);
            let index = 7u32;
            let res = generator.exp_u64(index as u64);

            let b = FieldScriptExpression::index_to_rou(index, sub_group_bits);
            // b.set_debug();
            let res_expr = FieldScriptExpression::from(res);
            let equal = b.equal_verify(res_expr);
            equal.express_to_script(&mut stack, &bmap);
            stack.op_true();
            let res = stack.run();
            assert!(res.success);
        }

        {
            let bmap = BTreeMap::new();
            let mut stack = StackTracker::new();
            let sub_group_bits = 10u32;
            let generator = EF::two_adic_generator(sub_group_bits as usize);
            let index = 7u32;
            let res = generator.exp_u64(index as u64);

            let b = FieldScriptExpression::index_to_rou(index, sub_group_bits);
            let equal = b.equal_verify_for_f(res);
            equal.express_to_script(&mut stack, &bmap);
            stack.op_true();
            let res = stack.run();
            assert!(res.success);
        }
    }

    #[test]
    fn test_num_to_field() {
        let num = 182712u32;

        {
            let bmap = BTreeMap::new();
            let mut stack = StackTracker::new();
            let a = NumScriptExpression::from(num);
            let b = a.num_to_field();
            let res = BabyBear::from_canonical_u32(num);
            let equal = b.equal_verify_for_f(res);
            equal.express_to_script(&mut stack, &bmap);
            stack.op_true();
            let res = stack.run();
            assert!(res.success);
        }

        {
            let bmap = BTreeMap::new();
            let mut stack = StackTracker::new();
            let a = NumScriptExpression::from(num);
            let b = a.num_to_field();
            let res = EF::from_canonical_u32(num);
            let equal = b.equal_verify_for_f(res);
            equal.express_to_script(&mut stack, &bmap);
            stack.op_true();
            let res = stack.run();
            assert!(res.success);
        }
    }

    #[test]
    fn test_script_expression_add() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = FieldScriptExpression::from(BabyBear::one());
        let b = FieldScriptExpression::from(BabyBear::two());
        let c = a + b;
        c.set_debug();

        let d = FieldScriptExpression::from(BabyBear::two());
        let e = FieldScriptExpression::from(BabyBear::two());
        let f = d + e;

        let g = c + f; // 4 + 3 = 7
        let script = g.express_to_script(&mut stack, &bmap);
        stack.number(BabyBear::from_canonical_u32(7u32).as_u32_vec()[0]);
        stack.op_equal();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_script_expression_u31add_u31ext() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = FieldScriptExpression::from(BabyBear::one());
        let b = FieldScriptExpression::from(EF::two());
        let c = a.add_ext(b);

        let d = FieldScriptExpression::from(BabyBear::two());
        let e = FieldScriptExpression::from(EF::two());
        let f = e.add_base(d);

        let g = c + f; // 4 + 3 = 7
        let h = g.equal_verify_for_f(EF::from_canonical_u32(7u32));
        let script = h.express_to_script(&mut stack, &bmap);
        stack.op_true();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_script_expression_u31sub_u31ext() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = FieldScriptExpression::from(BabyBear::one());
        let b = FieldScriptExpression::from(EF::two());
        let c = a.sub_ext(b);

        let d = FieldScriptExpression::from(BabyBear::two());
        let e = FieldScriptExpression::from(EF::from_canonical_u32(4));
        let f = e.sub_base(d);
        let g = c + f; // 4 + 3 = 7
        let script = g.express_to_script(&mut stack, &bmap);
        stack.bignumber(EF::from_canonical_u32(1u32).as_u32_vec());
        stack.custom(
            u31ext_equalverify::<BabyBear4>(),
            2,
            false,
            0,
            "u31ext_equalverify",
        );
        stack.op_true();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_script_expression_u31mul_u31ext() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = FieldScriptExpression::from(BabyBear::one());
        let b = FieldScriptExpression::from(EF::two());
        b.set_debug();
        // let c = a.mul_ext(b);
        let c = b.mul_base(a);
        c.set_debug();
        let d = FieldScriptExpression::from(BabyBear::two());
        let e = FieldScriptExpression::from(EF::from_canonical_u32(4));
        let f = e.mul_base(d);
        f.set_debug();
        let g = c * f;
        let equal = g.equal_for_f(EF::from_canonical_u32(16));
        equal.express_to_script(&mut stack, &bmap);
        let res = stack.run();
        println!("{:?}", res.error);
        println!("{:?}", res.error_msg);
        assert!(res.success);
    }

    #[test]
    fn test_ext_constant() {
        let mut stack = StackTracker::new();
        let bmap = BTreeMap::new();
        let a = FieldScriptExpression::from(EF::one());
        a.express_to_script(&mut stack, &bmap);
        let res = EF::one();

        stack.bignumber(res.as_u32_vec());
        stack.custom(
            u31ext_equalverify::<BabyBear4>(),
            2,
            false,
            0,
            "u31ext_equalverify",
        );

        stack.op_true();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_script_expr_with_input() {
        let var1 = Variable::new(0, 0);
        let var2 = Variable::new(0, 1);
        let var3 = Variable::new(1, 0);
        let var4 = Variable::new(1, 1);

        let mut stack = StackTracker::new();
        let mut bmap = BTreeMap::new();
        bmap.insert(
            var1,
            stack.var(
                1,
                script! { {BabyBear::from_canonical_u32(1u32).as_u32_vec()[0]}},
                "input 1",
            ),
        );
        bmap.insert(
            var2,
            stack.var(
                1,
                script! { {BabyBear::from_canonical_u32(2u32).as_u32_vec()[0]}},
                "input 2",
            ),
        );
        bmap.insert(
            var3,
            stack.var(
                1,
                script! {{BabyBear::from_canonical_u32(3u32).as_u32_vec()[0]}},
                "input 3",
            ),
        );
        bmap.insert(
            var4,
            stack.var(
                1,
                script! {{BabyBear::from_canonical_u32(4u32).as_u32_vec()[0]}},
                "input 4",
            ),
        );

        let var1_wrap = FieldScriptExpression::InputVariable {
            sv: var1,
            debug: Cell::new(false),
            var: StackVariable::null(),
        };
        let var2_wrap = FieldScriptExpression::<BabyBear>::InputVariable {
            sv: var2,
            debug: Cell::new(false),
            var: StackVariable::null(),
        };
        let var3_wrap = FieldScriptExpression::InputVariable {
            sv: var3,
            debug: Cell::new(false),
            var: StackVariable::null(),
        };
        let var4_wrap = FieldScriptExpression::<BabyBear>::InputVariable {
            sv: var4,
            debug: Cell::new(false),
            var: StackVariable::null(),
        };
        let res1 = var1_wrap + var2_wrap;
        let res2 = var3_wrap + var4_wrap;

        let res = res1 + res2;
        res.express_to_script(&mut stack, &bmap);

        stack.number(BabyBear::from_canonical_u32(10u32).as_u32_vec()[0]);
        stack.op_equalverify();

        stack.drop(*bmap.get(&var4).unwrap());
        stack.drop(*bmap.get(&var3).unwrap());
        stack.drop(*bmap.get(&var2).unwrap());
        stack.drop(*bmap.get(&var1).unwrap());
        stack.op_true();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_script_expr_with_extinput() {
        let var1 = Variable::new(0, 0);
        let var2 = Variable::new(0, 1);
        let var3 = Variable::new(1, 0);
        let var4 = Variable::new(1, 1);

        let mut stack = StackTracker::new();
        let mut bmap = BTreeMap::new();
        bmap.insert(
            var1,
            stack.var(
                4,
                script! {
                    {EF::from_canonical_u32(1u32).as_u32_vec()[3]}
                    {EF::from_canonical_u32(1u32).as_u32_vec()[2]}
                    {EF::from_canonical_u32(1u32).as_u32_vec()[1]}
                    {EF::from_canonical_u32(1u32).as_u32_vec()[0]}
                },
                "input 1",
            ),
        );
        bmap.insert(
            var2,
            stack.var(
                4,
                script! {
                    {EF::from_canonical_u32(2u32).as_u32_vec()[3]}
                    {EF::from_canonical_u32(2u32).as_u32_vec()[2]}
                    {EF::from_canonical_u32(2u32).as_u32_vec()[1]}
                    {EF::from_canonical_u32(2u32).as_u32_vec()[0]}
                },
                "input 2",
            ),
        );
        bmap.insert(
            var3,
            stack.var(
                4,
                script! {{EF::from_canonical_u32(3u32).as_u32_vec()[3]} {EF::from_canonical_u32(3u32).as_u32_vec()[2]} {EF::from_canonical_u32(3u32).as_u32_vec()[1]} {EF::from_canonical_u32(3u32).as_u32_vec()[0]}},
                "input 3",
            ),
        );
        bmap.insert(
            var4,
            stack.var(
                4,
                script! {{EF::from_canonical_u32(4u32).as_u32_vec()[3]} {EF::from_canonical_u32(4u32).as_u32_vec()[2]} {EF::from_canonical_u32(4u32).as_u32_vec()[1]} {EF::from_canonical_u32(4u32).as_u32_vec()[0]}},
                "input 4",
            ),
        );

        let var1_wrap = FieldScriptExpression::<EF>::InputVariable {
            sv: var1,
            debug: Cell::new(false),
            var: StackVariable::null(),
        };
        let var2_wrap = FieldScriptExpression::InputVariable {
            sv: var2,
            debug: Cell::new(false),
            var: StackVariable::null(),
        };
        let var3_wrap = FieldScriptExpression::InputVariable {
            sv: var3,
            debug: Cell::new(false),
            var: StackVariable::null(),
        };
        let var4_wrap = FieldScriptExpression::InputVariable {
            sv: var4,
            debug: Cell::new(false),
            var: StackVariable::null(),
        };
        stack.debug();
        let res1 = var1_wrap + var2_wrap;
        let res2 = var3_wrap + var4_wrap;

        let res = res1 + res2 + EF::from_canonical_u32(3);
        res.express_to_script(&mut stack, &bmap);

        // stack.debug();
        stack.bignumber(EF::from_canonical_u32(13u32).as_u32_vec());
        stack.custom(
            u31ext_equalverify::<BabyBear4>(),
            2,
            false,
            0,
            "u31ext_equalverify",
        );
        stack.debug();

        stack.drop(*bmap.get(&var4).unwrap());
        stack.drop(*bmap.get(&var3).unwrap());
        stack.drop(*bmap.get(&var2).unwrap());
        stack.drop(*bmap.get(&var1).unwrap());
        stack.op_true();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_script_expression_extadd() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = FieldScriptExpression::from(EF::one());
        let b = FieldScriptExpression::from(EF::two());
        let c = a + b;

        let script = c.express_to_script(&mut stack, &bmap);
        stack.debug();
        let res = EF::one() + EF::two();

        stack.bignumber(res.as_u32_vec());
        stack.debug();
        stack.custom(
            u31ext_equalverify::<BabyBear4>(),
            2,
            false,
            0,
            "u31ext_equalverify",
        );
        stack.op_true();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_base_addlong(){
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = FieldScriptExpression::from(F::one());
        let b1 = FieldScriptExpression::from(F::two());
        let b2 = FieldScriptExpression::from(F::two());
        let c = FieldScriptExpression::add_long(&vec![a,b1,b2]);

        let script = c.express_to_script(&mut stack, &bmap);
        stack.debug();
        let res = F::one() + F::two() + F::two();

        stack.bignumber(res.as_u32_vec());
        stack.debug();
        stack.custom(
            u31_equalverify(),
            2,
            false,
            0,
            "u31ext_equalverify",
        );
        stack.op_true();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_script_expression_sub() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = FieldScriptExpression::from(BabyBear::one());
        let b = FieldScriptExpression::from(BabyBear::two());
        let c = b - a; // 1

        let d = FieldScriptExpression::from(BabyBear::two());
        let e = FieldScriptExpression::from(BabyBear::from_canonical_u32(8));
        let f = e - d; // 6

        let g = f - c; // 5
        let script = g.express_to_script(&mut stack, &bmap);
        stack.number(BabyBear::from_canonical_u32(5u32).as_u32_vec()[0]);
        stack.op_equal();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_script_expression_extsub() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = FieldScriptExpression::from(EF::one());
        let b = FieldScriptExpression::from(EF::two());
        let c = b - a; // 1

        let d = FieldScriptExpression::from(EF::two());
        let e = FieldScriptExpression::from(EF::from_canonical_u32(8));
        let f = e - d; // 6
        let g = f - c; // 5
        let script = g.express_to_script(&mut stack, &bmap);
        stack.bignumber(EF::from_canonical_u32(5u32).as_u32_vec());
        stack.custom(
            u31ext_equalverify::<BabyBear4>(),
            2,
            false,
            0,
            "u31ext_equalverify",
        );
        stack.op_true();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_script_expression_mul() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = FieldScriptExpression::from(BabyBear::one());
        let b = FieldScriptExpression::from(BabyBear::two());
        let c = b * a; // 2

        let d = FieldScriptExpression::from(BabyBear::two());
        let e = FieldScriptExpression::from(BabyBear::from_canonical_u32(8));
        let f = e * d * BabyBear::one(); // 16
        stack.show_stack();
        let g = f * c; // 32
        let script = g.express_to_script(&mut stack, &bmap);
        stack.number(BabyBear::from_canonical_u32(32u32).as_u32_vec()[0]);
        stack.op_equal();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_script_expression_extmul() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = FieldScriptExpression::from(EF::one());
        let b = FieldScriptExpression::from(EF::two());
        let c = b * a; // 2

        let d = FieldScriptExpression::from(EF::two());
        let e = FieldScriptExpression::from(EF::from_canonical_u32(8));
        let f = e * d; // 16
        let g = f * c; // 32
        g.express_to_script(&mut stack, &bmap);

        stack.show_stack();

        stack.bignumber(EF::from_canonical_u32(32u32).as_u32_vec());
        stack.custom(
            u31ext_equalverify::<BabyBear4>(),
            2,
            false,
            0,
            "u31ext_equalverify",
        );
        stack.op_true();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_script_expression_neg() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = FieldScriptExpression::from(BabyBear::one());
        let b = -a * BabyBear::two();
        let script = b.express_to_script(&mut stack, &bmap);
        stack.number(BabyBear::from_canonical_u32(BabyBear::MOD - 2).as_u32_vec()[0]);
        stack.op_equal();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_script_expression_extneg() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = FieldScriptExpression::from(EF::one());
        let b = -a * EF::two();
        let equal = b.equal_for_f(EF::from_canonical_u32(EF::MOD - 2));
        let script = equal.express_to_script(&mut stack, &bmap);
        // let res = stack.run();
        // assert!(res.success);
    }
    #[test]
    fn test_ext_equal() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = FieldScriptExpression::from(EF::two());
        let exp = a.equal_for_f(EF::two());
        let script = exp.express_to_script(&mut stack, &bmap);
        let res = stack.run();
        assert!(res.success);

        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = FieldScriptExpression::from(BabyBear::two());
        let exp = a.equal_for_f(BabyBear::two());
        let script = exp.express_to_script(&mut stack, &bmap);
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_exp_7() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a_value = BabyBear::two();
        let b_value = a_value.exp_u64(7);
        let a = FieldScriptExpression::from(a_value);
        let b = a.exp7();
        let equal = b.equal_verify_for_f(b_value);
        equal.express_to_script(&mut stack, &bmap);
        stack.op_true();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_lookup() {
        let vec = vec![
            BabyBear::from_canonical_u32(1 as u32),
            BabyBear::from_canonical_u32(2 as u32),
            BabyBear::from_canonical_u32(3 as u32),
            BabyBear::from_canonical_u32(4 as u32),
            BabyBear::from_canonical_u32(5 as u32),
        ];
        let mut stack = StackTracker::new();
        let bmap = BTreeMap::new();

        let table = FieldScriptExpression::Table {
            table: vec.clone(),
            debug: Cell::new(false),
            var: StackVariable::null(),
        };

        let index = 4;

        let m = table.lookup(index, vec.len());

        let script = m.express_to_script(&mut stack, &bmap);

        stack.number(5 as u32);

        stack.custom(u31_equalverify(), 2, false, 0, "u31_equalverify");
        stack.op_true();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_blake3_perm() {
        let mut vec = vec![];
        for _ in 0..16 {
            vec.push(BabyBear::one());
            vec.push(BabyBear::zero());
            vec.push(BabyBear::zero());
            vec.push(BabyBear::zero());
        }
        let mut stack = StackTracker::new();
        let bmap = BTreeMap::new();

        let preimage = FieldScriptExpression::Table {
            table: vec.clone(),
            debug: Cell::new(false),
            var: StackVariable::null(),
        };

        let m = preimage.blake3(64);

        let script = m.express_to_script(&mut stack, &bmap);

        let hex = "86ca95aefdee3d969af9bcc78b48a5c1115be5d66cafc2fc106bbd982d820e70";
        let hex: String = hex
            .chars()
            .filter(|c| c.is_ascii_digit() || c.is_ascii_alphabetic())
            .collect();

        let bytes: Vec<u8> = (0..hex.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).unwrap())
            .collect::<Vec<u8>>();

        for i in (0 .. bytes.len()).rev().step_by(4) {
            stack.number(bytes[i] as u32);
            stack.number(bytes[i-1] as u32);
            stack.number(bytes[i-2] as u32);
            stack.number(bytes[i-3] as u32);
            stack.custom(u32_equalverify(), 8, false, 0, "u32_equalverify");
        }

        stack.op_true();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_poseidon2_perm() {
        let t = 16;
        let rounds_f_beginning = 1;
        let rounds_p = 3;
        let rounds = 3;

        let mut current_state = vec![];
        for i in 0..t {
            current_state.push(FieldScriptExpression::from(BabyBear::from_canonical_u32(i as u32)));
        }

        // matmul_external(&mut current_state);

        // for r in 0..rounds_f_beginning {
        //     current_state = add_rc(&current_state, &RC16[r]);
        //     current_state = sbox(&current_state);
        //     matmul_external(&mut current_state);
        // }

        let p_end = rounds_f_beginning + rounds_p;
        for r in rounds_f_beginning..p_end {
            current_state[0].add_assign(RC16[r][0]);
            current_state[0] = current_state[0].exp7();
            matmul_internal(&mut current_state);
        }
        
        // for r in p_end..rounds {
        //     current_state = add_rc(&current_state, &RC16[r]);
        //     current_state = sbox(&current_state);
        //     matmul_external(&mut current_state);
        // }
        let mut stack = StackTracker::new();
        let bmap = BTreeMap::new();

        println!("begin express_to_script");
        current_state[0].express_to_script(&mut stack, &bmap);
        println!("finish express_to_script");
        stack.debug();
        
    }

    fn sbox(input: &[FieldScriptExpression<F>]) -> Vec<FieldScriptExpression<F>> {
        input.iter().map(|el| el.exp7()).collect()
    }

    
    fn matmul_internal(input: &mut[FieldScriptExpression<F>]) {
        let sum = FieldScriptExpression::add_long(input);
        // let mut sum = input[0].clone();
        // input
        //     .iter()
        //     .skip(1)
        //     .take(t-1)
        //     .for_each(|el| sum.add_assign(el.clone()));
        // Add sum + diag entry * element to each element
        for i in 0..input.len() {
            input[i].mul_assign(FieldScriptExpression::from(MAT_DIAG16_M_1[i]));
            input[i].add_assign(sum.clone());
        }
    }

    fn matmul_external(input: &mut[FieldScriptExpression<F>]) {
        let t = 16;
        matmul_m4(input);

        // Applying second cheap matrix for t > 4
        let t4 = t / 4;
        let mut stored = vec![FieldScriptExpression::from(F::zero()); 4];
        for l in 0..4 {
            stored[l] = input[l].clone();
            for j in 1..t4 {
                stored[l].add_assign(input[4 * j + l].clone());
            }
        }
        for i in 0..input.len() {
            input[i].add_assign(stored[i % 4].clone());
        }
    }

    fn matmul_m4(input: &mut[FieldScriptExpression<F>]) {
        let t = 16;
        let t4 = t / 4;
        for i in 0..t4 {
            let start_index = i * 4;
            let mut t_0 = input[start_index].clone();
            t_0.add_assign(input[start_index + 1].clone());
            let mut t_1 = input[start_index + 2].clone();
            t_1.add_assign(input[start_index + 3].clone());
            let mut t_2 = input[start_index + 1].clone();
            t_2 = t_2.clone() + t_2.clone();
            t_2.add_assign(t_1.clone());
            let mut t_3 = input[start_index + 3].clone();
            t_3 = t_3.clone() + t_3.clone();
            t_3.add_assign(t_0.clone());
            let mut t_4 = t_1.clone();
            t_4 = t_4.clone() * F::from_canonical_u32(2 as u32);
            t_4 = t_4.clone() * F::from_canonical_u32(2 as u32);
            t_4.add_assign(t_3.clone());
            let mut t_5 = t_0.clone();
            t_5 = t_5.clone() + t_5.clone();
            t_5 = t_5.clone() + t_5.clone();
            t_5.add_assign(t_2.clone());
            let mut t_6 = t_3.clone();
            t_6.add_assign(t_5.clone());
            let mut t_7 = t_2.clone();
            t_7.add_assign(t_4.clone());
            input[start_index] = t_6.clone();
            input[start_index + 1] = t_5.clone();
            input[start_index + 2] = t_7.clone();
            input[start_index + 3] = t_4.clone();
        }
    }

// plonky3 optimize:
// Multiply a 4-element vector x by:
// [ 2 3 1 1 ]
// [ 1 2 3 1 ]
// [ 1 1 2 3 ]
// [ 3 1 1 2 ].
// This is more efficient than the previous matrix.
// fn apply_mat4<AF>(x: &mut [AF; 4])
// where
//     AF: AbstractField,
// {
//     let t01 = x[0].clone() + x[1].clone();
//     let t23 = x[2].clone() + x[3].clone();
//     let t0123 = t01.clone() + t23.clone();
//     let t01123 = t0123.clone() + x[1].clone();
//     let t01233 = t0123.clone() + x[3].clone();
//     // The order here is important. Need to overwrite x[0] and x[2] after x[1] and x[3].
//     x[3] = t01233.clone() + x[0].double(); // 3*x[0] + x[1] + x[2] + 2*x[3]
//     x[1] = t01123.clone() + x[2].double(); // x[0] + 2*x[1] + 3*x[2] + x[3]
//     x[0] = t01123 + t01; // 2*x[0] + 3*x[1] + x[2] + x[3]
//     x[2] = t01233 + t23; // x[0] + x[1] + 2*x[2] + 3*x[3]
// }

    fn p3_matmul_m4(input: &mut[FieldScriptExpression<F>]) {
        let t = 16;
        let t4 = t / 4;
        for i in 0..t4 {
            let start_index = i * 4;
            let t01 = input[start_index].clone() + input[start_index + 1].clone();
            let t23 = input[start_index + 2].clone() + input[start_index + 3].clone();
            let t0123 = t01.clone() + t23.clone();
            let t01123 = t0123.clone() + input[start_index + 1].clone();
            let t01233 = t0123.clone() + input[start_index + 3].clone();
            // The order here is important. Need to overwrite x[0] and x[2] after x[1] and x[3].
            input[start_index + 3] = t01233.clone() + input[start_index].clone() + input[start_index].clone(); // 3*x[0] + x[1] + x[2] + 2*x[3]
            input[start_index + 1] = t01123.clone() + input[start_index + 2].clone() + input[start_index + 2].clone(); // x[0] + 2*x[1] + 3*x[2] + x[3]
            input[start_index] = t01123 + t01; // 2*x[0] + 3*x[1] + x[2] + x[3]
            input[start_index + 2] = t01233 + t23; // x[0] + x[1] + 2*x[2] + 3*x[3]
        }
    }


    fn add_rc(input: &[FieldScriptExpression<F>], rc: &[F]) -> Vec<FieldScriptExpression<F>> {
        input
            .iter()
            .zip(rc.iter())
            .map(|(a, b)| {
                let mut r = a.clone();
                r.add_assign(FieldScriptExpression::from(*b));
                r
            })
            .collect()
    }

    use lazy_static::lazy_static;

lazy_static! {

//p3 opt
// See poseidon2\src\diffusion.rs for information on how to double check these matrices in Sage.
// Optimized diffusion matrices for Babybear16:
// Small entries: [-2, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16]
// Power of 2 entries: [-2,   1,   2,   4,   8,  16,  32,  64, 128, 256, 512, 1024, 2048, 4096, 8192, 32768]
//                   = [ ?, 2^0, 2^1, 2^2, 2^3, 2^4, 2^5, 2^6, 2^7, 2^8, 2^9, 2^10, 2^11, 2^12, 2^13, 2^15]
    pub static ref MAT_DIAG16_M_1: Vec<BabyBear> = vec![
    BabyBear::from_canonical_u32(0x0a632d94),
    BabyBear::from_canonical_u32(0x6db657b7),
    BabyBear::from_canonical_u32(0x56fbdc9e),
    BabyBear::from_canonical_u32(0x052b3d8a),
    BabyBear::from_canonical_u32(0x33745201),
    BabyBear::from_canonical_u32(0x5c03108c),
    BabyBear::from_canonical_u32(0x0beba37b),
    BabyBear::from_canonical_u32(0x258c2e8b),
    BabyBear::from_canonical_u32(0x12029f39),
    BabyBear::from_canonical_u32(0x694909ce),
    BabyBear::from_canonical_u32(0x6d231724),
    BabyBear::from_canonical_u32(0x21c3b222),
    BabyBear::from_canonical_u32(0x3c0904a5),
    BabyBear::from_canonical_u32(0x01d6acda),
    BabyBear::from_canonical_u32(0x27705c83),
    BabyBear::from_canonical_u32(0x5231c802),
    ];

    pub static ref MAT_INTERNAL16: Vec<Vec<BabyBear>> = vec![
    vec![BabyBear::from_canonical_u32(0x0a632d95),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    ],
    vec![BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x6db657b8),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    ],
    vec![BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x56fbdc9f),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    ],
    vec![BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x052b3d8b),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    ],
    vec![BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x33745202),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    ],
    vec![BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x5c03108d),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    ],
    vec![BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x0beba37c),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    ],
    vec![BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x258c2e8c),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    ],
    vec![BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x12029f3a),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    ],
    vec![BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x694909cf),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    ],
    vec![BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x6d231725),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    ],
    vec![BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x21c3b223),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    ],
    vec![BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x3c0904a6),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    ],
    vec![BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x01d6acdb),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    ],
    vec![BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x27705c84),
    BabyBear::from_canonical_u32(0x00000001),
    ],
    vec![BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x00000001),
    BabyBear::from_canonical_u32(0x5231c803),
    ],
    ];

    pub static ref RC16: Vec<Vec<BabyBear>> = vec![
    vec![BabyBear::from_canonical_u32(0x69cbb6af),
    BabyBear::from_canonical_u32(0x46ad93f9),
    BabyBear::from_canonical_u32(0x60a00f4e),
    BabyBear::from_canonical_u32(0x6b1297cd),
    BabyBear::from_canonical_u32(0x23189afe),
    BabyBear::from_canonical_u32(0x732e7bef),
    BabyBear::from_canonical_u32(0x72c246de),
    BabyBear::from_canonical_u32(0x2c941900),
    BabyBear::from_canonical_u32(0x0557eede),
    BabyBear::from_canonical_u32(0x1580496f),
    BabyBear::from_canonical_u32(0x3a3ea77b),
    BabyBear::from_canonical_u32(0x54f3f271),
    BabyBear::from_canonical_u32(0x0f49b029),
    BabyBear::from_canonical_u32(0x47872fe1),
    BabyBear::from_canonical_u32(0x221e2e36),
    BabyBear::from_canonical_u32(0x1ab7202e),
    ],
    vec![BabyBear::from_canonical_u32(0x487779a6),
    BabyBear::from_canonical_u32(0x3851c9d8),
    BabyBear::from_canonical_u32(0x38dc17c0),
    BabyBear::from_canonical_u32(0x209f8849),
    BabyBear::from_canonical_u32(0x268dcee8),
    BabyBear::from_canonical_u32(0x350c48da),
    BabyBear::from_canonical_u32(0x5b9ad32e),
    BabyBear::from_canonical_u32(0x0523272b),
    BabyBear::from_canonical_u32(0x3f89055b),
    BabyBear::from_canonical_u32(0x01e894b2),
    BabyBear::from_canonical_u32(0x13ddedde),
    BabyBear::from_canonical_u32(0x1b2ef334),
    BabyBear::from_canonical_u32(0x7507d8b4),
    BabyBear::from_canonical_u32(0x6ceeb94e),
    BabyBear::from_canonical_u32(0x52eb6ba2),
    BabyBear::from_canonical_u32(0x50642905),
    ],
    vec![BabyBear::from_canonical_u32(0x05453f3f),
    BabyBear::from_canonical_u32(0x06349efc),
    BabyBear::from_canonical_u32(0x6922787c),
    BabyBear::from_canonical_u32(0x04bfff9c),
    BabyBear::from_canonical_u32(0x768c714a),
    BabyBear::from_canonical_u32(0x3e9ff21a),
    BabyBear::from_canonical_u32(0x15737c9c),
    BabyBear::from_canonical_u32(0x2229c807),
    BabyBear::from_canonical_u32(0x0d47f88c),
    BabyBear::from_canonical_u32(0x097e0ecc),
    BabyBear::from_canonical_u32(0x27eadba0),
    BabyBear::from_canonical_u32(0x2d7d29e4),
    BabyBear::from_canonical_u32(0x3502aaa0),
    BabyBear::from_canonical_u32(0x0f475fd7),
    BabyBear::from_canonical_u32(0x29fbda49),
    BabyBear::from_canonical_u32(0x018afffd),
    ],
    vec![BabyBear::from_canonical_u32(0x0315b618),
    BabyBear::from_canonical_u32(0x6d4497d1),
    BabyBear::from_canonical_u32(0x1b171d9e),
    BabyBear::from_canonical_u32(0x52861abd),
    BabyBear::from_canonical_u32(0x2e5d0501),
    BabyBear::from_canonical_u32(0x3ec8646c),
    BabyBear::from_canonical_u32(0x6e5f250a),
    BabyBear::from_canonical_u32(0x148ae8e6),
    BabyBear::from_canonical_u32(0x17f5fa4a),
    BabyBear::from_canonical_u32(0x3e66d284),
    BabyBear::from_canonical_u32(0x0051aa3b),
    BabyBear::from_canonical_u32(0x483f7913),
    BabyBear::from_canonical_u32(0x2cfe5f15),
    BabyBear::from_canonical_u32(0x023427ca),
    BabyBear::from_canonical_u32(0x2cc78315),
    BabyBear::from_canonical_u32(0x1e36ea47),
    ],
    vec![BabyBear::from_canonical_u32(0x5a8053c0),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    ],
    vec![BabyBear::from_canonical_u32(0x693be639),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    ],
    vec![BabyBear::from_canonical_u32(0x3858867d),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    ],
    vec![BabyBear::from_canonical_u32(0x19334f6b),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    ],
    vec![BabyBear::from_canonical_u32(0x128f0fd8),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    ],
    vec![BabyBear::from_canonical_u32(0x4e2b1ccb),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    ],
    vec![BabyBear::from_canonical_u32(0x61210ce0),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    ],
    vec![BabyBear::from_canonical_u32(0x3c318939),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    ],
    vec![BabyBear::from_canonical_u32(0x0b5b2f22),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    ],
    vec![BabyBear::from_canonical_u32(0x2edb11d5),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    ],
    vec![BabyBear::from_canonical_u32(0x213effdf),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    ],
    vec![BabyBear::from_canonical_u32(0x0cac4606),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    ],
    vec![BabyBear::from_canonical_u32(0x241af16d),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    BabyBear::from_canonical_u32(0x00000000),
    ],
    vec![BabyBear::from_canonical_u32(0x7290a80d),
    BabyBear::from_canonical_u32(0x6f7e5329),
    BabyBear::from_canonical_u32(0x598ec8a8),
    BabyBear::from_canonical_u32(0x76a859a0),
    BabyBear::from_canonical_u32(0x6559e868),
    BabyBear::from_canonical_u32(0x657b83af),
    BabyBear::from_canonical_u32(0x13271d3f),
    BabyBear::from_canonical_u32(0x1f876063),
    BabyBear::from_canonical_u32(0x0aeeae37),
    BabyBear::from_canonical_u32(0x706e9ca6),
    BabyBear::from_canonical_u32(0x46400cee),
    BabyBear::from_canonical_u32(0x72a05c26),
    BabyBear::from_canonical_u32(0x2c589c9e),
    BabyBear::from_canonical_u32(0x20bd37a7),
    BabyBear::from_canonical_u32(0x6a2d3d10),
    BabyBear::from_canonical_u32(0x20523767),
    ],
    vec![BabyBear::from_canonical_u32(0x5b8fe9c4),
    BabyBear::from_canonical_u32(0x2aa501d6),
    BabyBear::from_canonical_u32(0x1e01ac3e),
    BabyBear::from_canonical_u32(0x1448bc54),
    BabyBear::from_canonical_u32(0x5ce5ad1c),
    BabyBear::from_canonical_u32(0x4918a14d),
    BabyBear::from_canonical_u32(0x2c46a83f),
    BabyBear::from_canonical_u32(0x4fcf6876),
    BabyBear::from_canonical_u32(0x61d8d5c8),
    BabyBear::from_canonical_u32(0x6ddf4ff9),
    BabyBear::from_canonical_u32(0x11fda4d3),
    BabyBear::from_canonical_u32(0x02933a8f),
    BabyBear::from_canonical_u32(0x170eaf81),
    BabyBear::from_canonical_u32(0x5a9c314f),
    BabyBear::from_canonical_u32(0x49a12590),
    BabyBear::from_canonical_u32(0x35ec52a1),
    ],
    vec![BabyBear::from_canonical_u32(0x58eb1611),
    BabyBear::from_canonical_u32(0x5e481e65),
    BabyBear::from_canonical_u32(0x367125c9),
    BabyBear::from_canonical_u32(0x0eba33ba),
    BabyBear::from_canonical_u32(0x1fc28ded),
    BabyBear::from_canonical_u32(0x066399ad),
    BabyBear::from_canonical_u32(0x0cbec0ea),
    BabyBear::from_canonical_u32(0x75fd1af0),
    BabyBear::from_canonical_u32(0x50f5bf4e),
    BabyBear::from_canonical_u32(0x643d5f41),
    BabyBear::from_canonical_u32(0x6f4fe718),
    BabyBear::from_canonical_u32(0x5b3cbbde),
    BabyBear::from_canonical_u32(0x1e3afb3e),
    BabyBear::from_canonical_u32(0x296fb027),
    BabyBear::from_canonical_u32(0x45e1547b),
    BabyBear::from_canonical_u32(0x4a8db2ab),
    ],
    vec![BabyBear::from_canonical_u32(0x59986d19),
    BabyBear::from_canonical_u32(0x30bcdfa3),
    BabyBear::from_canonical_u32(0x1db63932),
    BabyBear::from_canonical_u32(0x1d7c2824),
    BabyBear::from_canonical_u32(0x53b33681),
    BabyBear::from_canonical_u32(0x0673b747),
    BabyBear::from_canonical_u32(0x038a98a3),
    BabyBear::from_canonical_u32(0x2c5bce60),
    BabyBear::from_canonical_u32(0x351979cd),
    BabyBear::from_canonical_u32(0x5008fb73),
    BabyBear::from_canonical_u32(0x547bca78),
    BabyBear::from_canonical_u32(0x711af481),
    BabyBear::from_canonical_u32(0x3f93bf64),
    BabyBear::from_canonical_u32(0x644d987b),
    BabyBear::from_canonical_u32(0x3c8bcd87),
    BabyBear::from_canonical_u32(0x608758b8),
    ],
    ];
}
}

#[cfg(test)]
mod tests2 {
    use alloc::boxed::Box;
    use alloc::collections::BTreeMap;
    use alloc::sync::Arc;
    use alloc::vec::Vec;
    use core::cell::{self, Cell};
    use std::borrow::Borrow;

    use bitcoin_script_stack::stack::{self, StackTracker, StackVariable};
    use common::{AbstractField, BabyBear, BinomialExtensionField};
    use p3_air::AirBuilder;
    use p3_field::TwoAdicField;
    use p3_matrix::Matrix;
    use primitives::field::BfField;
    use scripts::treepp::*;
    use scripts::u31_lib::{u31ext_equalverify, BabyBear4};

    use super::{Expression, FieldScriptExpression, Variable, *};
    use crate::opcode::Opcode;
    type EF = BinomialExtensionField<BabyBear, 4>;

    #[test]
    fn test_field_compiler_optimize() {
        {
            let bmap = BTreeMap::new();
            let mut stack = StackTracker::new();
            let a_value = BabyBear::two();
            let b_value = BabyBear::one();
            let c_value = BabyBear::from_canonical_u32(13232);
            let d_value = a_value + b_value;
            let e_value = d_value * c_value;
            let f_value = e_value * d_value;
            let g_value = f_value * e_value;
            let h_value = g_value * e_value;

            let a = FieldScriptExpression::from(a_value);
            let b = FieldScriptExpression::from(b_value);

            let c = FieldScriptExpression::from(c_value);
            let d = a + b;
            let d_share = d.as_expr_ptr();
            let e = FieldScriptExpression::<BabyBear>::new_mul_from_expr_ptr(
                d_share.clone(),
                c.as_expr_ptr(),
            );

            let e_share = e.as_expr_ptr();
            let f = FieldScriptExpression::<BabyBear>::new_mul_from_expr_ptr(
                e_share.clone(),
                d_share.clone(),
            );
            let g = FieldScriptExpression::<BabyBear>::new_mul_from_expr_ptr(
                e_share.clone(),
                f.as_expr_ptr(),
            );
            let h = FieldScriptExpression::<BabyBear>::new_mul_from_expr_ptr(
                g.as_expr_ptr(),
                e_share.clone(),
            );

            let equal = h.equal_for_f(h_value);
            equal.express_to_script(&mut stack, &bmap);
            let res = stack.run();
            // println!("{:?}", e_share.clone().read().unwrap().get_var());
            println!("script len {:?}", stack.get_script().len());
            assert!(res.success);
        }

        {
            let bmap = BTreeMap::new();
            let mut stack = StackTracker::new();
            let a_value = BabyBear::two();
            let b_value = BabyBear::one();
            let c_value = BabyBear::from_canonical_u32(13232);
            let d_value = a_value + b_value;
            let e_value = d_value * c_value;
            let f_value = e_value * d_value;
            let g_value = f_value * e_value;
            let h_value = g_value * e_value;

            let a = FieldScriptExpression::from(a_value);
            let b = FieldScriptExpression::from(b_value);

            let c = FieldScriptExpression::from(c_value);
            let d = a + b;
            let d_share = d.as_expr_ptr();
            let e = FieldScriptExpression::<BabyBear>::new_mul_from_expr_ptr(
                d_share.clone(),
                c.as_expr_ptr(),
            );
            let e_copy = e.to_copy().unwrap();
            let e_copy_copy = e_copy.clone().as_ref().read().unwrap().to_copy().unwrap();
            let f = FieldScriptExpression::<BabyBear>::new_mul_from_expr_ptr(
                e_copy_copy.clone(),
                d_share.clone(),
            );
            let g =
                FieldScriptExpression::<BabyBear>::new_mul_from_expr_ptr(e_copy, f.as_expr_ptr());
            let h = FieldScriptExpression::<BabyBear>::new_mul_from_expr_ptr(
                e.as_expr_ptr(),
                g.as_expr_ptr(),
            );

            let equal = h.equal_for_f(h_value);
            equal.express_to_script(&mut stack, &bmap);
            let res = stack.run();
            println!("script len {:?}", stack.get_script().len());
            assert!(res.success);
        }
    }



    #[test]
    fn test_constant_copy() {
        {
            let bmap = BTreeMap::new();
            let mut stack = StackTracker::new();
            let a_value = BabyBear::two();
            let b_value = BabyBear::one();
            let c_value = BabyBear::from_canonical_u32(13232);
            let d_value = a_value + b_value;
            let e_value = d_value * c_value;
            let f_value = e_value * d_value;
            let g_value = f_value * e_value;
            let h_value = g_value * e_value;

            let a = FieldScriptExpression::from(a_value);
            let b = FieldScriptExpression::from(b_value);

            let c = FieldScriptExpression::from(c_value);
            let d = a + b;
            let d_share = d.as_expr_ptr();
            let e = FieldScriptExpression::<BabyBear>::new_mul_from_expr_ptr(
                d_share.clone(),
                c.as_expr_ptr(),
            );

            let e_share = e.as_expr_ptr();
            let f = FieldScriptExpression::<BabyBear>::new_mul_from_expr_ptr(
                e_share.clone(),
                d_share.clone(),
            );
            let g = FieldScriptExpression::<BabyBear>::new_mul_from_expr_ptr(
                e_share.clone(),
                f.as_expr_ptr(),
            );
            let h = FieldScriptExpression::<BabyBear>::new_mul_from_expr_ptr(
                g.as_expr_ptr(),
                e_share.clone(),
            );

            let equal = h.equal_for_f(h_value);
            equal.express_to_script(&mut stack, &bmap);
            let res = stack.run();
            // println!("{:?}", e_share.clone().read().unwrap().get_var());
            println!("script len {:?}", stack.get_script().len());
            assert!(res.success);
        }

        {
            let bmap = BTreeMap::new();
            let mut stack = StackTracker::new();
            let a_value = BabyBear::two();
            let b_value = BabyBear::one();
            let c_value = BabyBear::from_canonical_u32(13232);
            let d_value = a_value + b_value;
            let e_value = d_value * c_value;
            let f_value = e_value * d_value;
            let g_value = f_value * e_value;
            let h_value = g_value * e_value;

            let a = FieldScriptExpression::from(a_value);
            let b = FieldScriptExpression::from(b_value);

            let c = FieldScriptExpression::from(c_value);
            let d = a + b;
            let d_share = d.as_expr_ptr();
            let e = FieldScriptExpression::<BabyBear>::new_mul_from_expr_ptr(
                d_share.clone(),
                c.as_expr_ptr(),
            );
            let e_copy = e.to_copy().unwrap();
            let e_copy_copy = e_copy.clone().as_ref().read().unwrap().to_copy().unwrap();
            let f = FieldScriptExpression::<BabyBear>::new_mul_from_expr_ptr(
                e_copy_copy.clone(),
                d_share.clone(),
            );
            let g =
                FieldScriptExpression::<BabyBear>::new_mul_from_expr_ptr(e_copy, f.as_expr_ptr());
            let h = FieldScriptExpression::<BabyBear>::new_mul_from_expr_ptr(
                e.as_expr_ptr(),
                g.as_expr_ptr(),
            );

            let equal = h.equal_for_f(h_value);
            equal.express_to_script(&mut stack, &bmap);
            let res = stack.run();
            println!("script len {:?}", stack.get_script().len());
            assert!(res.success);
        }
    }
}
