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
            FieldScriptExpression::Equal(op) => op.to_copy(),
            _ => panic!("to_copy is only for Mul"),
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
    pub fn lookup(self, index: u32, len: usize) -> Self {
        let index = NumScriptExpression::from(index);
        Self::Lookup {
            x: Arc::new(Box::new(self)),
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
}

#[cfg(test)]
mod tests {
    use alloc::boxed::Box;
    use alloc::collections::BTreeMap;
    use alloc::sync::Arc;
    use alloc::vec::Vec;
    use core::cell::{self, Cell};

    use bitcoin_script_stack::stack::{self, StackTracker, StackVariable};
    use common::{AbstractField, BabyBear, BinomialExtensionField};
    use p3_air::AirBuilder;
    use p3_field::TwoAdicField;
    use p3_matrix::Matrix;
    use primitives::field::BfField;
    use scripts::treepp::*;
    use scripts::u31_lib::{u31_equalverify, u31ext_equalverify, BabyBear4};

    use super::{Expression, FieldScriptExpression, Variable, *};
    type EF = BinomialExtensionField<BabyBear, 4>;

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
}
