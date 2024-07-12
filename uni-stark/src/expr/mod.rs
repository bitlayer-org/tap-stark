use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::format;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::cell::Cell;
use core::fmt::Debug;
use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use bitcoin_script_stack::stack::{StackTracker, StackVariable};
use common::AbstractField;
use primitives::field::BfField;
use scripts::treepp::*;
use scripts::u31_lib::{
    u31_add, u31_mul, u31_neg, u31_sub, u31_sub_u31ext, u31ext_add, u31ext_add_u31,
    u31ext_equalverify, u31ext_mul, u31ext_mul_u31, u31ext_neg, u31ext_sub, u31ext_sub_u31,
    BabyBear4, BabyBearU31,
};

use crate::SymbolicExpression::{self, *};

mod script_builder;
pub use script_builder::*;
mod variable;
pub use variable::{ValueVariable, Variable};

pub struct Executor<F: BfField> {
    to_exec_expr: ScriptExpression<F>,
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

    fn get_var(&self) -> Option<&StackVariable>;
}

pub enum ScriptExpression<F: BfField> {
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
    Constant {
        f: F,
        debug: Cell<bool>,
        var: StackVariable,
    },
    Add {
        x: Arc<Box<dyn Expression>>,
        y: Arc<Box<dyn Expression>>,
        var: StackVariable,
        debug: Cell<bool>,
    },
    Sub {
        x: Arc<Box<dyn Expression>>,
        y: Arc<Box<dyn Expression>>,
        var: StackVariable,
        debug: Cell<bool>,
    },
    Neg {
        x: Arc<Box<dyn Expression>>,
        var: StackVariable,
        debug: Cell<bool>,
    },
    Mul {
        x: Arc<Box<dyn Expression>>,
        y: Arc<Box<dyn Expression>>,
        var: StackVariable,
        debug: Cell<bool>,
    },
    EqualVerify {
        x: Arc<Box<dyn Expression>>,
        y: Arc<Box<dyn Expression>>,
        debug: Cell<bool>,
    },
}

impl<F: BfField> ScriptExpression<F> {
    pub fn add_ext<EF: BfField>(&self, rhs: ScriptExpression<EF>) -> ScriptExpression<EF> {
        assert_eq!(F::U32_SIZE, 1);
        assert_eq!(EF::U32_SIZE, 4);
        ScriptExpression::<EF>::Add {
            x: Arc::new(Box::new(self.clone())),
            y: Arc::new(Box::new(rhs)),
            var: StackVariable::null(),
            debug: Cell::new(false),
        }
    }

    pub fn add_base<Base: BfField>(&self, rhs: ScriptExpression<Base>) -> Self {
        assert_eq!(F::U32_SIZE, 4);
        assert_eq!(Base::U32_SIZE, 1);
        ScriptExpression::Add {
            x: Arc::new(Box::new(self.clone())),
            y: Arc::new(Box::new(rhs)),
            var: StackVariable::null(),
            debug: Cell::new(false),
        }
    }

    pub fn mul_ext<EF: BfField>(&self, rhs: ScriptExpression<EF>) -> ScriptExpression<EF> {
        assert_eq!(F::U32_SIZE, 1);
        assert_eq!(EF::U32_SIZE, 4);
        ScriptExpression::<EF>::Mul {
            x: Arc::new(Box::new(self.clone())),
            y: Arc::new(Box::new(rhs)),
            var: StackVariable::null(),
            debug: Cell::new(false),
        }
    }

    pub fn mul_base<Base: BfField>(&self, rhs: ScriptExpression<Base>) -> Self {
        assert_eq!(F::U32_SIZE, 4);
        assert_eq!(Base::U32_SIZE, 1);
        ScriptExpression::Mul {
            x: Arc::new(Box::new(self.clone())),
            y: Arc::new(Box::new(rhs)),
            var: StackVariable::null(),
            debug: Cell::new(false),
        }
    }

    pub fn sub_ext<EF: BfField>(&self, rhs: ScriptExpression<EF>) -> ScriptExpression<EF> {
        assert_eq!(F::U32_SIZE, 1);
        assert_eq!(EF::U32_SIZE, 4);
        ScriptExpression::<EF>::Sub {
            x: Arc::new(Box::new(self.clone())),
            y: Arc::new(Box::new(rhs)),
            var: StackVariable::null(),
            debug: Cell::new(false),
        }
    }

    pub fn sub_base<Base: BfField>(&self, rhs: ScriptExpression<Base>) -> Self {
        assert_eq!(F::U32_SIZE, 4);
        assert_eq!(Base::U32_SIZE, 1);
        ScriptExpression::Sub {
            x: Arc::new(Box::new(self.clone())),
            y: Arc::new(Box::new(rhs)),
            var: StackVariable::null(),
            debug: Cell::new(false),
        }
    }

    pub fn equal_verify(&self, rhs: Self) -> Self {
        ScriptExpression::EqualVerify {
            x: Arc::new(Box::new(self.clone())),
            y: Arc::new(Box::new(rhs.clone())),
            debug: Cell::new(false),
        }
    }

    pub fn equal_verify_for_f(&self, rhs: F) -> Self {
        ScriptExpression::EqualVerify {
            x: Arc::new(Box::new(self.clone())),
            y: Arc::new(Box::new(Self::from(rhs))),
            debug: Cell::new(false),
        }
    }
}

impl<F: BfField> Expression for ScriptExpression<F> {
    fn set_debug(&self) {
        match self {
            ScriptExpression::ValueVariable { debug, .. } => {
                debug.set(true);
            }
            ScriptExpression::InputVariable { debug, .. } => {
                debug.set(true);
            }
            ScriptExpression::Constant { f, .. } => {}
            ScriptExpression::Add { debug, .. } => {
                debug.set(true);
            }
            ScriptExpression::Sub { debug, .. } => {
                debug.set(true);
            }
            ScriptExpression::Neg { debug, .. } => {
                debug.set(true);
            }
            ScriptExpression::Mul { debug, .. } => {
                debug.set(true);
            }
            ScriptExpression::EqualVerify { debug, .. } => {
                debug.set(true);
            }
        };
    }

    fn express_to_script(
        &self,
        stack: &mut StackTracker,
        input_variables: &BTreeMap<Variable, StackVariable>,
    ) -> Script {
        match self {
            ScriptExpression::ValueVariable { v, debug, mut var } => {
                let intput_var = input_variables.get(v.get_var()).unwrap();
                var = stack.copy_var(intput_var.clone());
                if debug.get() == true {
                    stack.debug();
                }
            }
            ScriptExpression::InputVariable { sv, debug, mut var } => {
                let intput_var = input_variables.get(sv).unwrap();
                var = stack.copy_var(intput_var.clone());
                if debug.get() == true {
                    stack.debug();
                }
            }
            ScriptExpression::Constant { f, mut var, debug } => {
                let v = f.as_u32_vec();
                var = stack.bignumber(v);
                if debug.get() == true {
                    stack.debug();
                }
            }
            ScriptExpression::Add {
                x,
                y,
                debug,
                mut var,
            } => {
                x.express_to_script(stack, input_variables); // F
                y.express_to_script(stack, input_variables); // EF
                if x.var_size() == y.var_size() {
                    let vars = stack
                        .custom1(
                            script! {
                                if x.var_size() == 1{
                                    {u31_add::<BabyBearU31>()}
                                }else{
                                    {u31ext_add::<BabyBear4>()}
                                }
                            },
                            2,
                            1,
                            0,
                            F::U32_SIZE as u32,
                            "ExprADD_Result",
                        )
                        .unwrap();
                    var = vars[0];
                    assert_eq!(var.size(), x.var_size() as u32);
                } else {
                    let mut script = Script::default();
                    if x.var_size() > y.var_size() {
                        script = script! {
                            {u31ext_add_u31::<BabyBear4>()}
                        };
                    } else {
                        script = script! {
                            4 OP_ROLL
                            {u31ext_add_u31::<BabyBear4>()}
                        };
                    }
                    let output_var_size = x.var_size().max(y.var_size());
                    let vars = stack
                        .custom1(
                            script,
                            2, // consumes 2 variable, one size is 4 and the other size is 1
                            1, // the output variable size is 4
                            0,
                            output_var_size,
                            "ExprADD_Result",
                        )
                        .unwrap();
                    var = vars[0];
                    assert_eq!(var.size(), output_var_size as u32);
                }
                if debug.get() == true {
                    stack.debug();
                }
            }
            ScriptExpression::Sub {
                x,
                y,
                debug,
                mut var,
            } => {
                x.express_to_script(stack, input_variables);
                y.express_to_script(stack, input_variables);
                if x.var_size() == y.var_size() {
                    let vars = stack
                        .custom1(
                            script! {
                                if F::U32_SIZE == 1{
                                    {u31_sub::<BabyBearU31>()}
                                }else{
                                    {u31ext_sub::<BabyBear4>()}
                                }
                            },
                            2,
                            1,
                            0,
                            F::U32_SIZE as u32,
                            "ExprSUB_Result",
                        )
                        .unwrap();
                    var = vars[0];
                } else {
                    let mut script = Script::default();
                    if debug.get() == true {
                        stack.debug();
                    }

                    if x.var_size() > y.var_size() {
                        script = script! {
                            {u31ext_sub_u31::<BabyBear4>()}
                        };
                    } else {
                        script = script! {
                            4 OP_ROLL
                            {u31_sub_u31ext::<BabyBear4>()}
                        };
                    }
                    let vars = stack
                        .custom1(
                            script,
                            2, // consumes 2 variable, one size is 4 and the other size is 1
                            1, // the size of output variable is 4
                            0,
                            F::U32_SIZE as u32,
                            "ExprSUB_Result",
                        )
                        .unwrap();
                    var = vars[0];
                }

                if debug.get() == true {
                    stack.debug();
                }
                assert_eq!(var.size(), F::U32_SIZE as u32);
            }
            ScriptExpression::Neg { x, debug, mut var } => {
                x.express_to_script(stack, input_variables);
                let vars = stack
                    .custom1(
                        script! {
                            if F::U32_SIZE == 1{
                                {u31_neg::<BabyBearU31>()}
                            }else{
                                {u31ext_neg::<BabyBear4>()}
                            }
                        },
                        1,
                        1,
                        0,
                        F::U32_SIZE as u32,
                        "ExprNEG_Result",
                    )
                    .unwrap();
                var = vars[0];
                if debug.get() == true {
                    stack.debug();
                }
                assert_eq!(var.size(), F::U32_SIZE as u32);
            }
            ScriptExpression::Mul {
                x,
                y,
                debug,
                mut var,
            } => {
                x.express_to_script(stack, input_variables);
                y.express_to_script(stack, input_variables);
                if x.var_size() == y.var_size() {
                    let vars = stack
                        .custom1(
                            script! {
                                if F::U32_SIZE == 1{
                                    {u31_mul::<BabyBearU31>()}
                                }else{
                                    {u31ext_mul::<BabyBear4>()}
                                }
                            },
                            2,
                            1,
                            0,
                            F::U32_SIZE as u32,
                            "ExprMUL_Result",
                        )
                        .unwrap();
                    var = vars[0];
                } else {
                    let mut script = Script::default();

                    if x.var_size() > y.var_size() {
                        script = script! {
                            {u31ext_mul_u31::<BabyBear4>()}
                        };
                    } else {
                        script = script! {
                            4 OP_ROLL
                            {u31ext_mul_u31::<BabyBear4>()}
                        };
                    }
                    let vars = stack
                        .custom1(
                            script,
                            2, // consumes 2 variable, one size is 4 and the other size is 1
                            1, // the size of output variable is 4
                            0,
                            F::U32_SIZE as u32,
                            "ExprMUL_Result",
                        )
                        .unwrap();
                    var = vars[0];
                }
                if debug.get() == true {
                    stack.debug();
                }
                assert_eq!(var.size(), F::U32_SIZE as u32);
            }
            ScriptExpression::EqualVerify { x, y, debug } => {
                x.express_to_script(stack, input_variables);
                y.express_to_script(stack, input_variables);
                assert_eq!(x.var_size(), y.var_size());
                if x.var_size() == 1 {
                    stack.op_equalverify();
                } else {
                    stack.custom(
                        u31ext_equalverify::<BabyBear4>(),
                        2,
                        false,
                        0,
                        "u31ext_equalverify",
                    );
                }
            }
        };
        stack.get_script()
    }

    fn var_size(&self) -> u32 {
        F::U32_SIZE as u32
    }

    fn get_var(&self) -> Option<&StackVariable> {
        match self {
            ScriptExpression::ValueVariable { var, .. } => Some(var),
            ScriptExpression::InputVariable { var, .. } => Some(var),
            ScriptExpression::Constant { var, .. } => Some(var),
            ScriptExpression::Add { var, .. } => Some(var),
            ScriptExpression::Sub { var, .. } => Some(var),
            ScriptExpression::Neg { var, .. } => Some(var),
            ScriptExpression::Mul { var, .. } => Some(var),
            ScriptExpression::EqualVerify { .. } => None,
        }
    }
}

impl<F: BfField> From<&SymbolicExpression<F>> for ScriptExpression<F> {
    fn from(value: &SymbolicExpression<F>) -> Self {
        match value {
            SymbolicExpression::Variable(v) => ScriptExpression::InputVariable {
                sv: v.into(),
                debug: Cell::new(false),
                var: StackVariable::null(),
            },
            SymbolicExpression::IsFirstRow => ScriptExpression::one(),
            SymbolicExpression::IsLastRow => ScriptExpression::one(),
            SymbolicExpression::IsTransition => ScriptExpression::one(),
            SymbolicExpression::Constant(f) => ScriptExpression::Constant {
                f: f.clone(),
                debug: Cell::new(false),
                var: StackVariable::null(),
            },
            SymbolicExpression::Add { x, y, .. } => ScriptExpression::Add {
                x: Arc::new(Box::new(ScriptExpression::from(&*x.clone()))),
                y: Arc::new(Box::new(ScriptExpression::from(&*y.clone()))),
                debug: Cell::new(false),
                var: StackVariable::null(),
            },
            SymbolicExpression::Sub { x, y, .. } => ScriptExpression::Sub {
                x: Arc::new(Box::new(ScriptExpression::from(&*x.clone()))),
                y: Arc::new(Box::new(ScriptExpression::from(&*y.clone()))),
                debug: Cell::new(false),
                var: StackVariable::null(),
            },
            SymbolicExpression::Neg { x, .. } => ScriptExpression::Neg {
                x: Arc::new(Box::new(ScriptExpression::from(&*x.clone()))),
                debug: Cell::new(false),
                var: StackVariable::null(),
            },
            SymbolicExpression::Mul { x, y, .. } => ScriptExpression::Mul {
                x: Arc::new(Box::new(ScriptExpression::from(&*x.clone()))),
                y: Arc::new(Box::new(ScriptExpression::from(&*y.clone()))),
                debug: Cell::new(false),
                var: StackVariable::null(),
            },
        }
    }
}

impl<F: BfField> Default for ScriptExpression<F> {
    fn default() -> Self {
        Self::zero()
    }
}

impl<F: BfField> From<F> for ScriptExpression<F> {
    fn from(value: F) -> Self {
        Self::Constant {
            f: value,
            debug: Cell::new(false),
            var: StackVariable::null(),
        }
    }
}

impl<F: BfField> Debug for ScriptExpression<F> {
    fn fmt(&self, fm: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ScriptExpression::ValueVariable { v, .. } => fm
                .debug_struct("ScriptExpression::ValueVariable")
                .field("var", v)
                .finish(),
            ScriptExpression::InputVariable { sv, .. } => fm
                .debug_struct("ScriptExpression::InputVariable")
                .field("sv", sv)
                .finish(),
            ScriptExpression::Constant { f, .. } => fm
                .debug_struct("ScriptExpression::Constant")
                .field("f", f)
                .finish(),
            ScriptExpression::Add { x, y, debug, var } => fm
                .debug_struct("ScriptExpression::Add")
                .field("variable", var)
                .finish(),
            ScriptExpression::Sub { x, y, debug, var } => fm
                .debug_struct("ScriptExpression::Sub")
                .field("variable", var)
                .finish(),
            ScriptExpression::Mul { x, y, debug, var } => fm
                .debug_struct("ScriptExpression::Mul")
                .field("variable", var)
                .finish(),
            ScriptExpression::Neg { x, debug, var } => fm
                .debug_struct("ScriptExpression::Neg")
                .field("variable", var)
                .finish(),
            ScriptExpression::EqualVerify { x, y, debug } => {
                fm.debug_struct("ScriptExpression::Equal").finish()
            }
        }
    }
}

impl<F: BfField> Clone for ScriptExpression<F> {
    fn clone(&self) -> Self {
        match self {
            ScriptExpression::ValueVariable { v, debug, var } => ScriptExpression::ValueVariable {
                v: v.clone(),
                debug: debug.clone(),
                var: var.clone(),
            },
            ScriptExpression::InputVariable { sv, debug, var } => ScriptExpression::InputVariable {
                sv: sv.clone(),
                debug: debug.clone(),
                var: var.clone(),
            },
            ScriptExpression::Constant { f, debug, var } => ScriptExpression::Constant {
                f: f.clone(),
                debug: debug.clone(),
                var: var.clone(),
            },
            ScriptExpression::Add { x, y, debug, var } => ScriptExpression::Add {
                x: x.clone(),
                y: y.clone(),
                debug: debug.clone(),
                var: var.clone(),
            },
            ScriptExpression::Mul { x, y, debug, var } => ScriptExpression::Mul {
                x: x.clone(),
                y: y.clone(),
                debug: debug.clone(),
                var: var.clone(),
            },
            ScriptExpression::Sub { x, y, debug, var } => ScriptExpression::Sub {
                x: x.clone(),
                y: y.clone(),
                debug: debug.clone(),
                var: var.clone(),
            },
            ScriptExpression::Neg { x, debug, var } => ScriptExpression::Neg {
                x: x.clone(),
                debug: debug.clone(),
                var: var.clone(),
            },
            ScriptExpression::EqualVerify { x, y, debug } => ScriptExpression::EqualVerify {
                x: x.clone(),
                y: y.clone(),
                debug: debug.clone(),
            },
        }
    }
}

impl<F: BfField> AbstractField for ScriptExpression<F> {
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

impl<F: BfField> Add<F> for ScriptExpression<F> {
    type Output = Self;

    fn add(self, rhs: F) -> Self {
        Self::Add {
            x: Arc::new(Box::new(self)),
            y: Arc::new(Box::new(Self::from(rhs))),
            debug: Cell::new(false),
            var: StackVariable::null(),
        }
        // self + Self::from(rhs)
    }
}

impl<F: BfField> Add<Self> for ScriptExpression<F> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Self::Add {
            x: Arc::new(Box::new(self)),
            y: Arc::new(Box::new(rhs)),
            debug: Cell::new(false),
            var: StackVariable::null(),
        }
    }
}

impl<F: BfField> Add<&Self> for ScriptExpression<F> {
    type Output = Self;

    fn add(self, rhs: &Self) -> Self {
        Self::Add {
            x: Arc::new(Box::new(self)),
            y: Arc::new(Box::new(rhs.clone())),
            debug: Cell::new(false),
            var: StackVariable::null(),
        }
    }
}

impl<F: BfField> AddAssign for ScriptExpression<F> {
    fn add_assign(&mut self, rhs: Self) {
        *self = self.clone() + rhs;
    }
}

impl<F: BfField> AddAssign<F> for ScriptExpression<F> {
    fn add_assign(&mut self, rhs: F) {
        *self += Self::from(rhs);
    }
}

impl<F: BfField> Sum for ScriptExpression<F> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|x, y| x + y).unwrap_or(Self::zero())
    }
}

impl<F: BfField> Sum<F> for ScriptExpression<F> {
    fn sum<I: Iterator<Item = F>>(iter: I) -> Self {
        iter.map(|x| Self::from(x)).sum()
    }
}

impl<F: BfField> Sub for ScriptExpression<F> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        Self::Sub {
            x: Arc::new(Box::new(self)),
            y: Arc::new(Box::new(rhs)),
            debug: Cell::new(false),
            var: StackVariable::null(),
        }
    }
}

impl<F: BfField> Sub<F> for ScriptExpression<F> {
    type Output = Self;

    fn sub(self, rhs: F) -> Self {
        self - Self::from(rhs)
    }
}

impl<F: BfField> SubAssign for ScriptExpression<F> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = self.clone() - rhs;
    }
}

impl<F: BfField> SubAssign<F> for ScriptExpression<F> {
    fn sub_assign(&mut self, rhs: F) {
        *self -= Self::from(rhs);
    }
}

impl<F: BfField> Neg for ScriptExpression<F> {
    type Output = Self;

    fn neg(self) -> Self {
        Self::Neg {
            x: Arc::new(Box::new(self)),
            debug: Cell::new(false),
            var: StackVariable::null(),
        }
    }
}

impl<F: BfField> Mul for ScriptExpression<F> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        #[allow(clippy::suspicious_arithmetic_impl)]
        Self::Mul {
            x: Arc::new(Box::new(self)),
            y: Arc::new(Box::new(rhs)),
            debug: Cell::new(false),
            var: StackVariable::null(),
        }
    }
}

impl<F: BfField> Mul<F> for ScriptExpression<F> {
    type Output = Self;

    fn mul(self, rhs: F) -> Self {
        self * Self::from(rhs)
    }
}

impl<F: BfField> MulAssign for ScriptExpression<F> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.clone() * rhs;
    }
}

impl<F: BfField> MulAssign<F> for ScriptExpression<F> {
    fn mul_assign(&mut self, rhs: F) {
        *self *= Self::from(rhs);
    }
}

impl<F: BfField> Product for ScriptExpression<F> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|x, y| x * y).unwrap_or(Self::one())
    }
}

impl<F: BfField> Product<F> for ScriptExpression<F> {
    fn product<I: Iterator<Item = F>>(iter: I) -> Self {
        iter.map(|x| Self::from(x)).product()
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
    use p3_matrix::Matrix;
    use primitives::field::BfField;
    use scripts::treepp::*;
    use scripts::u31_lib::{u31ext_equalverify, BabyBear4, BabyBearU31};

    use super::{Expression, ScriptExpression, Variable, *};
    use crate::{prove, verify, StarkConfig, SymbolicAirBuilder, SymbolicExpression};
    type EF = BinomialExtensionField<BabyBear, 4>;

    #[test]
    fn test_symbolic_expr_constraints() {
        let air_width: usize = 2;
        let mut builder = SymbolicAirBuilder::<BabyBear>::new(0, air_width, 0);
        let main_values = builder.main();
        let (local, next) = (main_values.row_slice(0), main_values.row_slice(1));
        let mut when_transition = builder.when_transition();
        // a' <- b
        when_transition.assert_eq(local[0], local[1]);

        // b' <- a + b
        when_transition.assert_eq(local[0] + local[1], next[1]);

        let cs = builder.constraints();
        let script_exp: Vec<ScriptExpression<BabyBear>> =
            cs.iter().map(|cons| ScriptExpression::from(cons)).collect();
    }

    #[test]
    fn test_script_expression_add() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = ScriptExpression::from(BabyBear::one());
        let b = ScriptExpression::from(BabyBear::two());
        let c = a + b;
        c.set_debug();

        let d = ScriptExpression::from(BabyBear::two());
        let e = ScriptExpression::from(BabyBear::two());
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
        let a = ScriptExpression::from(BabyBear::one());
        let b = ScriptExpression::from(EF::two());
        let c = a.add_ext(b);

        let d = ScriptExpression::from(BabyBear::two());
        let e = ScriptExpression::from(EF::two());
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
        let a = ScriptExpression::from(BabyBear::one());
        let b = ScriptExpression::from(EF::two());
        let c = a.sub_ext(b);

        let d = ScriptExpression::from(BabyBear::two());
        let e = ScriptExpression::from(EF::from_canonical_u32(4));
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
        let a = ScriptExpression::from(BabyBear::one());
        let b = ScriptExpression::from(EF::two());
        let c = ScriptExpression::<EF>::Mul {
            x: Arc::new(Box::new(a)),
            y: Arc::new(Box::new(b)),
            debug: Cell::new(false),
            var: StackVariable::null(),
        };

        let d = ScriptExpression::from(BabyBear::two());
        let e = ScriptExpression::from(EF::from_canonical_u32(4));
        let f = ScriptExpression::<EF>::Mul {
            x: Arc::new(Box::new(e)),
            y: Arc::new(Box::new(d)),
            debug: Cell::new(false),
            var: StackVariable::null(),
        };

        let g = c * f;
        let script = g.express_to_script(&mut stack, &bmap);
        stack.bignumber(EF::from_canonical_u32(16).as_u32_vec());
        stack.custom(
            u31ext_equalverify::<BabyBear4>(),
            2,
            false,
            0,
            "equal result",
        );
        stack.op_true();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_ext_constant() {
        let mut stack = StackTracker::new();
        let bmap = BTreeMap::new();
        let a = ScriptExpression::from(EF::one());
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

        let var1_wrap = ScriptExpression::InputVariable {
            sv: var1,
            debug: Cell::new(false),
            var: StackVariable::null(),
        };
        let var2_wrap = ScriptExpression::<BabyBear>::InputVariable {
            sv: var2,
            debug: Cell::new(false),
            var: StackVariable::null(),
        };
        let var3_wrap = ScriptExpression::InputVariable {
            sv: var3,
            debug: Cell::new(false),
            var: StackVariable::null(),
        };
        let var4_wrap = ScriptExpression::<BabyBear>::InputVariable {
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

        let var1_wrap = ScriptExpression::<EF>::InputVariable {
            sv: var1,
            debug: Cell::new(false),
            var: StackVariable::null(),
        };
        let var2_wrap = ScriptExpression::InputVariable {
            sv: var2,
            debug: Cell::new(false),
            var: StackVariable::null(),
        };
        let var3_wrap = ScriptExpression::InputVariable {
            sv: var3,
            debug: Cell::new(false),
            var: StackVariable::null(),
        };
        let var4_wrap = ScriptExpression::InputVariable {
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
        let a = ScriptExpression::from(EF::one());
        let b = ScriptExpression::from(EF::two());
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
        let a = ScriptExpression::from(BabyBear::one());
        let b = ScriptExpression::from(BabyBear::two());
        let c = b - a; // 1

        let d = ScriptExpression::from(BabyBear::two());
        let e = ScriptExpression::from(BabyBear::from_canonical_u32(8));
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
        let a = ScriptExpression::from(EF::one());
        let b = ScriptExpression::from(EF::two());
        let c = b - a; // 1

        let d = ScriptExpression::from(EF::two());
        let e = ScriptExpression::from(EF::from_canonical_u32(8));
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
        let a = ScriptExpression::from(BabyBear::one());
        let b = ScriptExpression::from(BabyBear::two());
        let c = b * a; // 2

        let d = ScriptExpression::from(BabyBear::two());
        let e = ScriptExpression::from(BabyBear::from_canonical_u32(8));
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
        let a = ScriptExpression::from(EF::one());
        let b = ScriptExpression::from(EF::two());
        let c = b * a; // 2

        let d = ScriptExpression::from(EF::two());
        let e = ScriptExpression::from(EF::from_canonical_u32(8));
        let f = e * d; // 16
        let g = f * c; // 32
        let script = g.express_to_script(&mut stack, &bmap);

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
        let a = ScriptExpression::from(BabyBear::one());
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
        let a = ScriptExpression::from(EF::one());
        let b = -a * EF::two();
        let script = b.express_to_script(&mut stack, &bmap);
        stack.bignumber(EF::from_canonical_u32(EF::MOD - 2).as_u32_vec());
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
}
