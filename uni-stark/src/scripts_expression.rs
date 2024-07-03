use alloc::rc::Rc;
use alloc::vec;
use alloc::vec::Vec;
use core::default;
use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use bitcoin::opcodes::OP_2DUP;
use bitcoin_script_stack::stack::{StackTracker, StackVariable};
use common::{AbstractField, AsU32Vec};
use primitives::field::BfField;
use script_primitives::*;
use scripts::treepp::*;
use scripts::u31_lib::{
    u31_add, u31_double, u31_mul, u31_neg, u31_sub, u31_sub_u31ext, u31_to_u31ext, u31ext_add,
    u31ext_add_u31, u31ext_double, u31ext_equalverify, u31ext_mul, u31ext_mul_u31,
    u31ext_mul_u31_by_constant, u31ext_sub, u31ext_sub_u31, BabyBear4, BabyBearU31,
};

use crate::symbolic_builder::get_symbolic_constraints;
use crate::symbolic_variable::SymbolicVariable;
use crate::SymbolicExpression::{self, *};

pub mod script_primitives {
    use bitcoin_script_stack::stack::{StackTracker, StackVariable};
}

#[derive(Clone, Debug)]
pub enum ScriptExpression<F: BfField> {
    Variable {
        sv: SymbolicVariable<F>,
        value: F,
        var: StackVariable,
    },
    IsFirstRow,
    IsLastRow,
    IsTransition,
    Constant(F),
    Add {
        x: Rc<Self>,
        y: Rc<Self>,
        script: Script,
        var: StackVariable,
    },
    Sub {
        x: Rc<Self>,
        y: Rc<Self>,
        script: Script,
        var: StackVariable,
    },
    Neg {
        x: Rc<Self>,
        script: Script,
        var: StackVariable,
    },
    Mul {
        x: Rc<Self>,
        y: Rc<Self>,
        script: Script,
        var: StackVariable,
    },
}

impl<F: BfField> From<&SymbolicExpression<F>> for ScriptExpression<F> {
    fn from(value: &SymbolicExpression<F>) -> Self {
        match value {
            SymbolicExpression::Variable(v) => ScriptExpression::Variable {
                sv: v.clone(),
                value: F::default(),
                var: StackVariable::null(),
            },
            SymbolicExpression::IsFirstRow => ScriptExpression::IsFirstRow,
            SymbolicExpression::IsLastRow => ScriptExpression::IsLastRow,
            SymbolicExpression::IsTransition => ScriptExpression::IsTransition,
            SymbolicExpression::Constant(f) => ScriptExpression::Constant(f.clone()),
            SymbolicExpression::Add { x, y, .. } => ScriptExpression::Add {
                x: Rc::new(ScriptExpression::from(&*x.clone())),
                y: Rc::new(ScriptExpression::from(&*y.clone())),
                script: Script::default(),
                var: StackVariable::null(),
            },
            SymbolicExpression::Sub { x, y, .. } => ScriptExpression::Sub {
                x: Rc::new(ScriptExpression::from(&*x.clone())),
                y: Rc::new(ScriptExpression::from(&*y.clone())),
                script: Script::default(),
                var: StackVariable::null(),
            },
            SymbolicExpression::Neg { x, .. } => ScriptExpression::Neg {
                x: Rc::new(ScriptExpression::from(&*x.clone())),
                script: Script::default(),
                var: StackVariable::null(),
            },
            SymbolicExpression::Mul { x, y, .. } => ScriptExpression::Mul {
                x: Rc::new(ScriptExpression::from(&*x.clone())),
                y: Rc::new(ScriptExpression::from(&*y.clone())),
                script: Script::default(),
                var: StackVariable::null(),
            },
        }
    }
}

impl<F: BfField> ScriptExpression<F> {
    fn express_to_script(&self, stack: &mut StackTracker) -> Script {
        let unity_num = |f_size| {
            if f_size == 1 {
                1
            } else {
                4
            }
        };

        match self {
            ScriptExpression::Variable { sv, value, mut var } => {
                var = stack.op_true();
            }
            ScriptExpression::IsFirstRow => {
                stack.op_true();
            }
            ScriptExpression::IsLastRow => {
                stack.op_true();
            }
            ScriptExpression::IsTransition => {
                stack.op_true();
            }
            ScriptExpression::Constant(f) => {
                let v = f.as_u32_vec();
                let length = v.len();
                for i in (0..length).rev() {
                    stack.number(v[i]);
                }
            }
            ScriptExpression::Add {
                x,
                y,
                script,
                mut var,
            } => {
                x.express_to_script(stack);
                y.express_to_script(stack);
                var = stack
                    .custom(
                        script! {
                            if F::U32_SIZE == 1{
                                {u31_add::<BabyBearU31>()}
                            }else{
                                {u31ext_add::<BabyBear4>()}
                            }
                        },
                        2 * unity_num(F::U32_SIZE),
                        true,
                        0,
                        "ScriptExpression_ADD",
                    )
                    .unwrap();
            }
            ScriptExpression::Sub {
                x,
                y,
                script,
                mut var,
            } => {
                x.express_to_script(stack);
                y.express_to_script(stack);
                var = stack
                    .custom(
                        script! {
                            if F::U32_SIZE == 1{
                                {u31_sub::<BabyBearU31>()}
                            }else{
                                {u31ext_sub::<BabyBear4>()}
                            }
                        },
                        2 * unity_num(F::U32_SIZE),
                        true,
                        0,
                        "ScriptExpression_SUB",
                    )
                    .unwrap();
            }

            ScriptExpression::Neg { x, script, mut var } => {
                x.express_to_script(stack);
                var = stack
                    .custom(
                        script! {
                            if F::U32_SIZE == 1{
                                {u31_neg::<BabyBearU31>()}
                            }else{
                                // {u31ext_neg::<BabyBear4>()}
                            }
                        },
                        1 * unity_num(F::U32_SIZE),
                        true,
                        0,
                        "ScriptExpression_NEG",
                    )
                    .unwrap();
            }
            ScriptExpression::Mul {
                x,
                y,
                script,
                mut var,
            } => {
                x.express_to_script(stack);
                y.express_to_script(stack);
                var = stack
                    .custom(
                        script! {
                            if F::U32_SIZE == 1{
                                {u31_mul::<BabyBearU31>()}
                            }else{
                                {u31ext_mul::<BabyBear4>()}
                            }
                        },
                        2 * unity_num(F::U32_SIZE),
                        true,
                        0,
                        "ScriptExpression_MUL",
                    )
                    .unwrap();
            }
        };

        stack.get_script()
    }
}

impl<F: BfField> Default for ScriptExpression<F> {
    fn default() -> Self {
        Self::Constant(F::zero())
    }
}

impl<F: BfField> From<F> for ScriptExpression<F> {
    fn from(value: F) -> Self {
        Self::Constant(value)
    }
}

impl<F: BfField> AbstractField for ScriptExpression<F> {
    type F = F;

    fn zero() -> Self {
        Self::Constant(F::zero())
    }
    fn one() -> Self {
        Self::Constant(F::one())
    }
    fn two() -> Self {
        Self::Constant(F::two())
    }
    fn neg_one() -> Self {
        Self::Constant(F::neg_one())
    }

    #[inline]
    fn from_f(f: Self::F) -> Self {
        f.into()
    }

    fn from_bool(b: bool) -> Self {
        Self::Constant(F::from_bool(b))
    }

    fn from_canonical_u8(n: u8) -> Self {
        Self::Constant(F::from_canonical_u8(n))
    }

    fn from_canonical_u16(n: u16) -> Self {
        Self::Constant(F::from_canonical_u16(n))
    }

    fn from_canonical_u32(n: u32) -> Self {
        Self::Constant(F::from_canonical_u32(n))
    }

    fn from_canonical_u64(n: u64) -> Self {
        Self::Constant(F::from_canonical_u64(n))
    }

    fn from_canonical_usize(n: usize) -> Self {
        Self::Constant(F::from_canonical_usize(n))
    }

    fn from_wrapped_u32(n: u32) -> Self {
        Self::Constant(F::from_wrapped_u32(n))
    }

    fn from_wrapped_u64(n: u64) -> Self {
        Self::Constant(F::from_wrapped_u64(n))
    }

    fn generator() -> Self {
        Self::Constant(F::generator())
    }
}

impl<F: BfField> Add for ScriptExpression<F> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Self::Add {
            x: Rc::new(self),
            y: Rc::new(rhs),
            script: Script::default(),
            var: StackVariable::null(),
        }
    }
}

impl<F: BfField> Add<F> for ScriptExpression<F> {
    type Output = Self;

    fn add(self, rhs: F) -> Self {
        self + Self::from(rhs)
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
            x: Rc::new(self),
            y: Rc::new(rhs),
            script: Script::default(),
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
            x: Rc::new(self),
            script: Script::default(),
            var: StackVariable::null(),
        }
    }
}

impl<F: BfField> Mul for ScriptExpression<F> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        #[allow(clippy::suspicious_arithmetic_impl)]
        Self::Mul {
            x: Rc::new(self),
            y: Rc::new(rhs),
            script: Script::default(),
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
    use bitcoin_script_stack::stack::StackTracker;
    use common::{AbstractField, BabyBear};
    use primitives::field::BfField;

    use super::ScriptExpression;

    #[test]
    fn test_script_expression_add() {
        let mut stack = StackTracker::new();
        let a = ScriptExpression::from(BabyBear::one());
        let b = ScriptExpression::from(BabyBear::two());
        let c = a + b;

        let d = ScriptExpression::from(BabyBear::two());
        let e = ScriptExpression::from(BabyBear::two());
        let f = d + e;

        let g = c + f; // 4 + 3 = 7
        let script = g.express_to_script(&mut stack);
        stack.number(BabyBear::from_canonical_u32(7u32).as_u32_vec()[0]);
        stack.op_equal();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_script_expression_sub() {
        let mut stack = StackTracker::new();
        let a = ScriptExpression::from(BabyBear::one());
        let b = ScriptExpression::from(BabyBear::two());
        let c = b - a; // 1

        let d = ScriptExpression::from(BabyBear::two());
        let e = ScriptExpression::from(BabyBear::from_canonical_u32(8));
        let f = e - d; // 6

        let g = f - c; // 5
        let script = g.express_to_script(&mut stack);
        stack.number(BabyBear::from_canonical_u32(5u32).as_u32_vec()[0]);
        stack.op_equal();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_script_expression_mul() {
        let mut stack = StackTracker::new();
        let a = ScriptExpression::from(BabyBear::one());
        let b = ScriptExpression::from(BabyBear::two());
        let c = b * a; // 2

        let d = ScriptExpression::from(BabyBear::two());
        let e = ScriptExpression::from(BabyBear::from_canonical_u32(8));
        let f = e * d; // 16

        let g = f * c; // 32
        let script = g.express_to_script(&mut stack);
        stack.number(BabyBear::from_canonical_u32(32u32).as_u32_vec()[0]);
        stack.op_equal();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_script_expression_neg() {
        let mut stack = StackTracker::new();
        let a = ScriptExpression::from(BabyBear::one());
        let b = -a * BabyBear::two();
        let script = b.express_to_script(&mut stack);
        stack.number(BabyBear::from_canonical_u32(BabyBear::MOD - 2).as_u32_vec()[0]);
        stack.op_equal();
        let res = stack.run();
        assert!(res.success);
    }
}
