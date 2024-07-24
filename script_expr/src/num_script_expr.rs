use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use alloc::vec::Vec;
use alloc::{format, vec};
use core::cell::Cell;
use core::fmt::Debug;
use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use bitcoin_script_stack::stack::{StackTracker, StackVariable};
use primitives::field::BfField;
use scripts::treepp::*;

use super::variable::{ValueVariable, Variable};
use super::{Expression, FieldScriptExpression};
use crate::script_helper::{reverse_bits_len_script_with_input, value_to_bits_format};

pub enum NumScriptExpression {
    InputVariable {
        sv: Variable,
        debug: Cell<bool>,
        var: StackVariable,
    },
    Constant {
        values: Vec<u32>,
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
    Equal {
        x: Arc<Box<dyn Expression>>,
        y: Arc<Box<dyn Expression>>,
        debug: Cell<bool>,
        var: StackVariable,
    },
    Double {
        x: Arc<Box<dyn Expression>>,
        debug: Cell<bool>,
        var: StackVariable,
    },
    Square {
        x: Arc<Box<dyn Expression>>,
        debug: Cell<bool>,
        var: StackVariable,
    },
    ToBits {
        x: Arc<Box<dyn Expression>>,
        debug: Cell<bool>,
        var: StackVariable,
        bits_len: u32,
    },
    ToBitsVec {
        x: Arc<Box<dyn Expression>>,
        debug: Cell<bool>,
        var: Vec<StackVariable>,
        bits_len: u32,
    },
    BitReverse {
        x: Arc<Box<dyn Expression>>,
        debug: Cell<bool>,
        var: StackVariable,
        bits_len: u32,
    },
    // Exp{
    //     x: Arc<Box<dyn Expression>>,
    //     y: Arc<Box<dyn Expression>>,
    //     var: StackVariable,
    //     debug: Cell<bool>,
    // },
}

impl NumScriptExpression {
    pub fn zero() -> Self {
        Self::from(0u32)
    }

    pub fn one() -> Self {
        Self::from(1u32)
    }

    pub fn two() -> Self {
        Self::from(2u32)
    }

    pub fn euqal_verify(&self, rhs: NumScriptExpression) -> Self {
        Self::EqualVerify {
            x: Arc::new(Box::new(self.clone())),
            y: Arc::new(Box::new(rhs)),
            debug: Cell::new(false),
        }
    }

    pub fn euqal(&self, rhs: NumScriptExpression) -> Self {
        Self::Equal {
            x: Arc::new(Box::new(self.clone())),
            y: Arc::new(Box::new(rhs)),
            debug: Cell::new(false),
            var: StackVariable::null(),
        }
    }

    pub fn to_bits(&self) -> Self {
        Self::ToBits {
            x: Arc::new(Box::new(self.clone())),
            debug: Cell::new(false),
            var: StackVariable::null(),
            bits_len: 32,
        }
    }

    pub fn to_custom_bits(&self, bits_len: u32) -> Self {
        Self::ToBits {
            x: Arc::new(Box::new(self.clone())),
            debug: Cell::new(false),
            var: StackVariable::null(),
            bits_len: bits_len,
        }
    }

    pub fn num_to_field<F: BfField>(&self) -> FieldScriptExpression<F> {
        FieldScriptExpression::NumToField {
            x: Arc::new(Box::new(self.clone())),
            debug: Cell::new(false),
            var: StackVariable::null(),
        }
    }

    pub fn index_to_rou<F: BfField>(self, sub_group_bits: u32) -> FieldScriptExpression<F> {
        FieldScriptExpression::<F>::num_index_to_rou(self, sub_group_bits)
    }

    pub fn debug(self) -> Self {
        self.set_debug();
        self
    }
}

impl Expression for NumScriptExpression {
    fn as_share_ptr(self) -> Arc<Box<dyn Expression>>{
        Arc::new(Box::new(self))
    }
    
    fn set_debug(&self) {
        match self {
            NumScriptExpression::InputVariable { debug, .. } => {
                debug.set(true);
            }
            NumScriptExpression::Constant { debug, .. } => debug.set(true),
            NumScriptExpression::Add { debug, .. } => {
                debug.set(true);
            }
            NumScriptExpression::Sub { debug, .. } => {
                debug.set(true);
            }
            NumScriptExpression::Neg { debug, .. } => {
                debug.set(true);
            }
            NumScriptExpression::Mul { debug, .. } => {
                debug.set(true);
            }
            NumScriptExpression::EqualVerify { debug, .. } => {
                debug.set(true);
            }
            NumScriptExpression::Equal { debug, .. } => {
                debug.set(true);
            }
            NumScriptExpression::Double { debug, .. } => {
                debug.set(true);
            }
            NumScriptExpression::Square { debug, .. } => {
                debug.set(true);
            }
            NumScriptExpression::ToBits { debug, .. } => {
                debug.set(true);
            }
            NumScriptExpression::ToBitsVec { debug, .. } => {
                debug.set(true);
            }
            NumScriptExpression::BitReverse { debug, .. } => {
                debug.set(true);
            }
        };
    }

    fn express_to_script(
        &self,
        stack: &mut StackTracker,
        input_variables: &BTreeMap<Variable, StackVariable>,
    )  {
        match self {
            NumScriptExpression::InputVariable { sv, debug, mut var } => {
                let intput_var = input_variables.get(sv).unwrap();
                var = stack.copy_var(intput_var.clone());
                if debug.get() == true {
                    stack.debug();
                }
                if sv.get_var_size().is_some() {
                    assert_eq!(var.size(), sv.get_var_size().unwrap());
                }
            }
            NumScriptExpression::Constant {
                values,
                mut var,
                debug,
            } => {
                var = stack.bignumber(values.clone());
                if debug.get() == true {
                    stack.debug();
                }
            }
            NumScriptExpression::Add {
                x,
                y,
                debug,
                mut var,
            } => {
                assert_eq!(x.var_size(), 1);
                assert_eq!(y.var_size(), 1);
                x.express_to_script(stack, input_variables); // F
                y.express_to_script(stack, input_variables); // EF

                var = stack.op_add(); // Bitcoin OP_ADD

                if debug.get() == true {
                    stack.debug();
                }
            }
            NumScriptExpression::Sub {
                x,
                y,
                debug,
                mut var,
            } => {
                x.express_to_script(stack, input_variables); // F
                y.express_to_script(stack, input_variables); // EF
                assert_eq!(x.var_size(), 1);
                assert_eq!(y.var_size(), 1);

                var = stack.op_sub();

                if debug.get() == true {
                    stack.debug();
                }
            }
            NumScriptExpression::Neg { x, debug, mut var } => {
                x.express_to_script(stack, input_variables); // F
                assert_eq!(x.var_size(), 1);

                var = stack.op_negate();

                if debug.get() == true {
                    stack.debug();
                }
            }
            NumScriptExpression::Mul {
                x,
                y,
                debug,
                mut var,
            } => {
                // todo: support mul
                assert_eq!(0, 1);
            }
            NumScriptExpression::EqualVerify { x, y, debug } => {
                x.express_to_script(stack, input_variables); // F
                y.express_to_script(stack, input_variables); // EF
                assert_eq!(x.var_size(), 1);
                assert_eq!(y.var_size(), 1);

                stack.op_equalverify();

                if debug.get() == true {
                    stack.debug();
                }
            }
            NumScriptExpression::Equal {
                x,
                y,
                debug,
                mut var,
            } => {
                assert_eq!(x.var_size(), 1);
                assert_eq!(y.var_size(), 1);
                x.express_to_script(stack, input_variables); // F
                y.express_to_script(stack, input_variables); // EF

                var = stack.op_equal();

                if debug.get() == true {
                    stack.debug();
                }
            }
            NumScriptExpression::Double { x, debug, mut var } => {
                assert_eq!(x.var_size(), 1);
                x.express_to_script(stack, input_variables); // F
                stack.copy_var(x.get_var().unwrap()[0].clone());
                stack.op_add();

                if debug.get() == true {
                    stack.debug();
                }
            }
            NumScriptExpression::Square { x, debug, mut var } => {
                x.express_to_script(stack, input_variables); // F
                assert_eq!(x.var_size(), 1);
                // todo: support square
                assert_eq!(0, 1);
                // var = stack.op_negate();

                if debug.get() == true {
                    stack.debug();
                }
            }
            NumScriptExpression::ToBits {
                x,
                debug,
                mut var,
                bits_len,
            } => {
                x.express_to_script(stack, input_variables); // F
                assert_eq!(x.var_size(), 1);
                let vars = stack
                    .custom1(
                        value_to_bits_format(*bits_len),
                        x.var_size(),
                        1,
                        0,
                        *bits_len,
                        "NumExpr::ToBits",
                    )
                    .unwrap();
                var = vars[0];

                if debug.get() == true {
                    stack.debug();
                }
            }
            NumScriptExpression::ToBitsVec { x, debug, .. } => {
                // todo: support ToBitsVec
                assert_eq!(1, 2);
                // var = stack.custom1(value_to_bits_format(*bits_len), x.var_size(), *bits_len, 0, 1, "NumExpr::ToBitsVec").unwrap();
            }
            NumScriptExpression::BitReverse {
                x,
                debug,
                mut var,
                bits_len,
            } => {
                x.express_to_script(stack, input_variables); // F
                assert_eq!(2, 1);

                // if debug.get() == true {
                //     stack.debug();
                // }
            }
        };
    }

    fn var_size(&self) -> u32 {
        match self {
            NumScriptExpression::ToBits { bits_len, .. } => *bits_len,
            NumScriptExpression::ToBitsVec { .. } => 1,
            _ => 1,
        }
    }

    fn get_var(&self) -> Option<Vec<StackVariable>> {
        match self {
            NumScriptExpression::InputVariable { var, .. } => Some(vec![*var]),
            NumScriptExpression::Constant { var, .. } => Some(vec![*var]),
            NumScriptExpression::Add { var, .. } => Some(vec![*var]),
            NumScriptExpression::Sub { var, .. } => Some(vec![*var]),
            NumScriptExpression::Neg { var, .. } => Some(vec![*var]),
            NumScriptExpression::Mul { var, .. } => Some(vec![*var]),
            NumScriptExpression::EqualVerify { .. } => None,
            NumScriptExpression::Equal { var, .. } => Some(vec![*var]),
            NumScriptExpression::Double { var, .. } => Some(vec![*var]),
            NumScriptExpression::Square { var, .. } => Some(vec![*var]),
            NumScriptExpression::ToBits { var, .. } => Some(vec![*var]),
            NumScriptExpression::ToBitsVec { var, .. } => {
                Some(var.clone())
            }
            NumScriptExpression::BitReverse { var, .. } => Some(vec![*var]),
        }
    }
}

impl Default for NumScriptExpression {
    fn default() -> Self {
        Self::zero()
    }
}

impl From<u32> for NumScriptExpression {
    fn from(value: u32) -> Self {
        Self::Constant {
            values: vec![value],
            debug: Cell::new(false),
            var: StackVariable::null(),
        }
    }
}

impl From<Vec<u32>> for NumScriptExpression {
    fn from(values: Vec<u32>) -> Self {
        Self::Constant {
            values,
            debug: Cell::new(false),
            var: StackVariable::null(),
        }
    }
}

impl Debug for NumScriptExpression {
    fn fmt(&self, fm: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            NumScriptExpression::InputVariable { sv, .. } => fm
                .debug_struct("ScriptExpression::InputVariable")
                .field("sv", sv)
                .finish(),
            NumScriptExpression::Constant { values, .. } => fm
                .debug_struct("ScriptExpression::Constant")
                .field("f", values)
                .finish(),
            NumScriptExpression::Add { x, y, debug, var } => fm
                .debug_struct("ScriptExpression::Add")
                .field("variable", var)
                .finish(),
            NumScriptExpression::Sub { x, y, debug, var } => fm
                .debug_struct("ScriptExpression::Sub")
                .field("variable", var)
                .finish(),
            NumScriptExpression::Mul { x, y, debug, var } => fm
                .debug_struct("ScriptExpression::Mul")
                .field("variable", var)
                .finish(),
            NumScriptExpression::Neg { x, debug, var } => fm
                .debug_struct("ScriptExpression::Neg")
                .field("variable", var)
                .finish(),
            NumScriptExpression::EqualVerify { x, y, debug } => {
                fm.debug_struct("ScriptExpression::EqualVerify").finish()
            }
            NumScriptExpression::Equal { x, y, debug, var } => fm
                .debug_struct("ScriptExpression::Equal")
                .field("variable", var)
                .finish(),
            NumScriptExpression::Double { x, debug, var } => fm
                .debug_struct("ScriptExpression::Double")
                .field("variable", var)
                .finish(),
            NumScriptExpression::Square { x, debug, var } => fm
                .debug_struct("ScriptExpression::Square")
                .field("variable", var)
                .finish(),
            NumScriptExpression::ToBits { x, debug, var, .. } => fm
                .debug_struct("ScriptExpression::ToBits")
                .field("variable", var)
                .finish(),
            NumScriptExpression::ToBitsVec { x, debug, var, .. } => fm
                .debug_struct("ScriptExpression::ToBits")
                .field("variable", var)
                .finish(),
            NumScriptExpression::BitReverse { x, debug, var, .. } => fm
                .debug_struct("ScriptExpression::ToBits")
                .field("variable", var)
                .finish(),
        }
    }
}

impl Clone for NumScriptExpression {
    fn clone(&self) -> Self {
        match self {
            NumScriptExpression::InputVariable { sv, debug, var } => {
                NumScriptExpression::InputVariable {
                    sv: sv.clone(),
                    debug: debug.clone(),
                    var: var.clone(),
                }
            }
            NumScriptExpression::Constant { values, debug, var } => NumScriptExpression::Constant {
                values: values.clone(),
                debug: debug.clone(),
                var: var.clone(),
            },
            NumScriptExpression::Add { x, y, debug, var } => NumScriptExpression::Add {
                x: x.clone(),
                y: y.clone(),
                debug: debug.clone(),
                var: var.clone(),
            },
            NumScriptExpression::Mul { x, y, debug, var } => NumScriptExpression::Mul {
                x: x.clone(),
                y: y.clone(),
                debug: debug.clone(),
                var: var.clone(),
            },
            NumScriptExpression::Sub { x, y, debug, var } => NumScriptExpression::Sub {
                x: x.clone(),
                y: y.clone(),
                debug: debug.clone(),
                var: var.clone(),
            },
            NumScriptExpression::Neg { x, debug, var } => NumScriptExpression::Neg {
                x: x.clone(),
                debug: debug.clone(),
                var: var.clone(),
            },
            NumScriptExpression::EqualVerify { x, y, debug } => NumScriptExpression::EqualVerify {
                x: x.clone(),
                y: y.clone(),
                debug: debug.clone(),
            },
            NumScriptExpression::Equal { x, y, debug, var } => NumScriptExpression::Equal {
                x: x.clone(),
                y: y.clone(),
                debug: debug.clone(),
                var: var.clone(),
            },
            NumScriptExpression::Double { x, debug, var } => NumScriptExpression::Double {
                x: x.clone(),
                debug: debug.clone(),
                var: var.clone(),
            },
            NumScriptExpression::Square { x, debug, var } => NumScriptExpression::Square {
                x: x.clone(),
                debug: debug.clone(),
                var: var.clone(),
            },
            NumScriptExpression::ToBits {
                x,
                debug,
                var,
                bits_len,
            } => NumScriptExpression::ToBits {
                x: x.clone(),
                debug: debug.clone(),
                var: var.clone(),
                bits_len: *bits_len,
            },
            NumScriptExpression::ToBitsVec {
                x,
                debug,
                var,
                bits_len,
            } => NumScriptExpression::ToBitsVec {
                x: x.clone(),
                debug: debug.clone(),
                var: var.clone(),
                bits_len: *bits_len,
            },
            NumScriptExpression::BitReverse {
                x,
                debug,
                var,
                bits_len,
            } => NumScriptExpression::BitReverse {
                x: x.clone(),
                debug: debug.clone(),
                var: var.clone(),
                bits_len: *bits_len,
            },
        }
    }
}

impl Add<Self> for NumScriptExpression {
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

impl Add<&Self> for NumScriptExpression {
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

impl AddAssign for NumScriptExpression {
    fn add_assign(&mut self, rhs: Self) {
        *self = self.clone() + rhs;
    }
}

impl AddAssign<u32> for NumScriptExpression {
    fn add_assign(&mut self, rhs: u32) {
        *self += Self::from(rhs);
    }
}

impl AddAssign<Vec<u32>> for NumScriptExpression {
    fn add_assign(&mut self, rhs: Vec<u32>) {
        *self += Self::from(rhs);
    }
}

impl Sum for NumScriptExpression {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|x, y| x + y).unwrap_or(Self::zero())
    }
}

impl Sum<u32> for NumScriptExpression {
    fn sum<I: Iterator<Item = u32>>(iter: I) -> Self {
        iter.map(|x| Self::from(x)).sum()
    }
}

impl Sub for NumScriptExpression {
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

impl Sub<u32> for NumScriptExpression {
    type Output = Self;

    fn sub(self, rhs: u32) -> Self {
        self - Self::from(rhs)
    }
}

impl SubAssign for NumScriptExpression {
    fn sub_assign(&mut self, rhs: Self) {
        *self = self.clone() - rhs;
    }
}

impl SubAssign<u32> for NumScriptExpression {
    fn sub_assign(&mut self, rhs: u32) {
        *self -= Self::from(rhs);
    }
}

impl Neg for NumScriptExpression {
    type Output = Self;

    fn neg(self) -> Self {
        Self::Neg {
            x: Arc::new(Box::new(self)),
            debug: Cell::new(false),
            var: StackVariable::null(),
        }
    }
}

impl Mul for NumScriptExpression {
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

impl Mul<u32> for NumScriptExpression {
    type Output = Self;

    fn mul(self, rhs: u32) -> Self {
        self * Self::from(rhs)
    }
}

impl MulAssign for NumScriptExpression {
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.clone() * rhs;
    }
}

impl MulAssign<u32> for NumScriptExpression {
    fn mul_assign(&mut self, rhs: u32) {
        *self *= Self::from(rhs);
    }
}

impl Product for NumScriptExpression {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|x, y| x * y).unwrap_or(Self::one())
    }
}

impl Product<u32> for NumScriptExpression {
    fn product<I: Iterator<Item = u32>>(iter: I) -> Self {
        iter.map(|x| Self::from(x)).product()
    }
}

#[cfg(test)]
mod tests {
    use alloc::collections::BTreeMap;
    use core::cell::{self, Cell};

    use bitcoin_script_stack::stack::{StackTracker, StackVariable};
    use scripts::treepp::*;

    use super::{Expression, NumScriptExpression, Variable, *};

    #[test]
    fn test_script_expression_add() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = NumScriptExpression::from(1);
        let b = NumScriptExpression::from(2);
        let c = a + b;
        c.set_debug();

        let d = NumScriptExpression::from(2);
        let e = NumScriptExpression::from(2);
        let f = d + e;

        let g: NumScriptExpression = c + f; // 4 + 3 = 7
        let h = g.euqal(NumScriptExpression::from(7));
        let script = h.express_to_script(&mut stack, &bmap);
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
        bmap.insert(var1, stack.var(1, script! { 1 }, "input 1"));
        bmap.insert(var2, stack.var(1, script! { 2}, "input 2"));
        bmap.insert(var3, stack.var(1, script! {3}, "input 3"));
        bmap.insert(var4, stack.var(1, script! {4}, "input 4"));

        let var1_wrap = NumScriptExpression::InputVariable {
            sv: var1,
            debug: Cell::new(false),
            var: StackVariable::null(),
        };
        let var2_wrap = NumScriptExpression::InputVariable {
            sv: var2,
            debug: Cell::new(false),
            var: StackVariable::null(),
        };
        let var3_wrap = NumScriptExpression::InputVariable {
            sv: var3,
            debug: Cell::new(false),
            var: StackVariable::null(),
        };
        let var4_wrap = NumScriptExpression::InputVariable {
            sv: var4,
            debug: Cell::new(false),
            var: StackVariable::null(),
        };
        let res1 = var1_wrap + var2_wrap;
        let res2 = var3_wrap + var4_wrap;

        let res = res1 + res2;
        res.express_to_script(&mut stack, &bmap);

        stack.number(10);
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
    fn test_script_expression_sub() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = NumScriptExpression::from(1);
        let b = NumScriptExpression::from(2);
        let c = b - a; // 1

        let d = NumScriptExpression::from(2);
        let e = NumScriptExpression::from(8);
        let f = e - d; // 6

        let g = f - c; // 5
        let script = g.express_to_script(&mut stack, &bmap);
        stack.number(5);
        stack.op_equal();
        let res = stack.run();
        assert!(res.success);
    }

    // #[test]
    // fn test_script_expression_mul() {
    //     let bmap = BTreeMap::new();
    //     let mut stack = StackTracker::new();
    //     let a = NumScriptExpression::from(BabyBear::one());
    //     let b = NumScriptExpression::from(BabyBear::two());
    //     let c = b * a; // 2

    //     let d = NumScriptExpression::from(BabyBear::two());
    //     let e = NumScriptExpression::from(BabyBear::from_canonical_u32(8));
    //     let f = e * d * BabyBear::one(); // 16
    //     stack.show_stack();
    //     let g = f * c; // 32
    //     let script = g.express_to_script(&mut stack, &bmap);
    //     stack.number(BabyBear::from_canonical_u32(32u32).as_u32_vec()[0]);
    //     stack.op_equal();
    //     let res = stack.run();
    //     assert!(res.success);
    // }

    #[test]
    fn test_script_expression_neg() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = NumScriptExpression::from(1);
        let b = -a + NumScriptExpression::two();
        let script = b.express_to_script(&mut stack, &bmap);
        stack.number(1);
        stack.op_equal();
        let res = stack.run();
        assert!(res.success);
    }
}
