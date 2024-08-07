use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use alloc::vec::Vec;
use alloc::{format, vec};
use core::cell::Cell;
use core::fmt::Debug;
use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use std::any::{Any, TypeId};
use std::sync::RwLock;

use bitcoin::opcodes::{OP_FROMALTSTACK, OP_MUL, OP_TOALTSTACK};
use bitcoin_script_stack::stack::{StackTracker, StackVariable};
use common::BinomialExtensionField;
use p3_baby_bear::BabyBear;
use p3_challenger::{CanObserve, CanSample};
use p3_field::{AbstractExtensionField, AbstractField, Field};
use p3_symmetric::CryptographicPermutation;
use primitives::challenger::chan_field::{PermutationField, U32};
use primitives::challenger::BitExtractor;
use primitives::field::BfField;
use scripts::blake3::{blake3, blake3_var_length};
use scripts::pseudo::{OP_4DROP, OP_4FROMALTSTACK, OP_4ROLL, OP_4TOALTSTACK};
use scripts::treepp::*;
use scripts::u31_lib::{u31_add, u31_mul, u32_to_u31, BabyBearU31};
use scripts::u32_std::u32_compress;

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
    Blake3Perm {
        x: Vec<Arc<Box<dyn Expression>>>,
        debug: Cell<bool>,
        var: StackVariable,
    },
    ToSample {
        x: Arc<Box<dyn Expression>>,
        debug: Cell<bool>,
        var: StackVariable,
    },
    SampleF {
        x: Arc<Box<dyn Expression>>,
        debug: Cell<bool>,
        var: StackVariable,
    },
    SampleEF {
        x: Arc<Box<dyn Expression>>,
        debug: Cell<bool>,
        var: StackVariable,
    }, // Exp{
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

    pub fn blake3(state: &[Self]) -> Self {
        let state = state
            .iter()
            .map(|x| Arc::new(Box::new(x.clone()) as Box<_>))
            .collect::<Vec<_>>();
        Self::Blake3Perm {
            x: state,
            debug: Cell::new(false),
            var: StackVariable::null(),
        }
    }
    pub fn to_sample(&self) -> Self {
        Self::ToSample {
            x: Arc::new(Box::new(self.clone())),
            debug: Cell::new(false),
            var: StackVariable::null(),
        }
    }
    pub fn sample_f(&self) -> Self {
        Self::SampleF {
            x: Arc::new(Box::new(self.clone())),
            debug: Cell::new(false),
            var: StackVariable::null(),
        }
    }
    pub fn sample_ef(&self) -> Self {
        Self::SampleEF {
            x: Arc::new(Box::new(self.clone())),
            debug: Cell::new(false),
            var: StackVariable::null(),
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
    fn as_expr_ptr(self) -> Arc<RwLock<Box<dyn Expression>>> {
        Arc::new(RwLock::new(Box::new(self)))
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
            NumScriptExpression::Blake3Perm { debug, .. } => {
                debug.set(true);
            }
            NumScriptExpression::ToSample { debug, .. } => {
                debug.set(true);
            }
            NumScriptExpression::SampleF { debug, .. } => {
                debug.set(true);
            }
            NumScriptExpression::SampleEF { debug, .. } => {
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
            NumScriptExpression::InputVariable { sv, debug, mut var } => {
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
            NumScriptExpression::Constant {
                values,
                mut var,
                debug,
            } => {
                var = stack.bignumber(values.clone());
                if debug.get() == true {
                    stack.debug();
                }
                vec![var]
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
                vec![var]
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
                vec![var]
            }
            NumScriptExpression::Neg { x, debug, mut var } => {
                x.express_to_script(stack, input_variables); // F
                assert_eq!(x.var_size(), 1);

                var = stack.op_negate();

                if debug.get() == true {
                    stack.debug();
                }
                vec![var]
            }
            NumScriptExpression::Mul {
                x,
                y,
                debug,
                mut var,
            } => {
                // todo: support mul
                assert_eq!(0, 1);
                vec![]
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
                vec![]
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
                vec![var]
            }
            NumScriptExpression::Double { x, debug, mut var } => {
                assert_eq!(x.var_size(), 1);
                let vars = x.express_to_script(stack, input_variables); // F
                stack.copy_var(vars[0]);
                let var = stack.op_add();

                if debug.get() == true {
                    stack.debug();
                }
                vec![var]
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
                vec![]
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

                if debug.get() == true {
                    stack.debug();
                }
                vars
            }
            NumScriptExpression::ToBitsVec { x, debug, .. } => {
                // todo: support ToBitsVec
                assert_eq!(1, 2);
                // var = stack.custom1(value_to_bits_format(*bits_len), x.var_size(), *bits_len, 0, 1, "NumExpr::ToBitsVec").unwrap();
                vec![]
            }
            NumScriptExpression::Blake3Perm { x, debug, mut var } => {
                for i in x.iter().rev() {
                    i.express_to_script(stack, input_variables);
                }
                stack.debug();
                let vars = stack
                    .custom1(
                        script! {
                            {blake3()}
                            for i in 0..7{
                                {(i+1)*4} OP_4ROLL
                            }
                        },
                        64,
                        32,
                        0,
                        1,
                        "ExprBlake3Perm_Result",
                    )
                    .unwrap();
                vars
            }
            NumScriptExpression::ToSample { x, debug, mut var } => {
                //input 32 u8  => output 8 babybear
                x.express_to_script(stack, input_variables);
                stack.debug();
                let vars = stack
                    .custom1(
                        script! {
                            for _ in 0..8 {
                                {u32_compress()}
                                {u32_to_u31()}
                                OP_TOALTSTACK
                            }
                            for _ in 0..8 {
                                OP_FROMALTSTACK
                            }
                            for i in 0..7{
                                {i+1} OP_ROLL
                            }
                        },
                        32 as u32,
                        8,
                        0,
                        1,
                        "ExprToF_Result",
                    )
                    .unwrap();
                vars
            }
            NumScriptExpression::SampleF { x, debug, mut var } => {
                x.express_to_script(stack, input_variables);
                println!("before sample f");
                stack.debug();
                let vars = stack
                    .custom1(
                        script! {
                            OP_TOALTSTACK
                            for _ in 0..7 {
                                OP_DROP
                            }
                            OP_FROMALTSTACK
                        },
                        8 as u32,
                        1,
                        0,
                        1,
                        "ExprSampleF_Result",
                    )
                    .unwrap();
                vars
            }
            NumScriptExpression::SampleEF { x, debug, mut var } => {
                x.express_to_script(stack, input_variables);
                stack.debug();
                let vars = stack
                    .custom1(
                        script! {
                            OP_4TOALTSTACK
                            OP_4DROP
                            OP_4FROMALTSTACK
                        },
                        8 as u32,
                        1,
                        0,
                        4,
                        "ExprSampleEF_Result",
                    )
                    .unwrap();
                vars
            }
        }
    }

    fn var_size(&self) -> u32 {
        match self {
            NumScriptExpression::ToBits { bits_len, .. } => *bits_len,
            NumScriptExpression::ToBitsVec { .. } => 1,
            _ => 1,
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
            NumScriptExpression::Blake3Perm { x, debug, var, .. } => fm
                .debug_struct("ScriptExpression::Blake3Perm")
                .field("variable", var)
                .finish(),
            NumScriptExpression::ToSample { x, debug, var, .. } => fm
                .debug_struct("ScriptExpression::Blake3Perm")
                .field("variable", var)
                .finish(),
            NumScriptExpression::SampleF { x, debug, var, .. } => fm
                .debug_struct("ScriptExpression::Blake3Perm")
                .field("variable", var)
                .finish(),
            NumScriptExpression::SampleEF { x, debug, var, .. } => fm
                .debug_struct("ScriptExpression::Blake3Perm")
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
            NumScriptExpression::Blake3Perm { x, debug, var } => NumScriptExpression::Blake3Perm {
                x: x.clone(),
                debug: debug.clone(),
                var: var.clone(),
            },
            NumScriptExpression::ToSample { x, debug, var } => NumScriptExpression::ToSample {
                x: x.clone(),
                debug: debug.clone(),
                var: var.clone(),
            },
            NumScriptExpression::SampleF { x, debug, var } => NumScriptExpression::SampleF {
                x: x.clone(),
                debug: debug.clone(),
                var: var.clone(),
            },
            NumScriptExpression::SampleEF { x, debug, var } => NumScriptExpression::SampleEF {
                x: x.clone(),
                debug: debug.clone(),
                var: var.clone(),
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

// BASE is the base field of F when F is a extension field
// And BASE is exactly same with F when F is a prime field
#[derive(Clone, Debug)]
pub struct BfChallengerExpr<F, const WIDTH: usize>
where
    F: BfField + BitExtractor,
{
    sponge_state: Vec<NumScriptExpression>,
    input_buffer: Vec<NumScriptExpression>,
    output_buffer: Vec<NumScriptExpression>,

    pub grind_bits: Option<usize>,
    pub grind_output: F,
    pub sample_input: Vec<Vec<NumScriptExpression>>,
    pub sample_output: Vec<FieldScriptExpression<F>>,
}

impl<F, const WIDTH: usize> BfChallengerExpr<F, WIDTH>
where
    F: BfField + BitExtractor,
{
    pub fn new() -> Result<Self, String> {
        let mut u8_state = vec![];
        for _ in 0..64 {
            u8_state.push(NumScriptExpression::from(0));
        }
        Ok(Self {
            sponge_state: u8_state,
            input_buffer: vec![],
            output_buffer: vec![],

            grind_bits: None,
            grind_output: F::default(),
            sample_input: vec![],
            sample_output: vec![],
        })
    }

    pub fn record_sample(
        &mut self,
        input: &Vec<NumScriptExpression>,
        output: &FieldScriptExpression<F>,
    ) {
        self.sample_input.push(input.clone());
        self.sample_output.push(output.clone());
    }
}

impl<F, const WIDTH: usize> BfChallengerExpr<F, WIDTH>
where
    F: BfField + BitExtractor,
{
    fn duplexing(&mut self) {
        assert!(self.input_buffer.len() <= WIDTH / 2);

        for i in 0..self.input_buffer.len() {
            self.sponge_state[i] = self.input_buffer[i].clone();
        }
        self.input_buffer.clear();

        // Apply the permutation.
        //self.permutation.permute_mut(&mut self.sponge_state);
        let temp = NumScriptExpression::blake3(&self.sponge_state);

        self.sponge_state.clear();
        for i in 0..32 {
            self.sponge_state.push(NumScriptExpression::zero());
        }
        self.sponge_state.push(temp.clone());

        //
        self.output_buffer.push(temp.to_sample());

        //tracing::debug! {"state change: {:?}", u32::from_le_bytes(self.sponge_state[8].as_u8_array())};
    }
}

// impl<F, const WIDTH: usize> CanObserve<NumScriptExpression> for BfChallengerExpr<F, WIDTH>
// where
//     F: BfField + BitExtractor,
// {
//     fn observe(&mut self, value: NumScriptExpression) {
//         //tracing::debug! {"observe: {:?}", u32::from_le_bytes(value.as_u8_array())};

//         // Any buffered output is now invalid.
//         self.output_buffer.clear();

//         self.input_buffer.push(value);

//         if self.input_buffer.len() == 32 {
//             self.duplexing();
//         }
//     }
// }

// impl<F, const WIDTH: usize> CanObserve<F> for BfChallengerExpr<F, WIDTH>
// where
//     F: BfField + BitExtractor,
// {
//     fn observe(&mut self, value: F) {
//         //tracing::debug! {"observe: {:?}", u32::from_le_bytes(value.as_u8_array())};

//         // Any buffered output is now invalid.
//         self.output_buffer.clear();

//         let elems_u32 = value.as_u32_vec();

//         for elem_u32 in elems_u32 {
//             let elems_u8 = elem_u32.to_le_bytes();
//             for elem_u8 in elems_u8 {
//                 self.input_buffer.push(NumScriptExpression::from(elem_u8.into()));
//             }

//         }

//         if self.input_buffer.len() == 32 {
//             self.duplexing();
//         }
//     }
// }

impl<F, const WIDTH: usize> CanObserve<U32> for BfChallengerExpr<F, WIDTH>
where
    F: BfField + BitExtractor,
{
    fn observe(&mut self, value: U32) {
        //tracing::debug! {"observe: {:?}", u32::from_le_bytes(value.as_u8_array())};

        // Any buffered output is now invalid.
        self.output_buffer.clear();

        for elem in value {
            self.input_buffer
                .push(NumScriptExpression::from(elem as u32));
        }

        if self.input_buffer.len() == 32 {
            self.duplexing();
        }
    }
}

// impl<F, const N: usize, const WIDTH: usize> CanObserve<[NumScriptExpression; N]>
//     for BfChallengerExpr<F, WIDTH>
// where
//     F: BfField + BitExtractor,
// {
//     fn observe(&mut self, values: [NumScriptExpression; N]) {
//         for value in values {
//             self.observe(value);
//         }
//     }
// }
impl<F, const N: usize, const WIDTH: usize> CanObserve<[U32; N]> for BfChallengerExpr<F, WIDTH>
where
    F: BfField + BitExtractor,
{
    fn observe(&mut self, values: [U32; N]) {
        for value in values {
            self.observe(value);
        }
    }
}

// impl<F, PF, const N: usize, P, const WIDTH: usize> CanObserve<Hash<PF, PF, N>>
//     for BfChallengerExpr<F, PF, P, WIDTH>
// where
//     F: Field + BitExtractor,
//     PF: PermutationField<4>,
//     P: CryptographicPermutation<[PF; WIDTH]>,
// {
//     fn observe(&mut self, values: Hash<PF, PF, N>) {
//         for pf_val in values {
//             self.observe(pf_val);
//         }
//     }
// }

// for TrivialPcs
impl<F, const WIDTH: usize> CanObserve<Vec<Vec<U32>>> for BfChallengerExpr<F, WIDTH>
where
    F: BfField + BitExtractor,
{
    fn observe(&mut self, valuess: Vec<Vec<U32>>) {
        for values in valuess {
            for value in values {
                self.observe(value);
            }
        }
    }
}

impl<F, const WIDTH: usize> CanSample<FieldScriptExpression<F>> for BfChallengerExpr<F, WIDTH>
where
    F: BfField + BitExtractor,
{
    fn sample(&mut self) -> FieldScriptExpression<F> {
        // if BASE is the same with F
        let mut sample_input = vec![];
        let res;
        if TypeId::of::<F>() == TypeId::of::<BabyBear>() {
            // If we have buffered inputs, we must perform a duplexing so that the challenge will
            // reflect them. Or if we've run out of outputs, we must perform a duplexing to get more.
            if !self.input_buffer.is_empty() || self.output_buffer.is_empty() {
                println!("!self.input_buffer.is_empty() || self.output_buffer.is_empty()");
                self.duplexing();
            }

            let value = self
                .output_buffer
                .pop()
                .expect("Output buffer should be non-empty");

            sample_input.push(value.clone());

            println!("line 1110");
            let output = value.sample_f();

            res = output.num_to_field();
            // res = (&output as &dyn Any).downcast_ref::<F>().unwrap().clone();
        }
        // else, F would be a extension field of Babybear
        else if TypeId::of::<F>() == TypeId::of::<BinomialExtensionField<BabyBear, 4>>() {
            // If we have buffered inputs, we must perform a duplexing so that the challenge will
            // reflect them. Or if we've run out of outputs, we must perform a duplexing to get more.
            if !self.input_buffer.is_empty() || self.output_buffer.is_empty() {
                self.duplexing();
            }
            let value = self
                .output_buffer
                .pop()
                .expect("Output buffer should be non-empty");

            sample_input.push(value.clone());

            let output = value.sample_ef();

            res = output.num_to_field();
        } else {
            panic!("the type of base or f is invalid")
        } // no other implementation yet

        res
    }
}

#[cfg(test)]
mod tests {
    use alloc::collections::BTreeMap;
    use core::cell::{self, Cell};

    use bitcoin::opcodes::OP_EQUAL;
    use bitcoin_script_stack::stack::{StackTracker, StackVariable};
    use primitives::challenger::{self, BfChallenger, Blake3Permutation};
    use scripts::pseudo::OP_256MUL;
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
    #[test]
    fn test_challenger_expr() {
        {
            let bmap = BTreeMap::new();
            let mut stack = StackTracker::new();

            let mut challenger = BfChallengerExpr::<BabyBear, 64>::new().unwrap();

            let value = [1 as u8; 4];
            challenger.observe(value.clone());

            let t = challenger.sample();

            challenger.observe(value.clone());

            let t1 = challenger.sample();

            t1.express_to_script(&mut stack, &bmap);

            stack.number(1103171332 as u32);
            stack.debug();
            stack.op_equal();

            stack.debug();
            let res = stack.run();
            assert!(res.success);
        }

        {
            let bmap = BTreeMap::new();
            let mut stack = StackTracker::new();

            let mut challenger =
                BfChallengerExpr::<BinomialExtensionField<BabyBear, 4>, 64>::new().unwrap();

            let value = [1 as u8, 2 as u8, 3 as u8, 4 as u8];
            challenger.observe(value.clone());

            let _t = challenger.sample();

            challenger.observe(value.clone());

            let t1 = challenger.sample();

            //t1.express_to_script(&mut stack, &bmap);

            let permutation = Blake3Permutation {};
            let mut challenger = BfChallenger::<
                BinomialExtensionField<BabyBear, 4>,
                U32,
                Blake3Permutation,
                16,
            >::new(permutation)
            .unwrap();
            let value = [1 as u8, 2 as u8, 3 as u8, 4 as u8];

            challenger.observe(value.clone());
            let _t_value = challenger.sample();

            challenger.observe(value);
            let t1_value = challenger.sample();

            let equal = t1.equal_for_f(t1_value);

            equal.express_to_script(&mut stack, &bmap);

            let res = stack.run();
            assert!(res.success);
        }
    }
}
