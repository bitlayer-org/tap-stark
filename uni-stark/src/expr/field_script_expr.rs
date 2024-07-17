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
use crate::expr::script_helper::{index_to_rou, value_exp_n};
use crate::SymbolicExpression::{self, *};

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
    ExpConstant {
        x: Arc<Box<dyn Expression>>,
        y: u32,
        var: StackVariable,
        debug: Cell<bool>,
    },
    IndexToROU {
        // calculate generator^index
        index: Arc<Box<dyn Expression>>, // u32 -> NumberScriptExpression
        sub_group_bits: u32,
        var: StackVariable,
        debug: Cell<bool>,
    },
    NumToField {
        x: Arc<Box<dyn Expression>>,
        var: StackVariable,
        debug: Cell<bool>,
    },
}

impl<F: BfField> FieldScriptExpression<F> {
    pub fn add_ext<EF: BfField>(
        &self,
        rhs: FieldScriptExpression<EF>,
    ) -> FieldScriptExpression<EF> {
        assert_eq!(F::U32_SIZE, 1);
        assert_eq!(EF::U32_SIZE, 4);
        FieldScriptExpression::<EF>::Add {
            x: Arc::new(Box::new(self.clone())),
            y: Arc::new(Box::new(rhs)),
            var: StackVariable::null(),
            debug: Cell::new(false),
        }
    }

    pub fn add_base<Base: BfField>(&self, rhs: FieldScriptExpression<Base>) -> Self {
        assert_eq!(F::U32_SIZE, 4);
        assert_eq!(Base::U32_SIZE, 1);
        FieldScriptExpression::Add {
            x: Arc::new(Box::new(self.clone())),
            y: Arc::new(Box::new(rhs)),
            var: StackVariable::null(),
            debug: Cell::new(false),
        }
    }

    pub fn mul_ext<EF: BfField>(
        &self,
        rhs: FieldScriptExpression<EF>,
    ) -> FieldScriptExpression<EF> {
        assert_eq!(F::U32_SIZE, 1);
        assert_eq!(EF::U32_SIZE, 4);
        FieldScriptExpression::<EF>::Mul {
            x: Arc::new(Box::new(self.clone())),
            y: Arc::new(Box::new(rhs)),
            var: StackVariable::null(),
            debug: Cell::new(false),
        }
    }

    pub fn mul_base<Base: BfField>(&self, rhs: FieldScriptExpression<Base>) -> Self {
        assert_eq!(F::U32_SIZE, 4);
        assert_eq!(Base::U32_SIZE, 1);
        FieldScriptExpression::Mul {
            x: Arc::new(Box::new(self.clone())),
            y: Arc::new(Box::new(rhs)),
            var: StackVariable::null(),
            debug: Cell::new(false),
        }
    }

    pub fn sub_ext<EF: BfField>(
        &self,
        rhs: FieldScriptExpression<EF>,
    ) -> FieldScriptExpression<EF> {
        assert_eq!(F::U32_SIZE, 1);
        assert_eq!(EF::U32_SIZE, 4);
        FieldScriptExpression::<EF>::Sub {
            x: Arc::new(Box::new(self.clone())),
            y: Arc::new(Box::new(rhs)),
            var: StackVariable::null(),
            debug: Cell::new(false),
        }
    }

    pub fn sub_base<Base: BfField>(&self, rhs: FieldScriptExpression<Base>) -> Self {
        assert_eq!(F::U32_SIZE, 4);
        assert_eq!(Base::U32_SIZE, 1);
        FieldScriptExpression::Sub {
            x: Arc::new(Box::new(self.clone())),
            y: Arc::new(Box::new(rhs)),
            var: StackVariable::null(),
            debug: Cell::new(false),
        }
    }

    pub fn exp_constant(&self, power: u32) -> Self {
        FieldScriptExpression::ExpConstant {
            x: Arc::new(Box::new(self.clone())),
            y: power,
            var: StackVariable::null(),
            debug: Cell::new(false),
        }
    }

    pub fn equal_verify(&self, rhs: Self) -> Self {
        FieldScriptExpression::EqualVerify {
            x: Arc::new(Box::new(self.clone())),
            y: Arc::new(Box::new(rhs.clone())),
            debug: Cell::new(false),
        }
    }

    pub fn equal_verify_for_f(&self, rhs: F) -> Self {
        FieldScriptExpression::EqualVerify {
            x: Arc::new(Box::new(self.clone())),
            y: Arc::new(Box::new(Self::from(rhs))),
            debug: Cell::new(false),
        }
    }

    pub fn index_to_rou(index: u32, sub_group_bits: u32) -> Self {
        FieldScriptExpression::IndexToROU {
            index: Arc::new(Box::new(NumScriptExpression::from(index))),
            sub_group_bits: sub_group_bits,
            var: StackVariable::null(),
            debug: Cell::new(false),
        }
    }
}

impl<F: BfField> Expression for FieldScriptExpression<F> {
    fn set_debug(&self) {
        match self {
            FieldScriptExpression::ValueVariable { debug, .. } => {
                debug.set(true);
            }
            FieldScriptExpression::InputVariable { debug, .. } => {
                debug.set(true);
            }
            FieldScriptExpression::Constant { debug, .. } => debug.set(true),
            FieldScriptExpression::Add { debug, .. } => {
                debug.set(true);
            }
            FieldScriptExpression::Sub { debug, .. } => {
                debug.set(true);
            }
            FieldScriptExpression::Neg { debug, .. } => {
                debug.set(true);
            }
            FieldScriptExpression::Mul { debug, .. } => {
                debug.set(true);
            }
            FieldScriptExpression::EqualVerify { debug, .. } => {
                debug.set(true);
            }
            FieldScriptExpression::ExpConstant { debug, .. } => {
                debug.set(true);
            }
            FieldScriptExpression::IndexToROU { debug, .. } => {
                debug.set(true);
            }
            FieldScriptExpression::NumToField { debug, .. } => {
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
            FieldScriptExpression::ValueVariable { v, debug, mut var } => {
                let intput_var = input_variables.get(v.get_var()).unwrap();
                var = stack.copy_var(intput_var.clone());
                if debug.get() == true {
                    stack.debug();
                }
                if v.get_var().get_var_size().is_some() {
                    assert_eq!(var.size(), v.get_var().get_var_size().unwrap());
                }
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
            }
            FieldScriptExpression::Constant { f, mut var, debug } => {
                let v = f.as_u32_vec();
                var = stack.bignumber(v);
                if debug.get() == true {
                    stack.debug();
                }
            }
            FieldScriptExpression::Add {
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
            FieldScriptExpression::Sub {
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
            FieldScriptExpression::Neg { x, debug, mut var } => {
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
            FieldScriptExpression::Mul {
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
            FieldScriptExpression::EqualVerify { x, y, debug } => {
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
                if debug.get() == true {
                    stack.debug();
                }
            }
            FieldScriptExpression::ExpConstant {
                x,
                y,
                debug,
                mut var,
            } => {
                x.express_to_script(stack, input_variables);

                let vars = stack
                    .custom1(
                        value_exp_n::<F>(log2_strict_usize(*y as usize)),
                        1,
                        1,
                        0,
                        x.var_size(),
                        "FieldExpr::ExpConstant",
                    )
                    .unwrap();
                var = vars[0];

                if debug.get() == true {
                    stack.debug();
                }
                assert_eq!(var.size(), F::U32_SIZE as u32);
            }
            FieldScriptExpression::IndexToROU {
                index,
                debug,
                mut var,
                sub_group_bits,
            } => {
                index.express_to_script(stack, input_variables);

                let vars = stack
                    .custom1(
                        index_to_rou::<F>(*sub_group_bits),
                        1,
                        1,
                        0,
                        F::U32_SIZE as u32,
                        "FieldExpr::IndexToROU",
                    )
                    .unwrap();
                var = vars[0];

                if debug.get() == true {
                    stack.debug();
                }
                assert_eq!(var.size(), F::U32_SIZE as u32);
            }
            FieldScriptExpression::NumToField { x, mut var, debug } => {
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
                var = vars[0];

                if debug.get() == true {
                    stack.debug();
                }
                assert_eq!(var.size(), F::U32_SIZE as u32);
            }
        };
        stack.get_script()
    }

    fn var_size(&self) -> u32 {
        F::U32_SIZE as u32
    }

    fn get_var(&self) -> Option<Vec<&StackVariable>> {
        match self {
            FieldScriptExpression::ValueVariable { var, .. } => Some(vec![var]),
            FieldScriptExpression::InputVariable { var, .. } => Some(vec![var]),
            FieldScriptExpression::Constant { var, .. } => Some(vec![var]),
            FieldScriptExpression::Add { var, .. } => Some(vec![var]),
            FieldScriptExpression::Sub { var, .. } => Some(vec![var]),
            FieldScriptExpression::Neg { var, .. } => Some(vec![var]),
            FieldScriptExpression::Mul { var, .. } => Some(vec![var]),
            FieldScriptExpression::EqualVerify { .. } => None,
            FieldScriptExpression::ExpConstant { var, .. } => Some(vec![var]),
            FieldScriptExpression::IndexToROU { var, .. } => Some(vec![var]),
            FieldScriptExpression::NumToField { var, .. } => Some(vec![var]),
        }
    }
}

impl<F: BfField> From<&SymbolicExpression<F>> for FieldScriptExpression<F> {
    fn from(value: &SymbolicExpression<F>) -> Self {
        match value {
            SymbolicExpression::Variable(v) => FieldScriptExpression::InputVariable {
                sv: v.into(),
                debug: Cell::new(false),
                var: StackVariable::null(),
            },
            SymbolicExpression::IsFirstRow => FieldScriptExpression::one(),
            SymbolicExpression::IsLastRow => FieldScriptExpression::one(),
            SymbolicExpression::IsTransition => FieldScriptExpression::one(),
            SymbolicExpression::Constant(f) => FieldScriptExpression::Constant {
                f: f.clone(),
                debug: Cell::new(false),
                var: StackVariable::null(),
            },
            SymbolicExpression::Add { x, y, .. } => FieldScriptExpression::Add {
                x: Arc::new(Box::new(FieldScriptExpression::from(&*x.clone()))),
                y: Arc::new(Box::new(FieldScriptExpression::from(&*y.clone()))),
                debug: Cell::new(false),
                var: StackVariable::null(),
            },
            SymbolicExpression::Sub { x, y, .. } => FieldScriptExpression::Sub {
                x: Arc::new(Box::new(FieldScriptExpression::from(&*x.clone()))),
                y: Arc::new(Box::new(FieldScriptExpression::from(&*y.clone()))),
                debug: Cell::new(false),
                var: StackVariable::null(),
            },
            SymbolicExpression::Neg { x, .. } => FieldScriptExpression::Neg {
                x: Arc::new(Box::new(FieldScriptExpression::from(&*x.clone()))),
                debug: Cell::new(false),
                var: StackVariable::null(),
            },
            SymbolicExpression::Mul { x, y, .. } => FieldScriptExpression::Mul {
                x: Arc::new(Box::new(FieldScriptExpression::from(&*x.clone()))),
                y: Arc::new(Box::new(FieldScriptExpression::from(&*y.clone()))),
                debug: Cell::new(false),
                var: StackVariable::null(),
            },
        }
    }
}

impl<F: BfField> Default for FieldScriptExpression<F> {
    fn default() -> Self {
        Self::zero()
    }
}

impl<F: BfField> From<F> for FieldScriptExpression<F> {
    fn from(value: F) -> Self {
        Self::Constant {
            f: value,
            debug: Cell::new(false),
            var: StackVariable::null(),
        }
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
            FieldScriptExpression::Constant { f, .. } => fm
                .debug_struct("ScriptExpression::Constant")
                .field("f", f)
                .finish(),
            FieldScriptExpression::Add { x, y, debug, var } => fm
                .debug_struct("ScriptExpression::Add")
                .field("variable", var)
                .finish(),
            FieldScriptExpression::Sub { x, y, debug, var } => fm
                .debug_struct("ScriptExpression::Sub")
                .field("variable", var)
                .finish(),
            FieldScriptExpression::Mul { x, y, debug, var } => fm
                .debug_struct("ScriptExpression::Mul")
                .field("variable", var)
                .finish(),
            FieldScriptExpression::Neg { x, debug, var } => fm
                .debug_struct("ScriptExpression::Neg")
                .field("variable", var)
                .finish(),
            FieldScriptExpression::EqualVerify { x, y, debug } => {
                fm.debug_struct("ScriptExpression::Equal").finish()
            }
            FieldScriptExpression::ExpConstant { x, y, debug, var } => fm
                .debug_struct("ScriptExpression::Exp")
                .field("variable", var)
                .finish(),
            FieldScriptExpression::IndexToROU { debug, var, .. } => fm
                .debug_struct("ScriptExpression::Exp")
                .field("variable", var)
                .finish(),
            FieldScriptExpression::NumToField { debug, var, .. } => fm
                .debug_struct("ScriptExpression::Exp")
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
            FieldScriptExpression::Constant { f, debug, var } => FieldScriptExpression::Constant {
                f: f.clone(),
                debug: debug.clone(),
                var: var.clone(),
            },
            FieldScriptExpression::Add { x, y, debug, var } => FieldScriptExpression::Add {
                x: x.clone(),
                y: y.clone(),
                debug: debug.clone(),
                var: var.clone(),
            },
            FieldScriptExpression::Mul { x, y, debug, var } => FieldScriptExpression::Mul {
                x: x.clone(),
                y: y.clone(),
                debug: debug.clone(),
                var: var.clone(),
            },
            FieldScriptExpression::Sub { x, y, debug, var } => FieldScriptExpression::Sub {
                x: x.clone(),
                y: y.clone(),
                debug: debug.clone(),
                var: var.clone(),
            },
            FieldScriptExpression::Neg { x, debug, var } => FieldScriptExpression::Neg {
                x: x.clone(),
                debug: debug.clone(),
                var: var.clone(),
            },
            FieldScriptExpression::EqualVerify { x, y, debug } => {
                FieldScriptExpression::EqualVerify {
                    x: x.clone(),
                    y: y.clone(),
                    debug: debug.clone(),
                }
            }
            FieldScriptExpression::ExpConstant { x, y, debug, var } => {
                FieldScriptExpression::ExpConstant {
                    x: x.clone(),
                    y: y.clone(),
                    debug: debug.clone(),
                    var: var.clone(),
                }
            }
            FieldScriptExpression::IndexToROU {
                index,
                debug,
                var,
                sub_group_bits,
            } => FieldScriptExpression::IndexToROU {
                index: index.clone(),
                debug: debug.clone(),
                var: var.clone(),
                sub_group_bits: *sub_group_bits,
            },
            FieldScriptExpression::NumToField { x, debug, var } => {
                FieldScriptExpression::NumToField {
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

impl<F: BfField> Add<F> for FieldScriptExpression<F> {
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

impl<F: BfField> Add<Self> for FieldScriptExpression<F> {
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

impl<F: BfField> Add<&Self> for FieldScriptExpression<F> {
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
        Self::Sub {
            x: Arc::new(Box::new(self)),
            y: Arc::new(Box::new(rhs)),
            debug: Cell::new(false),
            var: StackVariable::null(),
        }
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
        Self::Neg {
            x: Arc::new(Box::new(self)),
            debug: Cell::new(false),
            var: StackVariable::null(),
        }
    }
}

impl<F: BfField> Mul for FieldScriptExpression<F> {
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

impl<F: BfField> Mul<F> for FieldScriptExpression<F> {
    type Output = Self;

    fn mul(self, rhs: F) -> Self {
        self * Self::from(rhs)
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
    use scripts::u31_lib::{u31ext_equalverify, BabyBear4};

    use super::{Expression, FieldScriptExpression, Variable, *};
    use crate::SymbolicAirBuilder;
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
        let script_exp: Vec<FieldScriptExpression<BabyBear>> = cs
            .iter()
            .map(|cons| FieldScriptExpression::from(cons))
            .collect();
    }

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
        let c = FieldScriptExpression::<EF>::Mul {
            x: Arc::new(Box::new(a)),
            y: Arc::new(Box::new(b)),
            debug: Cell::new(false),
            var: StackVariable::null(),
        };

        let d = FieldScriptExpression::from(BabyBear::two());
        let e = FieldScriptExpression::from(EF::from_canonical_u32(4));
        let f = FieldScriptExpression::<EF>::Mul {
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
