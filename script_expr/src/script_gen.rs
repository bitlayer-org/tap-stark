use std::cell::{Cell, Ref, RefCell};
use std::collections::BTreeMap;
use std::env::vars;
use std::sync::{Arc, RwLock};

use bitcoin::hashes::serde::de::value;
use bitcoin_script::script;
use bitcoin_script_stack::stack::StackTracker;
use p3_util::log2_strict_usize;
use primitives::field::BfField;
use scripts::treepp::*;
use scripts::u31_lib::{
    u31_add, u31_mul, u31_neg, u31_sub, u31_sub_u31ext, u31_to_u31ext, u31ext_add, u31ext_add_u31,
    u31ext_equalverify, u31ext_mul, u31ext_mul_u31, u31ext_neg, u31ext_sub, u31ext_sub_u31,
    u32_to_u31, BabyBear4, BabyBearU31,
};

use crate::script_helper::value_exp_n;
use crate::{CopyVar, Expression, ScriptExprError, StackVariable, Variable};

#[derive(Debug, Clone, Copy)]
pub(crate) enum OpcodeId {
    Add,
    Mul,
    Sub,
    Neg,
    Equal,
    EqualVerify,
}

pub(crate) type OpScriptGen = dyn Fn(
        Vec<u32>,
        &mut StackTracker,
        Ref<Option<Arc<RwLock<Box<dyn Expression>>>>>,
    ) -> Vec<StackVariable>
    + 'static;

pub(crate) fn script_genreator(opid: OpcodeId) -> Box<OpScriptGen> {
    match opid {
        OpcodeId::Add => Box::new(op_add),
        OpcodeId::Mul => Box::new(op_mul),
        OpcodeId::Sub => Box::new(op_sub),
        OpcodeId::Neg => Box::new(op_neg),
        OpcodeId::EqualVerify => Box::new(op_euqalverify),
        OpcodeId::Equal => Box::new(op_euqal),
    }
}
fn to_copy(
    low_var: StackVariable,
    stack: &mut StackTracker,
    copy_ref: Ref<Option<Arc<RwLock<Box<dyn Expression>>>>>,
) -> Option<StackVariable> {
    if copy_ref.is_none() {
        return None;
    }
    let top_var = stack.copy_var(low_var);
    copy_ref
        .as_ref()
        .unwrap()
        .read()
        .unwrap()
        .set_copy_var(low_var);
    Some(top_var)
}

pub(crate) fn op_euqal(
    vars_size: Vec<u32>,
    stack: &mut StackTracker,
    copy_ref: Ref<Option<Arc<RwLock<Box<dyn Expression>>>>>,
) -> Vec<StackVariable> {
    assert_eq!(vars_size[0], vars_size[1]);
    assert_eq!(vars_size.len(), 2);

    if vars_size[0] == 1 {
        let var = stack.op_equal();
        vec![var]
    } else {
        stack.custom(
            u31ext_equalverify::<BabyBear4>(),
            2,
            false,
            0,
            "u31ext_equalverify",
        );
        let var = stack.op_true();
        vec![var]
    }
}

pub(crate) fn op_euqalverify(
    vars_size: Vec<u32>,
    stack: &mut StackTracker,
    copy_ref: Ref<Option<Arc<RwLock<Box<dyn Expression>>>>>,
) -> Vec<StackVariable> {
    assert_eq!(vars_size[0], vars_size[1]);
    assert_eq!(vars_size.len(), 2);
    if vars_size[0] == 1 {
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
    vec![]
}
pub(crate) fn op_neg(
    vars_size: Vec<u32>,
    stack: &mut StackTracker,
    copy_ref: Ref<Option<Arc<RwLock<Box<dyn Expression>>>>>,
) -> Vec<StackVariable> {
    assert_eq!(vars_size.len(), 1);
    let vars = stack
        .custom1(
            script! {
                if vars_size[0] == 1 {
                    {u31_neg::<BabyBearU31>()}
                }else{
                    {u31ext_neg::<BabyBear4>()}
                }
            },
            1,
            1,
            0,
            vars_size[0],
            "ExprNEG_Result",
        )
        .unwrap();
    vars
}

pub(crate) fn op_sub(
    vars_size: Vec<u32>,
    stack: &mut StackTracker,
    copy_ref: Ref<Option<Arc<RwLock<Box<dyn Expression>>>>>,
) -> Vec<StackVariable> {
    assert_eq!(vars_size.len(), 2);
    let mut vars = vec![];
    if vars_size[0] == vars_size[1] {
        vars = stack
            .custom1(
                script! {
                    if vars_size[0] == 1{
                        {u31_sub::<BabyBearU31>()}
                    }else{
                        {u31ext_sub::<BabyBear4>()}
                    }
                },
                2,
                1,
                0,
                vars_size[0],
                "ExprMUL_Result",
            )
            .unwrap()
    } else {
        let mut script = Script::default();

        if vars_size[0] > vars_size[1] {
            script = script! {
                {u31ext_sub_u31::<BabyBear4>()}
            };
        } else {
            script = script! {
                4 OP_ROLL
                {u31_sub_u31ext::<BabyBear4>()}
            };
        }
        vars = stack
            .custom1(
                script,
                2, // consumes 2 variable, one size is 4 and the other size is 1
                1, // the size of output variable is 4
                0,
                vars_size[0].max(vars_size[1]),
                "ExprMUL_Result",
            )
            .unwrap();
    }

    let copy_var = to_copy(vars[0], stack, copy_ref);
    if copy_var.is_some() {
        vec![copy_var.unwrap()]
    } else {
        vars
    }
}

pub(crate) fn op_add(
    vars_size: Vec<u32>,
    stack: &mut StackTracker,
    copy_ref: Ref<Option<Arc<RwLock<Box<dyn Expression>>>>>,
) -> Vec<StackVariable> {
    assert_eq!(vars_size.len(), 2);
    let mut vars = vec![];
    if vars_size[0] == vars_size[1] {
        vars = stack
            .custom1(
                script! {
                    if vars_size[0] == 1{
                        {u31_add::<BabyBearU31>()}
                    }else{
                        {u31ext_add::<BabyBear4>()}
                    }
                },
                2,
                1,
                0,
                vars_size[0],
                "ExprMUL_Result",
            )
            .unwrap()
    } else {
        let mut script = Script::default();

        if vars_size[0] > vars_size[1] {
            script = script! {
                {u31ext_add_u31::<BabyBear4>()}
            };
        } else {
            script = script! {
                4 OP_ROLL
                {u31ext_add_u31::<BabyBear4>()}
            };
        }
        vars = stack
            .custom1(
                script,
                2, // consumes 2 variable, one size is 4 and the other size is 1
                1, // the size of output variable is 4
                0,
                vars_size[0].max(vars_size[1]),
                "ExprMUL_Result",
            )
            .unwrap();
    }

    let copy_var = to_copy(vars[0], stack, copy_ref);
    if copy_var.is_some() {
        vec![copy_var.unwrap()]
    } else {
        vars
    }
}

pub(crate) fn op_mul(
    vars_size: Vec<u32>,
    stack: &mut StackTracker,
    copy_ref: Ref<Option<Arc<RwLock<Box<dyn Expression>>>>>,
) -> Vec<StackVariable> {
    assert_eq!(vars_size.len(), 2);
    let mut vars = vec![];

    if vars_size[0] == vars_size[1] {
        vars = stack
            .custom1(
                script! {
                    if vars_size[0] == 1{
                        {u31_mul::<BabyBearU31>()}
                    }else{
                        {u31ext_mul::<BabyBear4>()}
                    }
                },
                2,
                1,
                0,
                vars_size[0],
                "ExprMUL_Result",
            )
            .unwrap()
    } else {
        let mut script = Script::default();

        if vars_size[0] > vars_size[1] {
            script = script! {
                {u31ext_mul_u31::<BabyBear4>()}
            };
        } else {
            script = script! {
                4 OP_ROLL
                {u31ext_mul_u31::<BabyBear4>()}
            };
        }
        vars = stack
            .custom1(
                script,
                2, // consumes 2 variable, one size is 4 and the other size is 1
                1, // the size of output variable is 4
                0,
                vars_size[0].max(vars_size[1]),
                "ExprMUL_Result",
            )
            .unwrap();
    }

    let copy_var = to_copy(vars[0], stack, copy_ref);
    if copy_var.is_some() {
        vec![copy_var.unwrap()]
    } else {
        vars
    }
}
