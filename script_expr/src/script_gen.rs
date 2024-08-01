use std::cell::{Cell, Ref, RefCell};
use std::collections::BTreeMap;
use std::env::vars;
use std::sync::{Arc, RwLock};

use bitcoin::hashes::serde::de::value;
use bitcoin_script::script;
use bitcoin_script_stack::stack::StackTracker;
use p3_util::log2_strict_usize;
use primitives::field::BfField;
use scripts::blake3::blake3_var_length;
use scripts::treepp::*;
use scripts::u31_lib::{
    u31_add, u31_mul, u31_neg, u31_sub, u31_sub_u31ext, u31_to_u31ext, u31ext_add, u31ext_add_u31,
    u31ext_equalverify, u31ext_mul, u31ext_mul_u31, u31ext_neg, u31ext_sub, u31ext_sub_u31,
    u32_to_u31, BabyBear4, BabyBearU31,
};

use crate::script_helper::{index_to_rou, value_exp_n};
use crate::{CopyVar, Expression, ScriptExprError, StackVariable, Variable};

#[derive(Debug, Clone, Copy)]
pub(crate) enum StandardOpcodeId {
    Add,
    Mul,
    Sub,
    Neg,
    Equal,
    EqualVerify,
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum CustomOpcodeId {
    Constant,
    ExpConst,
    IndexToRou,
    Lookup,
    Add16,
    Blake3Perm,
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum InputOpcodeId {
    InputVariable,
    ValueVariable,
}

pub(crate) type CustomOpScriptGen = dyn Fn(
        Vec<u32>,
        Vec<u32>,
        &mut StackTracker,
        Ref<Option<Arc<RwLock<Box<dyn Expression>>>>>,
    ) -> Vec<StackVariable>
    + 'static;

pub(crate) type StandardOpScriptGen = dyn Fn(
        Vec<u32>,
        &mut StackTracker,
        Ref<Option<Arc<RwLock<Box<dyn Expression>>>>>,
    ) -> Vec<StackVariable>
    + 'static;

pub(crate) fn standard_script_genreator(opid: StandardOpcodeId) -> Box<StandardOpScriptGen> {
    match opid {
        StandardOpcodeId::Add => Box::new(op_add),
        StandardOpcodeId::Mul => Box::new(op_mul),
        StandardOpcodeId::Sub => Box::new(op_sub),
        StandardOpcodeId::Neg => Box::new(op_neg),
        StandardOpcodeId::EqualVerify => Box::new(op_euqalverify),
        StandardOpcodeId::Equal => Box::new(op_euqal),
    }
}

pub(crate) fn custom_script_generator<F: BfField>(opid: CustomOpcodeId) -> Box<CustomOpScriptGen> {
    match opid {
        CustomOpcodeId::ExpConst => Box::new(op_expconst::<F>),
        CustomOpcodeId::IndexToRou => Box::new(op_indextorou::<F>),
        CustomOpcodeId::Constant => Box::new(op_constant),
        CustomOpcodeId::Lookup => Box::new(op_lookup::<F>),
        CustomOpcodeId::Add16 => Box::new(op_add_16::<F>),
        CustomOpcodeId::Blake3Perm => Box::new(op_blake3::<F>),
    }
}

pub(crate) fn op_lookup<F: BfField>(
    len: Vec<u32>,
    vars_size: Vec<u32>,
    stack: &mut StackTracker,
    copy_ref: Ref<Option<Arc<RwLock<Box<dyn Expression>>>>>,
) -> Vec<StackVariable> {
    assert_eq!(len.len(), 1);
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
    for _ in 0..(len[0]) {
        stack.op_drop();
    }
    let var = stack.from_altstack();

    vec![var]
}

pub(crate) fn op_indextorou<F: BfField>(
    sub_group_bits: Vec<u32>,
    vars_size: Vec<u32>,
    stack: &mut StackTracker,
    copy_ref: Ref<Option<Arc<RwLock<Box<dyn Expression>>>>>,
) -> Vec<StackVariable> {
    assert_eq!(sub_group_bits.len(), 1);
    let vars = stack
        .custom1(
            index_to_rou::<F>(sub_group_bits[0]),
            1,
            1,
            0,
            F::U32_SIZE as u32,
            "FieldExpr::IndexToROU",
        )
        .unwrap();

    vars
}

pub(crate) fn op_add_16<F: BfField>(
    len: Vec<u32>,
    vars_size: Vec<u32>,
    stack: &mut StackTracker,
    copy_ref: Ref<Option<Arc<RwLock<Box<dyn Expression>>>>>,
) -> Vec<StackVariable> {
    let vars = stack
        .custom1(
            script! {
                for _ in 0..15 {
                    if F::U32_SIZE == 1{
                        {u31_add::<BabyBearU31>()}
                    }else{
                        {u31ext_add::<BabyBear4>()}
                    }
                }
            },
            16 as u32,
            1,
            0,
            F::U32_SIZE as u32,
            "ExprADD16_Result",
        )
        .unwrap();
    assert_eq!(vars[0].size(), vars_size[0]);
    vars
}

pub(crate) fn op_blake3<F: BfField>(
    num_bytes: Vec<u32>,
    vars_size: Vec<u32>,
    stack: &mut StackTracker,
    copy_ref: Ref<Option<Arc<RwLock<Box<dyn Expression>>>>>,
) -> Vec<StackVariable> {
    assert_eq!(num_bytes.len(), 1);
    let bytes = num_bytes[0];
    let vars = stack
        .custom1(
            blake3_var_length(bytes as usize),
            bytes,
            32,
            0,
            F::U32_SIZE as u32,
            "ExprBlake3Perm_Result",
        )
        .unwrap();
    assert_eq!(vars[0].size(), vars_size[0]);
    vars
}

pub(crate) fn op_expconst<F: BfField>(
    const_exp_power: Vec<u32>,
    vars_size: Vec<u32>,
    stack: &mut StackTracker,
    copy_ref: Ref<Option<Arc<RwLock<Box<dyn Expression>>>>>,
) -> Vec<StackVariable> {
    assert_eq!(const_exp_power.len(), 1);
    let vars = stack
        .custom1(
            value_exp_n::<F>(log2_strict_usize(const_exp_power[0] as usize)),
            1,
            1,
            0,
            vars_size[0],
            "FieldExpr::ExpConstant",
        )
        .unwrap();

    assert_eq!(vars[0].size(), vars_size[0]);
    vars
}

pub(crate) fn op_constant(
    value: Vec<u32>,
    vars_size: Vec<u32>,
    stack: &mut StackTracker,
    copy_ref: Ref<Option<Arc<RwLock<Box<dyn Expression>>>>>,
) -> Vec<StackVariable> {
    let var = stack.bignumber(value);
    vec![var]
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
                "ExprSub_Result",
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

    vars

    // let copy_var = to_copy(vars[0], stack, copy_ref);
    // if copy_var.is_some() {
    //     vec![copy_var.unwrap()]
    // } else {
    //     vars
    // }
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
                "ExprAdd_Result",
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

    vars

    // let copy_var = to_copy(vars[0], stack, copy_ref);
    // if copy_var.is_some() {
    //     vec![copy_var.unwrap()]
    // } else {
    //     vars
    // }
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
    vars

    // let copy_var = to_copy(vars[0], stack, copy_ref);
    // if copy_var.is_some() {
    //     vec![copy_var.unwrap()]
    // } else {
    //     vars
    // }
}
