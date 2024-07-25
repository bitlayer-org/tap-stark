use std::cell::{Cell, Ref, RefCell};
use std::collections::BTreeMap;
use std::sync::{Arc, RwLock};

use bitcoin_script::script;
use bitcoin_script_stack::stack::StackTracker;
use primitives::field::BfField;
use scripts::treepp::*;
use scripts::u31_lib::{
    u31_add, u31_mul, u31_neg, u31_sub, u31_sub_u31ext, u31_to_u31ext, u31ext_add, u31ext_add_u31,
    u31ext_equalverify, u31ext_mul, u31ext_mul_u31, u31ext_neg, u31ext_sub, u31ext_sub_u31,
    u32_to_u31, BabyBear4, BabyBearU31,
};

use crate::{CopyVar, Expression, ScriptExprError, StackVariable, Variable};

pub(crate) type OpScriptGen = dyn Fn(
        Vec<u32>,
        &mut StackTracker,
        Ref<Option<Arc<RwLock<Box<dyn Expression>>>>>,
    ) -> Vec<StackVariable>
    + 'static;

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

pub(crate) fn op_sub<F: BfField>(
    vars_size: Vec<u32>,
    stack: &mut StackTracker,
    copy_ref: Ref<Option<Arc<RwLock<Box<dyn Expression>>>>>,
) -> Vec<StackVariable> {
    let mut vars = vec![];
    if vars_size[0] == vars_size[1] {
        vars = stack
            .custom1(
                script! {
                    if F::U32_SIZE == 1{
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

pub(crate) fn op_add<F: BfField>(
    vars_size: Vec<u32>,
    stack: &mut StackTracker,
    copy_ref: Ref<Option<Arc<RwLock<Box<dyn Expression>>>>>,
) -> Vec<StackVariable> {
    let mut vars = vec![];
    if vars_size[0] == vars_size[1] {
        vars = stack
            .custom1(
                script! {
                    if F::U32_SIZE == 1{
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

pub(crate) fn op_mul<F: BfField>(
    vars_size: Vec<u32>,
    stack: &mut StackTracker,
    copy_ref: Ref<Option<Arc<RwLock<Box<dyn Expression>>>>>,
) -> Vec<StackVariable> {
    let mut vars = vec![];
    if vars_size[0] == vars_size[1] {
        vars = stack
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
