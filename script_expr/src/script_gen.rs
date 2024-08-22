use std::collections::BTreeMap;

use bitcoin_script::script;
use bitcoin_script_stack::stack::StackTracker;
use p3_util::{log2_strict_usize, reverse_bits_len};
use primitives::field::BfField;
use scripts::blake3::blake3;
use scripts::pseudo::{OP_4DROP, OP_4FROMALTSTACK, OP_4ROLL, OP_4TOALTSTACK};
use scripts::treepp::*;
use scripts::u31_lib::{
    u31_add, u31_double, u31_mul, u31_neg, u31_square, u31_sub, u31_sub_u31ext, u31_to_u31ext,
    u31ext_add, u31ext_add_u31, u31ext_double, u31ext_equalverify, u31ext_mul, u31ext_mul_u31,
    u31ext_neg, u31ext_square, u31ext_sub, u31ext_sub_u31, u32_to_u31, BabyBear4, BabyBearU31,
};
use scripts::u32_std::u32_compress;

use crate::script_helper::{
    index_to_reverse_index, index_to_rou, reverse_bits_len_script_with_input, value_exp_n,
};
use crate::{StackVariable, Variable};

#[derive(Debug, Clone, Copy)]
pub(crate) enum StandardOpcodeId {
    Add,
    Mul,
    Sub,
    Neg,
    Equal,
    EqualVerify,
    NumToField,
    Constant,
    ExpConst,
    IndexToRou,
    Lookup,
    InputVarMove,
    InputVarCopy,
    Table,
    Square,
    Double,
    Blake3Perm,
    ToSample,
    SampleBase,
    SampleExt,
    ReverseBitslen,
}

pub(crate) type StandardOpScriptGen = dyn Fn(Vec<u32>, &mut StackTracker, &BTreeMap<Variable, StackVariable>) -> Vec<StackVariable>
    + 'static;

pub(crate) fn standard_script_genreator(opid: StandardOpcodeId) -> Box<StandardOpScriptGen> {
    match opid {
        StandardOpcodeId::Add => Box::new(op_add),
        StandardOpcodeId::Mul => Box::new(op_mul),
        StandardOpcodeId::Sub => Box::new(op_sub),
        StandardOpcodeId::Neg => Box::new(op_neg),
        StandardOpcodeId::EqualVerify => Box::new(op_euqalverify),
        StandardOpcodeId::Equal => Box::new(op_euqal),
        StandardOpcodeId::NumToField => Box::new(op_num_to_field),
        StandardOpcodeId::Square => Box::new(op_square),
        StandardOpcodeId::Double => Box::new(op_double),
        StandardOpcodeId::Blake3Perm => Box::new(op_blake3),
        StandardOpcodeId::ToSample => Box::new(op_tosample),
        StandardOpcodeId::SampleBase => Box::new(op_samplebase),
        StandardOpcodeId::SampleExt => Box::new(op_sampleext),
        _ => panic!("not support"),
    }
}

pub(crate) fn custom_script_generator<F: BfField>(
    opid: StandardOpcodeId,
    custom_data: Vec<Vec<u32>>,
) -> Box<StandardOpScriptGen> {
    match opid {
        StandardOpcodeId::ExpConst => Box::new(
            move |vars_size: Vec<u32>,
                  stack: &mut StackTracker,
                  var_getter: &BTreeMap<Variable, StackVariable>| {
                op_expconst::<F>(custom_data.clone(), vars_size, stack, var_getter)
            },
        ),
        StandardOpcodeId::IndexToRou => Box::new(
            move |vars_size: Vec<u32>,
                  stack: &mut StackTracker,
                  var_getter: &BTreeMap<Variable, StackVariable>| {
                op_indextorou::<F>(custom_data.clone(), vars_size, stack, var_getter)
            },
        ),
        StandardOpcodeId::ReverseBitslen => Box::new(
            move |vars_size: Vec<u32>,
                  stack: &mut StackTracker,
                  var_getter: &BTreeMap<Variable, StackVariable>| {
                op_reversebitslen::<F>(custom_data.clone(), vars_size, stack, var_getter)
            },
        ),
        StandardOpcodeId::Constant => Box::new(
            move |vars_size: Vec<u32>,
                  stack: &mut StackTracker,
                  var_getter: &BTreeMap<Variable, StackVariable>| {
                op_constant(custom_data.clone(), vars_size, stack, var_getter)
            },
        ),
        StandardOpcodeId::Lookup => Box::new(
            move |vars_size: Vec<u32>,
                  stack: &mut StackTracker,
                  var_getter: &BTreeMap<Variable, StackVariable>| {
                op_lookup::<F>(custom_data.clone(), vars_size, stack, var_getter)
            },
        ),
        StandardOpcodeId::Table => Box::new(
            move |vars_size: Vec<u32>,
                  stack: &mut StackTracker,
                  var_getter: &BTreeMap<Variable, StackVariable>| {
                op_table(custom_data.clone(), vars_size, stack, var_getter)
            },
        ),
        _ => panic!("not support"),
    }
}

pub(crate) fn input_script_generator(
    opid: StandardOpcodeId,
    input_var: Variable,
) -> Box<StandardOpScriptGen> {
    match opid {
        StandardOpcodeId::InputVarMove => Box::new(
            move |vars_size: Vec<u32>,
                  stack: &mut StackTracker,
                  var_getter: &BTreeMap<Variable, StackVariable>| {
                op_inputvar_move(input_var, vars_size, stack, var_getter)
            },
        ),
        StandardOpcodeId::InputVarCopy => Box::new(
            move |vars_size: Vec<u32>,
                  stack: &mut StackTracker,
                  var_getter: &BTreeMap<Variable, StackVariable>| {
                op_inputvar_copy(input_var, vars_size, stack, var_getter)
            },
        ),
        _ => panic!("not support"),
    }
}

pub(crate) fn op_inputvar_copy(
    input_var: Variable,
    vars_size: Vec<u32>,
    stack: &mut StackTracker,
    var_getter: &BTreeMap<Variable, StackVariable>,
) -> Vec<StackVariable> {
    assert_eq!(vars_size.len(), 0);
    let stack_var = var_getter.get(&input_var).unwrap();
    let var = stack.copy_var(stack_var.clone());
    vec![var]
}

pub(crate) fn op_inputvar_move(
    input_var: Variable,
    vars_size: Vec<u32>,
    stack: &mut StackTracker,
    var_getter: &BTreeMap<Variable, StackVariable>,
) -> Vec<StackVariable> {
    assert_eq!(vars_size.len(), 0);
    let stack_var = var_getter.get(&input_var).unwrap();

    let var = stack.move_var(stack_var.clone());
    vec![var]
}

pub(crate) fn op_num_to_field(
    vars_size: Vec<u32>,
    stack: &mut StackTracker,
    var_getter: &BTreeMap<Variable, StackVariable>,
) -> Vec<StackVariable> {
    assert_eq!(vars_size.len(), 1);
    let vars = stack
        .custom1(
            script! {
                if vars_size[0] == 1 {
                    {u32_to_u31()}
                } else {
                    {u32_to_u31()}
                    {u31_to_u31ext::<BabyBear4>()}
                }
            },
            1,
            1,
            0,
            vars_size[0],
            "FieldExpr::NumToField",
        )
        .unwrap();

    vars
}

pub(crate) fn op_lookup<F: BfField>(
    len: Vec<Vec<u32>>,
    vars_size: Vec<u32>,
    stack: &mut StackTracker,
    var_getter: &BTreeMap<Variable, StackVariable>,
) -> Vec<StackVariable> {
    assert_eq!(len[0].len(), 1);
    assert_eq!(vars_size[0], 1); // the size of index is must 1
    assert!(F::U32_SIZE != 4); // no support extension
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
    for _ in 0..(len[0][0]) {
        stack.op_drop();
    }
    let var = stack.from_altstack();

    vec![var]
}

pub(crate) fn op_table(
    table: Vec<Vec<u32>>,
    vars_size: Vec<u32>,
    stack: &mut StackTracker,
    var_getter: &BTreeMap<Variable, StackVariable>,
) -> Vec<StackVariable> {
    //push table
    let mut vars = vec![];
    for f in table.iter().rev() {
        let v = f.clone();
        vars.push(stack.bignumber(v));
    }
    vars
}

pub(crate) fn op_indextorou<F: BfField>(
    sub_group_bits: Vec<Vec<u32>>,
    _vars_size: Vec<u32>,
    stack: &mut StackTracker,
    var_getter: &BTreeMap<Variable, StackVariable>,
) -> Vec<StackVariable> {
    assert_eq!(sub_group_bits[0].len(), 1);
    let vars = stack
        .custom1(
            index_to_rou::<F>(sub_group_bits[0][0]),
            1,
            1,
            0,
            F::U32_SIZE as u32,
            "FieldExpr::IndexToROU",
        )
        .unwrap();

    vars
}
pub(crate) fn op_reversebitslen<F: BfField>(
    bits_len: Vec<Vec<u32>>,
    _vars_size: Vec<u32>,
    stack: &mut StackTracker,
    var_getter: &BTreeMap<Variable, StackVariable>,
) -> Vec<StackVariable> {
    //assert_eq!(indexandbits[0].len(), 1);
    let vars = stack
        .custom1(
            index_to_reverse_index(bits_len[0][0]),
            1,
            1,
            0,
            1,
            "FieldExpr::ReverseBitsLen",
        )
        .unwrap();
    vars
}

pub(crate) fn op_expconst<F: BfField>(
    const_exp_power: Vec<Vec<u32>>,
    vars_size: Vec<u32>,
    stack: &mut StackTracker,
    var_getter: &BTreeMap<Variable, StackVariable>,
) -> Vec<StackVariable> {
    assert_eq!(const_exp_power[0].len(), 1);
    let vars = stack
        .custom1(
            value_exp_n::<F>(log2_strict_usize(const_exp_power[0][0] as usize)),
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
    value: Vec<Vec<u32>>,
    vars_size: Vec<u32>,
    stack: &mut StackTracker,
    var_getter: &BTreeMap<Variable, StackVariable>,
) -> Vec<StackVariable> {
    assert_eq!(value.len(), 1);
    let var = stack.bignumber(value[0].clone());
    vec![var]
}

pub(crate) fn op_euqal(
    vars_size: Vec<u32>,
    stack: &mut StackTracker,
    var_getter: &BTreeMap<Variable, StackVariable>,
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
    var_getter: &BTreeMap<Variable, StackVariable>,
) -> Vec<StackVariable> {
    assert_eq!(vars_size[0], vars_size[1]);
    assert_eq!(vars_size.len(), 2);
    stack.debug();
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
    var_getter: &BTreeMap<Variable, StackVariable>,
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
    var_getter: &BTreeMap<Variable, StackVariable>,
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

    vars
}

pub(crate) fn op_add(
    vars_size: Vec<u32>,
    stack: &mut StackTracker,
    var_getter: &BTreeMap<Variable, StackVariable>,
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

    vars
}

pub(crate) fn op_double(
    vars_size: Vec<u32>,
    stack: &mut StackTracker,
    var_getter: &BTreeMap<Variable, StackVariable>,
) -> Vec<StackVariable> {
    assert_eq!(vars_size.len(), 1);
    let mut vars = vec![];

    if vars_size[0] == 1 {
        vars = stack
            .custom1(
                script! {
                    {u31_double::<BabyBearU31>()}
                },
                1,
                1,
                0,
                vars_size[0],
                "op_double",
            )
            .unwrap()
    } else {
        vars = stack
            .custom1(
                script! {
                    {u31ext_double::<BabyBear4>()}
                },
                1,
                1,
                0,
                vars_size[0],
                "op_double",
            )
            .unwrap()
    }
    vars
}

pub(crate) fn op_square(
    vars_size: Vec<u32>,
    stack: &mut StackTracker,
    var_getter: &BTreeMap<Variable, StackVariable>,
) -> Vec<StackVariable> {
    assert_eq!(vars_size.len(), 1);
    let mut vars = vec![];

    if vars_size[0] == 1 {
        vars = stack
            .custom1(
                script! {
                    {u31_square()}
                },
                1,
                1,
                0,
                vars_size[0],
                "op_square",
            )
            .unwrap()
    } else {
        vars = stack
            .custom1(
                script! {
                    {u31ext_square()}
                },
                1,
                1,
                0,
                vars_size[0],
                "op_square",
            )
            .unwrap()
    }
    vars
}

pub(crate) fn op_mul(
    vars_size: Vec<u32>,
    stack: &mut StackTracker,
    var_getter: &BTreeMap<Variable, StackVariable>,
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
}

pub(crate) fn op_blake3(
    vars_size: Vec<u32>,
    stack: &mut StackTracker,
    var_getter: &BTreeMap<Variable, StackVariable>,
) -> Vec<StackVariable> {
    assert_eq!(vars_size.len(), 33);
    let mut vars = vec![];
    vars = stack
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

pub(crate) fn op_samplebase(
    vars_size: Vec<u32>,
    stack: &mut StackTracker,
    var_getter: &BTreeMap<Variable, StackVariable>,
) -> Vec<StackVariable> {
    assert_eq!(vars_size[0], 1);
    let mut vars = vec![];
    vars = stack
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

pub(crate) fn op_sampleext(
    vars_size: Vec<u32>,
    stack: &mut StackTracker,
    var_getter: &BTreeMap<Variable, StackVariable>,
) -> Vec<StackVariable> {
    let mut vars = vec![];
    vars = stack
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

pub(crate) fn op_tosample(
    vars_size: Vec<u32>,
    stack: &mut StackTracker,
    var_getter: &BTreeMap<Variable, StackVariable>,
) -> Vec<StackVariable> {
    assert_eq!(vars_size.len(), 1);
    let mut vars = vec![];
    vars = stack
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
