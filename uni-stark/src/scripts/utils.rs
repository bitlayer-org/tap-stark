use bitcoin::opcodes::{OP_ADD, OP_DROP, OP_SUB, OP_SWAP, OP_TOALTSTACK, OP_TRUE};
use bitcoin::{script, ScriptBuf as Script};
use bitcoin_script::{define_pushable, script};
use primitives::field::BfField;
use scripts::pseudo::{
    OP_4DROP, OP_4DUP, OP_4FROMALTSTACK, OP_4MUL, OP_4PICK, OP_4ROLL, OP_4SWAP, OP_4TOALTSTACK,
    OP_NDUP,
};
use scripts::u31_lib::{
    u31_add, u31_double, u31_mul, u31_sub, u31_sub_u31ext, u31_to_u31ext, u31ext_add,
    u31ext_double, u31ext_equalverify, u31ext_mul, u31ext_mul_u31, u31ext_mul_u31_by_constant,
    u31ext_sub, u31ext_sub_u31, BabyBear4, BabyBearU31,
};

define_pushable!();

fn value_square_with_input<F: BfField>() -> Script {
    script! {
        if F::U32_SIZE == 1 {
            OP_DUP
            {u31_mul::<BabyBearU31>()}
        }else{
            OP_4DUP
            {u31ext_mul::<BabyBear4>()}
        }
    }
}

pub fn value_exp_n_minus_one<F: BfField>(log_n: usize) -> Script {
    script! {
        for _ in 0..log_n {
            {value_square_with_input::<F>()}
        }
        if F::U32_SIZE == 1 {
            OP_1
            {u31_sub::<BabyBearU31>()}
        }else{
            OP_0 OP_0 OP_0 OP_1
            {u31ext_sub::<BabyBear4>()}
        }
    }
}

fn push_generator_table<F: BfField>(generator: F, quotient_chunk_nums: usize) -> Script {
    script! {
        for i in (0..quotient_chunk_nums).rev() {
            for j in (0..F::U32_SIZE).rev(){
                {generator.exp_u64(i as u64).as_u32_vec()[j]}
            }
        }
        for i in 1..quotient_chunk_nums {
            for j in (0..F::U32_SIZE).rev(){
                {generator.exp_u64(i as u64).try_inverse().unwrap().as_u32_vec()[j]}
            }
        }
    }
}

fn pop_generator_table<F: BfField>(quotient_chunk_nums: usize) -> Script {
    script! {
        for _ in 0..(2 * quotient_chunk_nums - 1){
            for _ in (0..F::U32_SIZE).rev(){
                OP_DROP
            }
        }
    }
}

// stack: index  input: generator: w, quotient_chunk_nums: s
pub fn get_generator<F: BfField>(generator: F, quotient_chunk_nums: usize) -> Script {
    script! {
        OP_TOALTSTACK
        {push_generator_table::<F>(generator, quotient_chunk_nums)}
        OP_FROMALTSTACK
        if F::U32_SIZE == 1{
            OP_PICK
            OP_TOALTSTACK
        }else{
            OP_4MUL
            OP_4PICK
            OP_4TOALTSTACK
        }

        {pop_generator_table::<F>(quotient_chunk_nums)}

        if F::U32_SIZE ==1{
            OP_FROMALTSTACK
        }else{
            OP_4FROMALTSTACK
        }
    }
}

pub fn get_table<F: BfField>(generator: F, quotient_chunk_nums: usize) -> Vec<F> {
    let mut table = vec![];
    for i in (0..quotient_chunk_nums).rev() {
        table.push(generator.exp_u64(i as u64));
    }
    for i in 1..quotient_chunk_nums {
        table.push(generator.exp_u64(i as u64).try_inverse().unwrap());
    }
    table
}
