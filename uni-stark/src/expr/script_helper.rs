use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use alloc::vec::Vec;
use alloc::{format, vec};
use core::cell::Cell;
use core::fmt::Debug;
use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use bitcoin::opcodes::OP_FROMALTSTACK;
use bitcoin_script_stack::stack::{StackTracker, StackVariable};
use common::AbstractField;
use primitives::field::BfField;
use scripts::pseudo::{OP_4FROMALTSTACK, OP_4MUL, OP_4PICK, OP_4TOALTSTACK};
use scripts::treepp::*;
use scripts::u31_lib::{
    u31_add, u31_mul, u31_neg, u31_sub, u31_sub_u31ext, u31ext_add, u31ext_add_u31,
    u31ext_equalverify, u31ext_mul, u31ext_mul_u31, u31ext_neg, u31ext_sub, u31ext_sub_u31,
    BabyBear4, BabyBearU31,
};

use super::variable::{ValueVariable, Variable};
use super::Expression;
use crate::SymbolicExpression::{self, *};

/// constraint: bits <= 31
/// input: [b_{0}, b_{1}, ..., b_{bits-1}]
pub fn compress_bits(bits: usize) -> Script {
    assert!(bits <= 31);
    let script = script! {
        for _ in 0..bits-1 {
            OP_DUP OP_ADD // double high bits
            OP_ADD // add a low bit
        }
    };
    script
}

/// decompress num to a vector of bits, from lowest bit to highest bit
pub fn decompress(num: u32, bits: usize) -> Vec<u8> {
    let mut res = vec![];
    for index in 0..bits {
        res.push(((num >> index) & 0x1) as u8);
    }
    res
}

/// input: [index, b_{0}, b_{1}, ..., b_{bits-1}]
pub fn reverse_bits_len_script(bits: usize) -> Script {
    let script = script! {
        for i in 0..bits {
            {i*2} OP_PICK
        }
        {compress_bits(bits)}
        OP_TOALTSTACK

        {compress_bits(bits)}
        OP_EQUALVERIFY

        OP_FROMALTSTACK
    };
    script
}

// the input stack:
// rev_index <-- top
// index
pub fn reverse_bits_len_script_with_input(input_index: u32, bits: usize) -> Script {
    script! {
        OP_TOALTSTACK
        for bit  in decompress(input_index, bits) {
            {bit}
        }
        {reverse_bits_len_script(bits)}
        OP_FROMALTSTACK
        OP_EQUAL
    }
}

fn push_two_adic_generator_table<F: BfField>() -> Script {
    script! {
        for i in (0..28).rev(){
            for j in (0..F::U32_SIZE).rev(){
                {F::two_adic_generator(i).as_u32_vec()[j]}
            }
        }
    }
}

fn pop_two_adic_generator_table<F: BfField>() -> Script {
    script! {
        for i in (0..28).rev(){
            for j in (0..F::U32_SIZE).rev(){
                OP_DROP
            }
        }
    }
}

// input: bits_len
fn get_generator<F: BfField>() -> Script {
    script! {
        OP_TOALTSTACK
        {push_two_adic_generator_table::<F>()}
        OP_FROMALTSTACK
        if F::U32_SIZE ==1{
            OP_PICK
            OP_TOALTSTACK
        }else{
            OP_4MUL
            OP_4PICK
            OP_4TOALTSTACK
        }

        {pop_two_adic_generator_table::<F>()}

        if F::U32_SIZE ==1{
            OP_FROMALTSTACK
        }else{
            OP_4FROMALTSTACK
        }
    }
}

// input stack:
//   value
// output stack:
//   31  <-- top  high_position
//   33   // 33 respresent 0
//   ...
//   0    // low_position
pub(crate) fn value_to_bits_format(bits_len_conf: u32) -> Script {
    script! {
        for i in (0..bits_len_conf).rev(){
            {value_bit_to_altstack(i)}
        }

        for _ in 0..bits_len_conf{
            OP_FROMALTSTACK
        }
    }
}

// value_bits_len
fn value_bit_to_altstack(bits: u32) -> Script {
    script! {
        OP_DUP
        { ((1<<bits) -1 )as u32}
        OP_GREATERTHAN
        OP_IF
            { (1<<bits)as u32}
            OP_SUB
            {1}
            OP_TOALTSTACK
        OP_ELSE
            {0} // plackholder
            OP_TOALTSTACK
        OP_ENDIF
    }
}

// input stack:
//   value
// output stack:
//   31  <-- top  high_position
//   33   // 33 respresent 0
//   ...
//   0    // low_position
fn value_to_bits_format_special(bits_len_conf: u32) -> Script {
    script! {
        for i in (0..bits_len_conf).rev(){
            {value_bit_to_altstack(i)}
        }

        for _ in 0..bits_len_conf{
            OP_FROMALTSTACK
        }
    }
}

// value_bits_len
fn value_bit_to_altstack_special(bits: u32) -> Script {
    script! {
        OP_DUP
        { ((1<<bits) -1 )as u32}
        OP_GREATERTHAN
        OP_IF
            { (1<<bits)as u32}
            OP_SUB
            {bits}
            OP_TOALTSTACK
        OP_ELSE
            {33} // plackholder
            OP_TOALTSTACK
        OP_ENDIF
    }
}

// value_bits_len
fn value_to_generator_bit_altstack(bits: u32, sub_group_bits: u32) -> Script {
    script! {
        OP_DUP
        { ((1<<bits) -1 )as u32}
        OP_GREATERTHAN
        OP_IF
            { (1<<bits)as u32}
            OP_SUB
            {sub_group_bits - bits}
            OP_TOALTSTACK
        OP_ELSE
            {33} // plackholder
            OP_TOALTSTACK
        OP_ENDIF
    }
}

// compute  w^index
// the input stack:
// w <- top
// index : exactly low than 30-bit
pub fn index_to_rou<F: BfField>(sub_group_bits: u32) -> Script {
    assert!(sub_group_bits <= 27);
    // 0..27
    script! {
        if F::U32_SIZE == 1{
            OP_TOALTSTACK
        }else{
            OP_4TOALTSTACK
        }


        OP_DUP
        0
        OP_EQUAL
        OP_IF
            // case: deal index is equal to 0
            OP_DROP
            for j in (0..F::U32_SIZE).rev(){
                {F::one().as_u32_vec()[j]}
            }
        OP_ELSE
            for i in (0..sub_group_bits).rev(){
                {value_to_generator_bit_altstack(i,sub_group_bits)}
            }

            // drop the 0
            OP_0
            OP_EQUALVERIFY

            for _i in 0..sub_group_bits{
                OP_FROMALTSTACK

                // bit-size
                OP_DUP
                {33}
                OP_EQUAL
                OP_IF
                    OP_DROP
                OP_ELSE
                    {get_generator::<F>()}
                        if F::U32_SIZE == 1{
                            OP_DEPTH
                            OP_2
                            OP_EQUAL
                            OP_IF
                            {u31_mul::<BabyBearU31>()}
                        }else{
                            OP_DEPTH
                            OP_8
                            OP_EQUAL
                            OP_IF
                            {u31ext_mul::<BabyBear4>()}
                        }
                    OP_ENDIF
                OP_ENDIF
            }
        OP_ENDIF

        if F::U32_SIZE == 1{
            OP_FROMALTSTACK
            OP_EQUAL
        }else{
            OP_4FROMALTSTACK
            {u31ext_equalverify::<BabyBear4>()}
            OP_1
        }

    }
}
