use alloc::vec::Vec;
use alloc::{format, vec};

use primitives::field::BfField;
use scripts::pseudo::{OP_4DUP, OP_4FROMALTSTACK, OP_4MUL, OP_4PICK, OP_4TOALTSTACK};
use scripts::treepp::*;
use scripts::u31_lib::{
    u31_add, u31_mul, u31_neg, u31_sub, u31_sub_u31ext, u31ext_add, u31ext_add_u31,
    u31ext_equalverify, u31ext_mul, u31ext_mul_u31, u31ext_neg, u31ext_sub, u31ext_sub_u31,
    BabyBear4, BabyBearU31,
};

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
// generator  <-- top
// index
pub fn index_to_rou<F: BfField>(sub_group_bits: u32) -> Script {
    assert!(sub_group_bits <= 27);
    // 0..27
    script! {

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

    }
}

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

// compute value^n
pub(crate) fn value_exp_n<F: BfField>(log_n: usize) -> Script {
    script! {
        for _ in 0..log_n {
            {value_square_with_input::<F>()}
        }
    }
}

#[cfg(test)]
mod tests {
    use p3_baby_bear::BabyBear;
    use p3_field::extension::BinomialExtensionField;
    use p3_field::{AbstractField, TwoAdicField};

    use super::*;
    type EF = BinomialExtensionField<BabyBear, 4>;

    #[test]
    fn test_index_to_rou() {
        let index: u64 = 7; // 111 ;  // 7= 4 + 3=(2+1)
        let subgroup_bit_size = 10;
        let generator = BabyBear::two_adic_generator(subgroup_bit_size);
        let w = generator.exp_u64(index);

        let script = script! {
            {index as u32}
            {index_to_rou::<BabyBear>(subgroup_bit_size as u32)}
            {w.as_u32_vec()[0]}
            OP_EQUAL
        };

        let res = execute_script(script);
        assert!(res.success);

        for j in 0..100 {
            let index: u32 = j; // 111 ;  // 7= 4 + 3=(2+1)
            let subgroup_bit_size = 10;
            let generator = BabyBear::two_adic_generator(subgroup_bit_size);
            let w = generator.exp_u64(index as u64);
            let script = script! {
                {index as u32}
                {index_to_rou::<BabyBear>(subgroup_bit_size as u32)}
                {w.as_u32_vec()[0]}
                OP_EQUAL
            };

            let res = execute_script(script);
            assert!(res.success);
        }

        // test the index to root-of-unity over babybear extension
        for j in 0..100 {
            let index: u32 = j; // 111 ;  // 7= 4 + 3=(2+1)
            let subgroup_bit_size = 10;
            let generator = EF::two_adic_generator(subgroup_bit_size);
            let w = generator.exp_u64(index as u64);
            let script = script! {
                {index as u32}
                {index_to_rou::<EF>(subgroup_bit_size as u32)}
                {w.as_u32_vec()[3]}{w.as_u32_vec()[2]}{w.as_u32_vec()[1]}{w.as_u32_vec()[0]}
                {u31ext_equalverify::<BabyBear4>()}
                OP_1
            };

            let res = execute_script(script);
            assert!(res.success);
        }
    }
}
