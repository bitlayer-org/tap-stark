use alloc::vec;
use alloc::vec::Vec;

use basic::field::BfField;
use scripts::pseudo::{OP_4DUP, OP_4FROMALTSTACK, OP_4MUL, OP_4PICK, OP_4TOALTSTACK};
use scripts::treepp::*;
use scripts::u31_lib::{u31_mul, u31ext_mul, BabyBear4, BabyBearU31};

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

/// constraint: bits <= 31
/// input: [b_{0}, b_{1}, ..., b_{bits-1}]
pub fn compress_custom_bits(input_bits_len: usize, output_bits_len: usize) -> Script {
    assert!(output_bits_len <= 31);
    let script = script! {
        for _ in 0..output_bits_len-1 {
            OP_DUP OP_ADD // double high bits
            OP_ADD // add a low bit
        }
        OP_TOALTSTACK
        for _ in 0..(input_bits_len-output_bits_len){
            OP_DROP
        }
        OP_FROMALTSTACK

    };
    script
}

/// decompress num to a vector of bits, from lowest bit to highest bit
fn decompress(num: u32, bits: usize) -> Vec<u8> {
    let mut res = vec![];
    for index in 0..bits {
        res.push(((num >> index) & 0x1) as u8);
    }
    res
}

/// input: [index, b_{0}, b_{1}, ..., b_{bits-1}]
fn reverse_bits_len_script(bits: usize) -> Script {
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

// input stack:
// index <-- top
// output stack:
// rev_index <-- top
fn reverse_bits_len_script_with_input(input_index: u32, bits: usize) -> Script {
    script! {
        for bit  in decompress(input_index, bits) {
            {bit}
        }
        {reverse_bits_len_script(bits)}
    }
}

// input stack:
// index <-- top
// output stack:
// rev_index <-- top
pub(crate) fn index_to_reverse_index(bits_len: u32) -> Script {
    script! {
        {value_to_bits_format(bits_len)}
        for i in 0..bits_len {
            {i*2} OP_PICK
        }
        {compress_bits(bits_len as usize)}
        OP_TOALTSTACK
        for _ in 0..bits_len {
            OP_DROP
        }
        OP_FROMALTSTACK
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
//   1  <-- top  high_position
//   0   // 0 respresent 0
//   ...
//   0    // low_position
pub(crate) fn value_to_bits_format(bits_len_conf: u32) -> Script {
    script! {
        for i in (0..bits_len_conf).rev(){
            {value_bit_to_altstack(i)}
        }
        OP_DROP
        for _ in 0..bits_len_conf{
            OP_FROMALTSTACK
        }
    }
}

// input stack:
//   value
// output stack:
//   1  <-- top  high_position
//   0   // 0 respresent 0
//   ...
//   0    // low_position
pub(crate) fn value_to_32_bits_format(bits_len_conf: u32) -> Script {
    script! {
        if bits_len_conf == 32 {
            {value_32_bits_to_altstack(bits_len_conf)}
        }
        for i in (0..31).rev(){
            {value_bit_to_altstack(i)}
        }
        OP_DROP
        for _ in 0..bits_len_conf{
            OP_FROMALTSTACK
        }
    }
}

//  Positive numbers: Represented directly as unsigned integers, with a range of [0, 0x7FFFFFFF].
//  Negative numbers: Represented by setting the most significant bit (MSB) to 1, with a range of [-1, -0x80000000].
// Examples:
// • -1 = 0xFFFFFFFF
// • -2 = 0xFFFFFFFE
// • -3 = 0xFFFFFFFD
// Consider the value using 32 bits.
fn value_32_bits_to_altstack(bits: u32) -> Script {
    // because the value more than 1<<31 will represent as negative number in bitcoin vm
    assert!(bits == 32);
    script! {
        OP_DUP
        // { ((1<<31) -1 )as u32}
        {0}
        OP_LESSTHAN // if less than 0, it will bigger than 0x7fff ffff
        OP_IF
            { -0x7fffffff }
            OP_SUB
            OP_1
            OP_ADD  // simulate sub -0x80000000
            {1}
            OP_TOALTSTACK
        OP_ELSE
            {0} // placeholder
            OP_TOALTSTACK
        OP_ENDIF
    }
}

// value_bits_len
fn value_bit_to_altstack(bits: u32) -> Script {
    // because the value more than 1<<31 will represent as negative number in bitcoin vm
    assert!(bits <= 31);
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
//   1  <-- top  high_position
//   0   // 33 respresent 0
//   ...
//   0    // low_position
fn value_to_bits_format_special(bits_len_conf: u32) -> Script {
    script! {
        for i in (0..bits_len_conf).rev(){
            {value_bit_to_altstack_special(i)}
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
        for i in (0..sub_group_bits).rev(){
            {value_to_generator_bit_altstack(i, sub_group_bits)}
        }

        // drop the 0
        OP_0
        OP_EQUALVERIFY

        //init res acc to F::one()
        for j in (0..F::U32_SIZE).rev(){
            {F::one().as_u32_vec()[j]}
        }

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
                    {u31_mul::<BabyBearU31>()}
                }else{
                    {u31ext_mul::<BabyBear4>()}
                }
            OP_ENDIF
        }

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
    use scripts::u31_lib::u31ext_equalverify;

    use super::*;
    type EF = BinomialExtensionField<BabyBear, 4>;

    // #[test]
    // fn test_ts_20() {
    //     for bits in 1..31 {
    //         for _ in 0..30 {
    //             let x: u32 = rand::thread_rng().gen();
    //             let x = x % (1 << bits);
    //             let script = script! {
    //                 {x}
    //                 for bit in decompress(x, bits) {
    //                     {bit}
    //                 }
    //                 {reverse_bits_len_script(bits)}
    //                 {reverse_bits_len(x as usize, bits)}
    //                 OP_EQUAL
    //             };
    //             let res = execute_script(script);
    //             // println!("{:?}", res);
    //             assert_eq!(res.success, true);
    //         }
    //     }
    // }

    #[test]
    fn test_value_to_bits() {
        let index = 6;
        let bits_len = 3;
        let script = script! {
            {index as u32}
            {value_to_bits_format(bits_len)}
            {compress_bits(bits_len as usize)}
            {6}
            OP_EQUAL
        };
        let res = execute_script(script);
        println!("{:?}", res);
        assert_eq!(res.success, true);

        let input_bits_len = 5;
        let output_bits_len = 2;
        let script = script! {
            {index as u32} // 00110
            {value_to_bits_format(input_bits_len)}
            {compress_custom_bits(input_bits_len as usize, output_bits_len as usize)}
            {0}
            OP_EQUAL
        };
        let res = execute_script(script);
        println!("{:?}", res);
        assert_eq!(res.success, true);

        let input_bits_len = 4;
        let output_bits_len = 2;
        let script = script! {
            {index as u32} // 0110
            {value_to_bits_format(input_bits_len)}
            {compress_custom_bits(input_bits_len as usize, output_bits_len as usize)}
            {1}
            OP_EQUAL
        };
        let res = execute_script(script);
        println!("{:?}", res);
        assert_eq!(res.success, true);
    }

    #[test]
    fn test_value_to_32bits() {
        let index = 0x80000000_u32;
        let bits_len = 31;
        let script = script! {
            {-1} // 0xFFFFFFFF
            {value_to_32_bits_format(32)}
            {compress_custom_bits(32,bits_len as usize)}
            {0x7fffffff}
            OP_EQUAL
        };
        let res = execute_script(script);
        assert_eq!(res.success, true);

        let script = script! {
            {-3} // 0xFFFFFFFE
            {value_to_32_bits_format(32)}
            {compress_custom_bits(32,bits_len as usize)}
            {0x7ffffffe}
            OP_EQUAL
        };

        let res = execute_script(script);
        assert_eq!(res.success, true);

    }

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
