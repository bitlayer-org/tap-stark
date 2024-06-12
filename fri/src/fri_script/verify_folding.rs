use bitcoin::opcodes::{
    OP_DEPTH, OP_DROP, OP_DUP, OP_ELSE, OP_ENDIF, OP_EQUAL, OP_EQUALVERIFY, OP_FROMALTSTACK,
    OP_GREATERTHAN, OP_PICK, OP_SWAP, OP_TOALTSTACK,
};
use bitcoin::secp256k1::ellswift;
use bitcoin::taproot::TapLeafHash;
use bitcoin::ScriptBuf as Script;
use bitcoin_script::{define_pushable, script};
use p3_field::{AbstractField, TwoAdicField};
use p3_util::{log2_ceil_u64, log2_ceil_usize, log2_strict_usize, reverse_bits_len};
use primitives::field::BfField;
use scripts::pseudo::{
    OP_4DUP, OP_4FROMALTSTACK, OP_4MUL, OP_4PICK, OP_4ROLL, OP_4TOALTSTACK, OP_NDUP,
};
use scripts::u32_rrot::u8_extract_hbit;
use scripts::u32_std::{u32_compress, u32_push};
use scripts::{
    u31_add, u31_double, u31_equalverify, u31_mul, u31_sub, u31ext_add, u31ext_double,
    u31ext_equalverify, u31ext_mul, u31ext_sub, BabyBear4, BabyBearU31, U31Config,
};

define_pushable!();

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
        {OP_EQUAL}
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

// value_bits_len
fn value_bit_to_altstack(bits: u32) -> Script {
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

// the input stack:
// w^index  <- top
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

            for i in 0..sub_group_bits{
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

// calculate the neg index
// input: x, -x
// calculate: -x = x * F::two_adic_generator(1);
pub fn cal_neg_x<F: BfField>(x: F, neg_x: F) -> Script {
    script! {
        for i in (0..F::U32_SIZE).rev() {
            {neg_x.as_u32_vec()[i]}
        }
        for i in (0..F::U32_SIZE).rev() {
            {x.as_u32_vec()[i]}
        }
        {cal_neg_x_with_input::<F>()}
        // for i in (0..F::U32_SIZE).rev() {
        //     {F::two_adic_generator(1).as_u32_vec()[i]}
        // }

        // {u31_mul::<BabyBearU31>()}
        // OP_EQUAL
    }
}

pub fn cal_neg_x_with_input<F: BfField>() -> Script {
    script! {
        for i in (0..F::U32_SIZE).rev() {
            {F::two_adic_generator(1).as_u32_vec()[i]}
        }
        if F::U32_SIZE == 1 {
            {u31_mul::<BabyBearU31>()}
            OP_EQUAL
        }else{
            {u31ext_mul::<BabyBear4>()}
            {u31ext_equalverify::<BabyBear4>()}
            OP_1
        }
    }
}

pub fn value_square_with_input<F: BfField>() -> Script {
    script! {
        // stack state:
        // value
        // value square
        if F::U32_SIZE == 1 {
            OP_DUP
            {u31_mul::<BabyBearU31>()}
            OP_EQUAL
        }else{
            OP_4DUP
            {u31ext_mul::<BabyBear4>()}
            {u31ext_equalverify::<BabyBear4>()}
            OP_1
        }
    }
}

#[cfg(test)]
mod tests {
    use std::ops::MulAssign;

    use bitcoin::opcodes::{OP_DEPTH, OP_EQUAL};
    use bitcoin::script;
    use p3_baby_bear::BabyBear;
    use p3_field::extension::BinomialExtensionField;
    use rand::{random, Rng};
    type AF = BabyBear;
    type F = BinomialExtensionField<BabyBear, 4>;
    use scripts::{execute_script, execute_script_with_inputs};

    use super::*;

    #[test]
    fn test_get_generator() {
        for i in 0..27 {
            let script = script! {
                {i}
                {get_generator::<BabyBear>()}
                {BabyBear::two_adic_generator(i).as_u32_vec()[0]}
                OP_EQUAL
            };

            let res = execute_script(script);
            assert!(res.success);
        }

        for i in 0..27 {
            let script = script! {
                {i}
                {get_generator::<F>()}
                {F::two_adic_generator(i).as_u32_vec()[3]}{F::two_adic_generator(i).as_u32_vec()[2]}{F::two_adic_generator(i).as_u32_vec()[1]}{F::two_adic_generator(i).as_u32_vec()[0]}
                {u31ext_equalverify::<BabyBear4>()}
                OP_1
            };

            let res = execute_script(script);
            assert!(res.success);
        }
    }

    #[test]
    fn test_value_bit_to_altstack() {
        let script = script! {
            7  // 111
            {value_bit_to_altstack(2)}
            OP_DROP // drop 3 = 7-4

            OP_FROMALTSTACK
            2
            OP_EQUAL
        };

        let res = execute_script(script);
        assert!(res.success);
        println!("{:?}", res);

        // push 1 case
        let script = script! {
            1  // 111
            {value_bit_to_altstack(0)}

            OP_0
            OP_EQUALVERIFY

            OP_FROMALTSTACK
            0
            OP_EQUAL
        };

        let res = execute_script(script);
        assert!(res.success);
        println!("{:?}", res);

        // push 0 case
        let script = script! {
            0 // 111
            {value_bit_to_altstack(0)}

            OP_0
            OP_EQUALVERIFY

            OP_FROMALTSTACK
            33
            OP_EQUAL
        };

        let res = execute_script(script);
        assert!(res.success);
        println!("{:?}", res);

        // push 7 case
        let script = script! {
            7  // 111
            {value_bit_to_altstack(2)}
            {value_bit_to_altstack(1)}
            {value_bit_to_altstack(0)}

            OP_0 // the remainder must be 0
            OP_EQUALVERIFY

            OP_FROMALTSTACK
            0
            OP_EQUALVERIFY

            OP_FROMALTSTACK
            1
            OP_EQUALVERIFY

            OP_FROMALTSTACK
            2
            OP_EQUAL
        };

        let res = execute_script(script);
        assert!(res.success);
        println!("{:?}", res);

        // push 6 case
        let script = script! {
            6  // 110
            {value_bit_to_altstack(2)}
            {value_bit_to_altstack(1)}
            {value_bit_to_altstack(0)}

            OP_0 // the remainder must be 0
            OP_EQUALVERIFY

            OP_FROMALTSTACK
            33
            OP_EQUALVERIFY

            OP_FROMALTSTACK
            1
            OP_EQUALVERIFY

            OP_FROMALTSTACK
            2
            OP_EQUAL
        };

        let res = execute_script(script);
        assert!(res.success);
        println!("{:?}", res);

        // push 5 case
        let script = script! {
            5  // 101
            {value_bit_to_altstack(2)}
            {value_bit_to_altstack(1)}
            {value_bit_to_altstack(0)}

            OP_0 // the remainder must be 0
            OP_EQUALVERIFY

            OP_FROMALTSTACK
            0
            OP_EQUALVERIFY

            OP_FROMALTSTACK
            33
            OP_EQUALVERIFY

            OP_FROMALTSTACK
            2
            OP_EQUAL
        };

        let res = execute_script(script);
        assert!(res.success);
        println!("{:?}", res);

        // push 4 case
        let script = script! {
            4  // 100
            {value_bit_to_altstack(2)}
            {value_bit_to_altstack(1)}
            {value_bit_to_altstack(0)}

            OP_0 // the remainder must be 0
            OP_EQUALVERIFY

            OP_FROMALTSTACK
            33
            OP_EQUALVERIFY

            OP_FROMALTSTACK
            33
            OP_EQUALVERIFY

            OP_FROMALTSTACK
            2
            OP_EQUAL
        };

        let res = execute_script(script);
        // assert!(res.success);
        println!("{:?}", res);

        // push 3 case
        let script = script! {
            3  // 011
            {value_bit_to_altstack(2)}
            {value_bit_to_altstack(1)}
            {value_bit_to_altstack(0)}

            OP_0 // the remainder must be 0
            OP_EQUALVERIFY

            OP_FROMALTSTACK
            0
            OP_EQUALVERIFY

            OP_FROMALTSTACK
            1
            OP_EQUALVERIFY

            OP_FROMALTSTACK
            33
            OP_EQUAL
        };

        let res = execute_script(script);
        assert!(res.success);
        println!("{:?}", res);
    }

    #[test]
    fn test_op_depth() {
        let script = script! {
            OP_1
            OP_DEPTH
            OP_1
            OP_ADD
            OP_ADD
            OP_3
            OP_EQUAL
        };

        let res = execute_script(script);
        assert!(res.success);
    }

    #[test]
    fn test_index_to_rou() {
        let index: u64 = 7; // 111 ;  // 7= 4 + 3=(2+1)
        let subgroup_bit_size = 10;
        let generator = BabyBear::two_adic_generator(subgroup_bit_size);
        let self_g = generator.exp_u64(index);

        let generator1 = BabyBear::two_adic_generator(subgroup_bit_size - 2);
        let generator2 = BabyBear::two_adic_generator(subgroup_bit_size - 1);
        let self_g1 = generator2 * generator1 * generator;
        assert_eq!(self_g, self_g1);

        let script = script! {
            {subgroup_bit_size-2}
            {get_generator::<BabyBear>()}
            {subgroup_bit_size-1}
            {get_generator::<BabyBear>()}
            {subgroup_bit_size-0}
            {get_generator::<BabyBear>()}
            {u31_mul::<BabyBearU31>()}
            {u31_mul::<BabyBearU31>()}
            {self_g.as_u32_vec()[0]}
            OP_EQUAL
        };
        let res = execute_script(script);
        println!("{:?}", res);

        let script = script! {
            {index as u32}
            {self_g.as_u32_vec()[0]}
            {index_to_rou::<BabyBear>(subgroup_bit_size as u32)}
        };

        let res = execute_script(script);
        assert!(res.success);

        for j in 0..100 {
            let index: u32 = j; // 111 ;  // 7= 4 + 3=(2+1)
            let subgroup_bit_size = 10;
            let generator = BabyBear::two_adic_generator(subgroup_bit_size);
            let self_g = generator.exp_u64(index as u64);
            let script = script! {
                {index as u32}
                {self_g.as_u32_vec()[0]}
                {index_to_rou::<BabyBear>(subgroup_bit_size as u32)}
            };

            let res = execute_script(script);
            // println!("{:?}", res);
            assert!(res.success);
        }

        // test the index to root-of-unity over babybear extension
        for j in 0..100 {
            let index: u32 = j; // 111 ;  // 7= 4 + 3=(2+1)
            let subgroup_bit_size = 10;
            let generator = F::two_adic_generator(subgroup_bit_size);
            let self_g = generator.exp_u64(index as u64);
            let script = script! {
                {index as u32}
                {self_g.as_u32_vec()[3]}{self_g.as_u32_vec()[2]}{self_g.as_u32_vec()[1]}{self_g.as_u32_vec()[0]}
                {index_to_rou::<F>(subgroup_bit_size as u32)}
            };

            let res = execute_script(script);
            println!("{:?}", res);
            assert!(res.success);
        }
    }

    #[test]
    fn test_neg_x() {
        let x = BabyBear::two_adic_generator(3).exp_u64(6);
        let neg_x = x * BabyBear::two_adic_generator(1);
        let script = cal_neg_x(x, neg_x);
        let res = execute_script(script);
        println!("{:?}", res);
        assert!(res.success);

        let x = F::two_adic_generator(3).exp_u64(6);
        let neg_x: BinomialExtensionField<BabyBear, 4> = x * F::two_adic_generator(1);
        let script = cal_neg_x(x, neg_x);
        let res = execute_script(script);
        println!("{:?}", res);
        assert!(res.success);
    }

    #[test]
    fn test_reverse_bits_20() {
        for bits in 1..31 {
            for _ in 0..30 {
                let x: u32 = rand::thread_rng().gen();
                let x = x % (1 << bits);
                let script = script! {
                    {x}
                    for bit in decompress(x, bits) {
                        {bit}
                    }
                    {reverse_bits_len_script(bits)}
                    {reverse_bits_len(x as usize, bits)}
                    {OP_EQUAL}
                };
                let res = execute_script(script);
                // println!("{:?}", res);
                assert_eq!(res.success, true);
            }
        }
    }
}

// y_0(r)= g_0,1(r^2) + r g_0,2(r^2)
// y_0(-r)= g_0,1(r^2) -r g_0,2(r^2)
// y_1(r^2) = g_0,1(r^2) + v_0 g_0,2(r^2)
pub fn fold_degree<F: BfField>(
    r: Vec<u32>,
    y_0_r: Vec<u32>,
    y_0_neg_r: Vec<u32>,
    beta: Vec<u32>,
    y_1_r_quare: Vec<u32>,
    with_input: bool,
) -> Script {
    if with_input {
        script! {
            for i in (0..r.len()).rev(){
                {y_1_r_quare[i]}
            }
            for i in (0..r.len()).rev(){
                {beta[i]}
            }
            for i in (0..r.len()).rev(){
                {r[i]}
            }
            for i in (0..r.len()).rev(){
                {y_0_neg_r[i]}
            }
            for i in (0..r.len()).rev(){
                {y_0_r[i]}
            }
            {fold_degree_with_input::<F>()}
        }
    } else {
        if F::U32_SIZE == 1 {
            script! {

                // calculate 2 * g_0,1(r^2)
                {y_0_r[0]}
                {y_0_neg_r[0]}
                { u31_add::<BabyBearU31>() }
                // calculate 2 * x * g_0,1(r^2)
                { r[0]}
                { u31_mul::<BabyBearU31>()}
                OP_TOALTSTACK

                // calculate 2 * x * g_0,2(r^2)
                {y_0_r[0]}
                {y_0_neg_r[0]}
                { u31_sub::<BabyBearU31>() }
                // calculate 2 * r * beta * g_0,2(r^2)
                {beta[0]}
                {u31_mul::<BabyBearU31>()}
                // calaulate (2 * r * beta * g_0,2(r^2)) + (2 * r * g_0,1(r^2))
                OP_FROMALTSTACK
                { u31_add::<BabyBearU31>() }
                OP_TOALTSTACK

                // calculate 2*r*y_1(r^2)
                {y_1_r_quare[0]}
                {u31_double::<BabyBearU31>()}
                {r[0]}
                {u31_mul::<BabyBearU31>()}

                // Check Equal
                OP_FROMALTSTACK
                OP_EQUAL
            }
        } else if F::U32_SIZE == 4 {
            script! {

                // calculate 2 * g_0,1(r^2)
                for i in (0..F::U32_SIZE).rev(){
                    {y_0_r[i as usize]}
                }
                for i in (0..F::U32_SIZE).rev(){
                    {y_0_neg_r[i as usize]}
                }
                { u31ext_add::<BabyBear4>() }
                // calculate 2 * x * g_0,1(r^2)
                for i in (0..F::U32_SIZE).rev(){
                    {r[i as usize]}
                }
                { u31ext_mul::<BabyBear4>()}

                for _ in 0..F::U32_SIZE{
                    OP_TOALTSTACK
                }

                // calculate 2 * x * g_0,2(r^2)
                for i in (0..F::U32_SIZE).rev(){
                    {y_0_r[i as usize]}
                }
                for i in (0..F::U32_SIZE).rev(){
                    {y_0_neg_r[i as usize]}
                }
                { u31ext_sub::<BabyBear4>() }
                // calculate 2 * r * beta * g_0,2(r^2)
                for i in (0..F::U32_SIZE).rev(){
                    {beta[i as usize]}
                }
                {u31ext_mul::<BabyBear4>()}
                // calaulate (2 * r * beta * g_0,2(r^2)) + (2 * r * g_0,1(r^2))
                for _ in 0..F::U32_SIZE{
                    OP_FROMALTSTACK
                }

                { u31ext_add::<BabyBear4>() }
                for _ in 0..F::U32_SIZE{
                    OP_TOALTSTACK
                }


                // calculate 2*r*y_1(r^2)
                for i in (0..F::U32_SIZE).rev(){
                    {y_1_r_quare[i as usize]}
                }
                {u31ext_double::<BabyBear4>()}
                for i in (0..F::U32_SIZE).rev(){
                    {r[i as usize]}
                }
                {u31ext_mul::<BabyBear4>()}

                // Check Equal
               for _ in 0..F::U32_SIZE{
                    OP_FROMALTSTACK
                }

                { u31ext_equalverify::<BabyBear4>() }
                OP_1
            }
        } else {
            panic!("incorrect F::U32_SIZE")
        }
    }
}

// y_0(r)= g_0,1(r^2) + r g_0,2(r^2)
// y_0(-r)= g_0,1(r^2) -r g_0,2(r^2)
// y_1(r^2) = g_0,1(r^2) + beta g_0,2(r^2)
// Final Check:
// 2ry_1(r^2) = 2rg_0,1(r^2) + beta 2rg_0,2(r^2)

// First:
// y_0(r) + y_0(-r) = 2 g_0,1(r^2)
// S1 = r * 2 g_0,1(r^2)
// Second:
// S2' = y_0(r) - y_0(-r) = 2 r g_0,2(r^2)
// S2 = beta * S2'
// Third:
// S3 =  S2 + S1
// Fourth:
// S4 = 2 * r * y_1(r^2)
// Fifth:
// S4 == S3
pub fn fold_degree_with_input<F: BfField>() -> Script {
    // the stack afer input
    // y_0_r   <-- top
    // y_0_neg_r
    // r
    // beta
    // y_1_r_quare

    if F::U32_SIZE == 1 {
        script! {

            // calculate 2 * g_0,1(r^2)
            // Dup the top 3 elements and push to altStack
            // {y_0_r}
            // {y_0_neg_r}
            // {r}
            OP_3DUP
            OP_ROT

            // Stack State of top3 is
            // {r}
            // {y_0_r}
            // {y_0_neg_r}
            OP_TOALTSTACK
            OP_TOALTSTACK
            OP_TOALTSTACK


            // altstack state is:
            // {y_0_neg_r} <-- top
            // {y_0_r}
            // {r}
            //
            // stack state is
            // y_0_r   <-- top
            // y_0_neg_r
            // r
            // beta
            // y_1_r_quare

            //  ==== calculate S1 = {r * 2g_0,1(r^2)} ====
            { u31_add::<BabyBearU31>()}
            // stack is
            // 2g_0,1(r^2)   <-- top
            // r
            // beta
            // y_1_r_quare

            { u31_mul::<BabyBearU31>()}
            // stack state is:
            // S1
            // beta
            // y_1_r_quare



            //  ==== calculate S2 = {[2rg_0,2(r^2)] * [beta]} ====
            OP_FROMALTSTACK
            OP_FROMALTSTACK
            OP_SWAP
            // we hope the altstack is:
            // {r}
            // stack is:
            // {y_0_neg_r} <-- top
            // {y_0_r}
            // S1
            // beta
            // y_1_r_quare
            { u31_sub::<BabyBearU31>() }
            // stack is:
            // [2rg_0,2(r^2)]
            // S1
            // beta
            // y_1_r_quare

            OP_ROT

            // stack is:
            // beta
            // [2rg_0,2(r^2)]
            // S1
            // y_1_r_quare

            {u31_mul::<BabyBearU31>()}
            // stack is:
            // S2
            // S1
            // y_1_r_quare


            // ==== calaulate S3 = S2 + S1  ====
            { u31_add::<BabyBearU31>() }
            // stack is:
            // S3  <-- top
            // y_1_r_square

            OP_FROMALTSTACK

            // stack state is:
            // r  <-- top
            // S3  <-- top
            // y_1_r_quare

            // altstack state:
            // empty

            OP_ROT
            // stack is:
            // y_1_r_quare <-- top
            // r
            // S3

            // === calculate S4 = 2*r*y_1(r^2) ===
            {u31_mul::<BabyBearU31>()}
            {u31_double::<BabyBearU31>()}
            // stack is:
            // S4
            // S3

            // Check Equal
            OP_EQUAL
        }
    } else if F::U32_SIZE == 4 {
        // the stack afer input
        // y_0_r   <-- top
        // y_0_neg_r
        // r
        // beta
        // y_1_r_quare
        script! {

            // Dup the top 3 elements and push to altStack
            4 OP_4PICK
            4 OP_4PICK
            16 OP_4PICK

            // Stack State of top3 is
            // {r}
            // {y_0_r}
            // {y_0_neg_r}

            OP_4TOALTSTACK
            OP_4TOALTSTACK
            OP_4TOALTSTACK


            // altstack state is:
            // {y_0_neg_r} <-- top
            // {y_0_r}
            // {r}
            //
            // stack state is
            // y_0_r   <-- top
            // y_0_neg_r
            // r
            // beta
            // y_1_r_quare

            //  ==== calculate S1 = {r * 2g_0,1(r^2)} ====
            { u31ext_add::<BabyBear4>()}
            // stack is
            // 2g_0,1(r^2)   <-- top
            // r
            // beta
            // y_1_r_quare

            { u31ext_mul::<BabyBear4>()}
            // stack state is:
            // S1
            // beta
            // y_1_r_quare



            //  ==== calculate S2 = {[2rg_0,2(r^2)] * [beta]} ====
            OP_4FROMALTSTACK
            OP_4FROMALTSTACK
            4 OP_4ROLL   // OP_SWAP
            // we hope the altstack is:
            // {r}
            // stack is:
            // {y_0_neg_r} <-- top
            // {y_0_r}
            // S1
            // beta
            // y_1_r_quare
            { u31ext_sub::<BabyBear4>() }
            // stack is:
            // [2rg_0,2(r^2)]
            // S1
            // beta
            // y_1_r_quare

            8 OP_4ROLL // OP_ROT

            // stack is:
            // beta
            // [2rg_0,2(r^2)]
            // S1
            // y_1_r_quare

            {u31ext_mul::<BabyBear4>()}
            // stack is:
            // S2
            // S1
            // y_1_r_square


            // ==== calaulate S3 = S2 + S1  ====
            { u31ext_add::<BabyBear4>() }
            // stack is:
            // S3  <-- top
            // y_1_r_square

            OP_4FROMALTSTACK

            // stack state is:
            // r  <-- top
            // S3
            // y_1_r_quare

            // altstack state:
            // empty

            8 OP_4ROLL // OP_ROT
            // stack is:
            // y_1_r_quare <-- top
            // r
            // S3

            // === calculate S4 = 2*r*y_1(r^2) ===
            {u31ext_mul::<BabyBear4>()}
            {u31ext_double::<BabyBear4>()}
            // stack is:
            // S4
            // S3

            // Check Equal
            {u31ext_equalverify::<BabyBear4>()}
            OP_1
        }
    } else {
        panic!("incorrect F::U32_SIZE")
    }
}

#[cfg(test)]
mod tests2 {
    use bitcoin::opcodes::{OP_DROP, OP_EQUAL, OP_EQUALVERIFY, OP_FROMALTSTACK, OP_TOALTSTACK};
    use bitcoin::Script;
    use p3_baby_bear::BabyBear;
    use primitives::field::BfField;
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaCha20Rng;
    use scripts::execute_script;

    use super::*;

    #[test]
    fn test_op4_op() {
        let sc = script! {
            1
            1
            3
            4
            1
            1
           2 OP_4ROLL
           OP_ADD
           7
           OP_EQUAL
           OP_DROP
           OP_EQUALVERIFY
            OP_EQUAL
        };

        let success = execute_script(sc);
        assert!(success.success);

        let sc = script! {
            1
            1
            3
            4
            1
            1
           {OP_NDUP(3)}
           OP_ADD
           OP_ADD
           6
           OP_EQUAL
           OP_DROP
           OP_DROP
           OP_DROP
           OP_DROP

           OP_TOALTSTACK
           OP_ADD
           OP_1 OP_ADD
            OP_FROMALTSTACK
            OP_EQUAL
        };

        let success = execute_script(sc);
        assert!(success.success);
    }

    #[test]
    fn test_folding_poly() {
        let beta = BabyBear::from_u32(2);

        let mut y0_vector = Vec::new();
        let mut y1_vector = Vec::new();

        let y0 = vec![1, 2013265920];
        let y1 = vec![2];
        y0_vector.push(y0);
        y1_vector.push(y1);

        let y0 = vec![6, 569722814, 2013265919, 1443543103];
        let y1 = vec![10, 2013265915];
        y0_vector.push(y0);
        y1_vector.push(y1);

        let y0 = vec![
            120, 1124803747, 1939037439, 700342088, 265625335, 1911300408, 1407786753, 1273260695,
            2013265913, 740005210, 605479152, 101965497, 1747640570, 1312923817, 74228466,
            888462158,
        ];
        let y1 = vec![
            184, 1790580475, 796876005, 196828417, 2013265897, 1816437456, 1216389868, 222685398,
        ];
        y0_vector.push(y0);
        y1_vector.push(y1);

        for (index, log_n) in vec![1, 2, 4].iter().enumerate() {
            let n = 1 << log_n;
            let y0 = y0_vector[index].clone();
            let y1 = y1_vector[index].clone();

            let subgroup = BabyBear::sub_group(*log_n as usize);

            for j in 0..n as usize {
                let x_index = j;
                let x_nge_index = (n / 2 + x_index) % n;
                let x = subgroup[x_index as usize];
                let y0_r = y0[x_index];
                let y0_neg_r = y0[x_nge_index];
                let y_1_r_quare: u32 = y1[x_index % (n / 2)];
                let script = fold_degree::<BabyBear>(
                    x.as_u32_vec(),
                    vec![y0_r],
                    vec![y0_neg_r],
                    beta.as_u32_vec(),
                    vec![y_1_r_quare],
                    false,
                );

                let script_with_input = fold_degree::<BabyBear>(
                    x.as_u32_vec(),
                    vec![y0_r],
                    vec![y0_neg_r],
                    beta.as_u32_vec(),
                    vec![y_1_r_quare],
                    true,
                );

                let result = execute_script(script);
                assert!(result.success);

                let result = execute_script(script_with_input);
                if !result.success {
                    println!("{:?}", result)
                }
                assert!(result.success);
            }
        }
    }
}
