use alloc::vec::Vec;
use alloc::{format, vec};

use bitcoin::opcodes::OP_FROMALTSTACK;
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
pub fn reverse_bits_len_script_with_input(input_index: u32, bits: usize) -> Script {
    script! {
        for bit  in decompress(input_index, bits) {
            {bit}
        }
        {reverse_bits_len_script(bits)}
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
pub(crate) fn value_exp_7<F: BfField>() -> Script {
    script! {
        if F::U32_SIZE == 1 {
            OP_DUP
            OP_TOALTSTACK  //x 
            {value_square_with_input::<F>()} //x^2
            OP_DUP
            OP_TOALTSTACK   //x^2
            {value_square_with_input::<F>()} //x^4
            OP_FROMALTSTACK
            {u31_mul::<BabyBearU31>()}
            OP_FROMALTSTACK
            {u31_mul::<BabyBearU31>()}
        } else {
            OP_4DUP
            OP_4TOALTSTACK  //x 
            {value_square_with_input::<F>()} //x^2
            OP_4DUP
            OP_4TOALTSTACK   //x^2
            {value_square_with_input::<F>()} //x^4
            OP_4FROMALTSTACK
            {u31ext_mul::<BabyBear4>()}
            OP_4FROMALTSTACK
            {u31ext_mul::<BabyBear4>()}
        }
    }
}

pub fn poseidon2_mat_internal() -> Script {
    //input: state_0 - state_16
    script!{
        OP_0
        //get sum
        for _ in 0..16{
            OP_SWAP
            OP_DUP
            OP_TOALTSTACK
            {u31_add::<BabyBearU31>()}
        }
        for i in 0..16 {
            OP_FROMALTSTACK
            OP_DUP
            {MAT_DIAG16_M_1_u32[i]}
            {u31_mul::<BabyBearU31>()}
            {u31_add::<BabyBearU31>()}
            OP_SWAP
            OP_DUP
            OP_TOALTSTACK
            {u31_add::<BabyBearU31>()}
            OP_FROMALTSTACK
        }
        OP_DROP
    }
}

pub fn poseidon2_mat_external() -> Script {
    script! {
        for _ in 0..4 {
            //dup t_0 t_1 t_2 t_3
            for i in 0..4{
                {i} OP_ROLL
                OP_DUP
                OP_TOALTSTACK
            }
            // s: t3 t2 t1 t0  alt: t3 t2 t1 t0
            {u31_add::<BabyBearU31>()}      //t23
            OP_DUP      
            OP_TOALTSTACK 
            OP_TOALTSTACK
 
            //s: t1 t0    alt:t23 t23 t3 t2 t1 t0
            {u31_add::<BabyBearU31>()}      //t01
            OP_DUP

            OP_FROMALTSTACK //t23

            {u31_add::<BabyBearU31>()}     //t0123
            OP_DUP

            //s: t0123 t0123 t01  alt: t23 t3 t2 t1 t0
            for _ in 0..5 {
                OP_FROMALTSTACK
            }

            //s:t0 t1 t2 t3 t23 t0123 t0123 t01
            OP_SWAP
            5 OP_ROLL
            {u31_add::<BabyBearU31>()}
            OP_DUP
            OP_TOALTSTACK
            //s: t01123 t0 t2 t3 t23 t0123 t01  alt:t01123
            3 OP_ROLL
            4 OP_ROLL
            //s: t0123 t3 t01123 t0 t2 t23 t01
            {u31_add::<BabyBearU31>()}
            //s: t01233 t01123 t0 t2 t23 t01
            OP_DUP
            OP_TOALTSTACK
            //s:t01233 t01123 t0 t2 t23 t01    alt:t01233 t01123
            
            2 OP_ROLL
            OP_DUP
            {u31_add::<BabyBearU31>()}
            {u31_add::<BabyBearU31>()}
            OP_TOALTSTACK
            //s: t01123 t2 t23 t01 alt: new_t3 t01233 t01123
            OP_SWAP
            OP_DUP
            {u31_add::<BabyBearU31>()}
            {u31_add::<BabyBearU31>()}
            //s: new_t1 t23 t01 alt: new_t3 t01233 t01123
            for _ in 0..3 {
                OP_FROMALTSTACK
            }
            //s: t01123 t01233 new_t3 new_t1 t23 t01
            5 OP_ROLL
            {u31_add::<BabyBearU31>()}
            OP_TOALTSTACK
            //s: t01233 new_t3 new_t1 t23  alt:new_t0 

            3 OP_ROLL
            {u31_add::<BabyBearU31>()}
            
            2 OP_ROLL

            OP_TOALTSTACK
            OP_TOALTSTACK
            OP_TOALTSTACK
            // alt: new_t3 new_t2 new_t1 new_t0 
        }
        //alt: t15 t14 ... t0

        for _ in 0..16 {
            OP_FROMALTSTACK
            OP_DUP
        }

        8 OP_ROLL
        16 OP_ROLL 
        24 OP_ROLL
        for _ in 0..3{
            {u31_add::<BabyBearU31>()}
        }
        OP_TOALTSTACK

        1 OP_ROLL
        8 OP_ROLL
        15 OP_ROLL
        22 OP_ROLL
        for _ in 0..3{
            {u31_add::<BabyBearU31>()}
        }
        OP_TOALTSTACK

        2 OP_ROLL
        8 OP_ROLL
        14 OP_ROLL
        20 OP_ROLL
        for _ in 0..3{
            {u31_add::<BabyBearU31>()}
        }
        OP_TOALTSTACK

        3 OP_ROLL
        8 OP_ROLL
        13 OP_ROLL
        18 OP_ROLL
        for _ in 0..3{
            {u31_add::<BabyBearU31>()}
        }
        OP_TOALTSTACK

        //s: t0 ... t15  alt: store3 store2 store1 store0 

        for i in 0..4 {
            if i == 3 {
                for _ in 0..4 {
                    OP_FROMALTSTACK
                }
            } else {
                for _ in 0..4 {
                    OP_FROMALTSTACK
                    OP_DUP
                }
    
                for i in 0..4 {
                    {i}
                    OP_ROLL
                    OP_TOALTSTACK
                }
            }
            
            19 OP_ROLL
            {u31_add::<BabyBearU31>()}

            OP_ROLL
            18 OP_ROLL
            {u31_add::<BabyBearU31>()}

            2 OP_ROLL
            17 OP_ROLL
            {u31_add::<BabyBearU31>()}

            3 OP_ROLL
            16 OP_ROLL
            {u31_add::<BabyBearU31>()}
        }
        //s: new_t0  .. new_t15
    }

}

pub fn sbox_f<F: BfField>() -> Script {
    script!{
        for _ in 0..16 {
            {value_exp_7::<F>()}
            OP_TOALTSTACK
        }
        for _ in 0..16 {
            OP_FROMALTSTACK
        }
    }
}

pub fn add_rc<F: BfField>(round: usize) -> Script {
    script!{
        for i in 0..16 {
            {RC16[round][i]}
            {u31_add::<BabyBearU31>()}
            OP_TOALTSTACK
        }
        for _ in 0..16 {
            OP_FROMALTSTACK
        }
    }
}

pub fn poseidon2_full_round<F: BfField>(round: usize) -> Script {
    script!{
        {add_rc::<F>(round)}
        {sbox_f::<F>()}
        {poseidon2_mat_external()}
    }
}

pub fn poseidon2_partial_round<F: BfField>(round: usize) -> Script {
    script!{
        {RC16[round][0]}
        {u31_add::<BabyBearU31>()}
        {value_exp_7::<F>()}
        {poseidon2_mat_internal()}
    }
}

use lazy_static::lazy_static;
lazy_static! {
    
        pub static ref MAT_DIAG16_M_1_u32: Vec<u32> = vec![
            0x0a632d94,
            0x6db657b7,
            0x56fbdc9e,
            0x052b3d8a,
            0x33745201,
            0x5c03108c,
            0x0beba37b,
            0x258c2e8b,
            0x12029f39,
            0x694909ce,
            0x6d231724,
            0x21c3b222,
            0x3c0904a5,
            0x01d6acda,
            0x27705c83,
            0x5231c802,
        ];

        pub static ref RC16: Vec<Vec<u32>> = vec![
            vec![0x69cbb6af,
            0x46ad93f9,
            0x60a00f4e,
            0x6b1297cd,
            0x23189afe,
            0x732e7bef,
            0x72c246de,
            0x2c941900,
            0x0557eede,
            0x1580496f,
            0x3a3ea77b,
            0x54f3f271,
            0x0f49b029,
            0x47872fe1,
            0x221e2e36,
            0x1ab7202e,
            ],
            vec![0x487779a6,
            0x3851c9d8,
            0x38dc17c0,
            0x209f8849,
            0x268dcee8,
            0x350c48da,
            0x5b9ad32e,
            0x0523272b,
            0x3f89055b,
            0x01e894b2,
            0x13ddedde,
            0x1b2ef334,
            0x7507d8b4,
            0x6ceeb94e,
            0x52eb6ba2,
            0x50642905,
            ],
            vec![0x05453f3f,
            0x06349efc,
            0x6922787c,
            0x04bfff9c,
            0x768c714a,
            0x3e9ff21a,
            0x15737c9c,
            0x2229c807,
            0x0d47f88c,
            0x097e0ecc,
            0x27eadba0,
            0x2d7d29e4,
            0x3502aaa0,
            0x0f475fd7,
            0x29fbda49,
            0x018afffd,
            ],
            vec![0x0315b618,
            0x6d4497d1,
            0x1b171d9e,
            0x52861abd,
            0x2e5d0501,
            0x3ec8646c,
            0x6e5f250a,
            0x148ae8e6,
            0x17f5fa4a,
            0x3e66d284,
            0x0051aa3b,
            0x483f7913,
            0x2cfe5f15,
            0x023427ca,
            0x2cc78315,
            0x1e36ea47,
            ],
            vec![0x5a8053c0,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            ],
            vec![0x693be639,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            ],
            vec![0x3858867d,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            ],
            vec![0x19334f6b,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            ],
            vec![0x128f0fd8,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            ],
            vec![0x4e2b1ccb,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            ],
            vec![0x61210ce0,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            ],
            vec![0x3c318939,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            ],
            vec![0x0b5b2f22,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            ],
            vec![0x2edb11d5,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            ],
            vec![0x213effdf,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            ],
            vec![0x0cac4606,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            ],
            vec![0x241af16d,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            0x00000000,
            ],
            vec![0x7290a80d,
            0x6f7e5329,
            0x598ec8a8,
            0x76a859a0,
            0x6559e868,
            0x657b83af,
            0x13271d3f,
            0x1f876063,
            0x0aeeae37,
            0x706e9ca6,
            0x46400cee,
            0x72a05c26,
            0x2c589c9e,
            0x20bd37a7,
            0x6a2d3d10,
            0x20523767,
            ],
            vec![0x5b8fe9c4,
            0x2aa501d6,
            0x1e01ac3e,
            0x1448bc54,
            0x5ce5ad1c,
            0x4918a14d,
            0x2c46a83f,
            0x4fcf6876,
            0x61d8d5c8,
            0x6ddf4ff9,
            0x11fda4d3,
            0x02933a8f,
            0x170eaf81,
            0x5a9c314f,
            0x49a12590,
            0x35ec52a1,
            ],
            vec![0x58eb1611,
            0x5e481e65,
            0x367125c9,
            0x0eba33ba,
            0x1fc28ded,
            0x066399ad,
            0x0cbec0ea,
            0x75fd1af0,
            0x50f5bf4e,
            0x643d5f41,
            0x6f4fe718,
            0x5b3cbbde,
            0x1e3afb3e,
            0x296fb027,
            0x45e1547b,
            0x4a8db2ab,
            ],
            vec![0x59986d19,
            0x30bcdfa3,
            0x1db63932,
            0x1d7c2824,
            0x53b33681,
            0x0673b747,
            0x038a98a3,
            0x2c5bce60,
            0x351979cd,
            0x5008fb73,
            0x547bca78,
            0x711af481,
            0x3f93bf64,
            0x644d987b,
            0x3c8bcd87,
            0x608758b8,
            ],
            ];
}


#[cfg(test)]
mod tests {
    use p3_baby_bear::BabyBear;
    use p3_field::extension::BinomialExtensionField;
    use p3_field::{AbstractField, TwoAdicField};

    use super::*;
    type EF = BinomialExtensionField<BabyBear, 4>;

    // #[test]
    // fn test_reverse_bits_20() {
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
