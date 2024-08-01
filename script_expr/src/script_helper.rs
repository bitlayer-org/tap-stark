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
    //ouput: new_state_0 - new_state_16
    script! {
        OP_0
        //get sum
        for _ in 0..16{
            OP_SWAP
            OP_DUP
            OP_TOALTSTACK
            {u31_add::<BabyBearU31>()}
        }
        for i in (0..16).rev() {
            OP_FROMALTSTACK
            {MAT_DIAG16_M_1_u32[i]}
            {u31_mul::<BabyBearU31>()}
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
            for i in 0..4 {
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
            5 OP_ROLL
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

            1 OP_ROLL
            2 OP_ROLL
            3 OP_ROLL

            19 OP_ROLL
            {u31_add::<BabyBearU31>()}

            1 OP_ROLL
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
    script! {
        for _ in 0..16 {
            OP_FROMALTSTACK
            {value_exp_7::<F>()}
        }
    }
}

pub fn add_rc<F: BfField>(round: usize) -> Script {
    script! {
        for i in 0..16 {
            {RC16[round][i]}
            {u31_add::<BabyBearU31>()}
            OP_TOALTSTACK
        }
    }
}

pub fn poseidon2_full_round<F: BfField>(round: usize) -> Script {
    script! {
        {add_rc::<F>(round)}
        {sbox_f::<F>()}
        {poseidon2_mat_external()}
    }
}

pub fn poseidon2_partial_round<F: BfField>(round: usize) -> Script {
    script! {
        {RC16[round][0]}
        {u31_add::<BabyBearU31>()}
        {value_exp_7::<F>()}
        {poseidon2_mat_internal()}
    }
}

pub fn poseidon2_perm<F: BfField>() -> Script {
    let rounds_f_beginning = 4;
    let rounds_p = 13;
    let rounds = 21;

    script! {
        {poseidon2_mat_external()}
        for i in 0..rounds_f_beginning{
            {poseidon2_full_round::<F>(i)}
        }
        for i in rounds_f_beginning..rounds_f_beginning + rounds_p{
            {poseidon2_partial_round::<F>(i)}
        }
        for i in rounds_f_beginning + rounds_p..rounds{
            {poseidon2_full_round::<F>(i)}
        }
    }
}

use lazy_static::lazy_static;
lazy_static! {
        //poseidon2 babybear param
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
    use std::ops::{AddAssign, MulAssign};

    use p3_baby_bear::BabyBear;
    use p3_field::extension::BinomialExtensionField;
    use p3_field::{AbstractField, TwoAdicField};
    use scripts::u31_lib::u31_equalverify;

    use super::*;
    type EF = BinomialExtensionField<BabyBear, 4>;
    type F = BabyBear;

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

    #[test]
    fn test_poseidon2_perm_len() {
        let script = poseidon2_perm::<BabyBear>();

        println!("poseidon2 perm size: {:?} \n", script.len());

        let res = execute_script(script);
    }

    #[test]
    fn test_poseidon2_perm() {
        let mut current_state = vec![];
        for i in 0..16 {
            current_state.push(BabyBear::from_canonical_u32(i as u32));
        }

        matmul_external(&mut current_state);
        for r in 0..4 {
            current_state = add_rc(&current_state, &RC16[r]);
            current_state = sbox(&current_state);
            matmul_external(&mut current_state);
        }

        let p_end = 4 + 13;
        for r in 4..p_end {
            current_state[0].add_assign(RC16[r][0]);
            current_state[0] = sbox_p(&current_state[0]);
            matmul_internal(&mut current_state);
        }

        for r in p_end..21 {
            current_state = add_rc(&current_state, &RC16[r]);
            current_state = sbox(&current_state);
            matmul_external(&mut current_state);
        }
        println!("expected:{:?}", current_state);

        let expected = vec![
            156693781, 475434885, 1865994834, 166767749, 1567303069, 1426876722, 1220324855,
            1787973231, 30499433, 1806831384, 1435676709, 1321869261, 916771791, 1584598824,
            189674455, 1963929763,
        ];

        let script = script! {
            for i in (0..16).rev() {
                {i as u32}
            }
            {poseidon2_perm::<F>()}
            for i in 0..16 {
                {expected[i] as u32}
                {u31_equalverify()}
            }
            OP_TRUE
        };
        let res = execute_script(script);
        println!("res:{:?}", res);
        assert!(res.success);
    }

    fn sbox(input: &[F]) -> Vec<F> {
        input.iter().map(|el| sbox_p(el)).collect()
    }

    fn sbox_p(input: &F) -> F {
        let input2 = (*input) * (*input);

        let input4 = input2 * input2;

        input4 * input2 * (*input)
    }
    fn add_rc(input: &[F], rc: &[F]) -> Vec<F> {
        input
            .iter()
            .zip(rc.iter())
            .map(|(a, b)| {
                let mut r = *a;
                r.add_assign(*b);
                r
            })
            .collect()
    }
    #[test]
    fn test_poseidon2_mat_internal() {
        let mut expected = vec![
            120, 1840666671, 905427379, 260159766, 1439778939, 1678725937, 1199953242, 383075907,
            404027967, 1804687535, 190769111, 191408107, 7092270, 401000330, 1210388382, 552253580,
        ];
        // for i in 0..16 {
        //     vec.push(BabyBear::from_canonical_u32(i as u32));
        // }
        // matmul_internal(&mut vec);
        // println!("expected:{:?}", vec);

        let script = script! {
            for i in (0..16).rev() {
                {i as u32}
            }
            {poseidon2_mat_internal()}
            for i in 0..16 {
                {expected[i] as u32}
                {u31_equalverify()}
            }
            OP_TRUE
        };
        let res = execute_script(script);
        println!("res:{:?}", res);
        assert!(res.success);
    }

    #[test]
    fn test_poseidon2_mat_external() {
        let mut expected = vec![
            208, 223, 238, 213, 236, 251, 266, 241, 264, 279, 294, 269, 292, 307, 322, 297,
        ];
        //m4 expected
        // let expected = vec![8, 11, 14, 9, 36, 39, 42, 37, 64, 67, 70, 65, 92, 95, 98, 93];
        // let mut vec = vec![];
        // for i in 0..16 {
        //     vec.push(BabyBear::from_canonical_u32(i as u32));
        // }
        // //matmul_external(&mut vec);
        // matmul_m4(&mut vec);
        // println!("expected:{:?}", vec);

        let script = script! {
            for i in (0..16).rev() {
                {i as u32}
            }
            {poseidon2_mat_external()}
            for i in 0..16 {
                {expected[i] as u32}
                {u31_equalverify()}
            }
            OP_TRUE
        };
        let res = execute_script(script);
        println!("res:{:?}", res);
        assert!(res.success);
    }

    fn matmul_internal(input: &mut [F]) {
        let t = 16;
        // Compute input sum
        let mut sum = input[0];
        input
            .iter()
            .skip(1)
            .take(t - 1)
            .for_each(|el| sum.add_assign(*el));
        // Add sum + diag entry * element to each element
        for i in 0..input.len() {
            input[i].mul_assign(MAT_DIAG16_M_1[i]);
            input[i].add_assign(sum);
        }
    }

    fn matmul_external(input: &mut [F]) {
        let t = 16;
        matmul_m4(input);

        // Applying second cheap matrix for t > 4
        let t4 = t / 4;
        let mut stored = [F::zero(); 4];
        for l in 0..4 {
            stored[l] = input[l];
            for j in 1..t4 {
                stored[l].add_assign(input[4 * j + l]);
            }
        }
        for i in 0..input.len() {
            input[i].add_assign(stored[i % 4]);
        }
    }

    fn matmul_m4(x: &mut [F]) {
        for i in 0..4 {
            let start_index = i * 4;
            let t01 = x[start_index].clone() + x[start_index + 1].clone();
            let t23 = x[start_index + 2].clone() + x[start_index + 3].clone();
            let t0123 = t01.clone() + t23.clone();
            let t01123 = t0123.clone() + x[start_index + 1].clone();
            let t01233 = t0123.clone() + x[start_index + 3].clone();
            // The order here is important. Need to overwrite x[0] and x[2] after x[1] and x[3].
            x[start_index + 3] = t01233.clone() + x[start_index].double(); // 3*x[0] + x[1] + x[2] + 2*x[3]
            x[start_index + 1] = t01123.clone() + x[start_index + 2].double(); // x[0] + 2*x[1] + 3*x[2] + x[3]
            x[start_index] = t01123 + t01; // 2*x[0] + 3*x[1] + x[2] + x[3]
            x[start_index + 2] = t01233 + t23; // x[0] + x[1] + 2*x[2] + 3*x[3]
        }
    }

    use lazy_static::lazy_static;

    lazy_static! {
        pub static ref MAT_DIAG16_M_1: Vec<BabyBear> = vec![
            BabyBear::from_canonical_u32(0x0a632d94),
            BabyBear::from_canonical_u32(0x6db657b7),
            BabyBear::from_canonical_u32(0x56fbdc9e),
            BabyBear::from_canonical_u32(0x052b3d8a),
            BabyBear::from_canonical_u32(0x33745201),
            BabyBear::from_canonical_u32(0x5c03108c),
            BabyBear::from_canonical_u32(0x0beba37b),
            BabyBear::from_canonical_u32(0x258c2e8b),
            BabyBear::from_canonical_u32(0x12029f39),
            BabyBear::from_canonical_u32(0x694909ce),
            BabyBear::from_canonical_u32(0x6d231724),
            BabyBear::from_canonical_u32(0x21c3b222),
            BabyBear::from_canonical_u32(0x3c0904a5),
            BabyBear::from_canonical_u32(0x01d6acda),
            BabyBear::from_canonical_u32(0x27705c83),
            BabyBear::from_canonical_u32(0x5231c802),
        ];
        pub static ref RC16: Vec<Vec<BabyBear>> = vec![
            vec![
                BabyBear::from_canonical_u32(0x69cbb6af),
                BabyBear::from_canonical_u32(0x46ad93f9),
                BabyBear::from_canonical_u32(0x60a00f4e),
                BabyBear::from_canonical_u32(0x6b1297cd),
                BabyBear::from_canonical_u32(0x23189afe),
                BabyBear::from_canonical_u32(0x732e7bef),
                BabyBear::from_canonical_u32(0x72c246de),
                BabyBear::from_canonical_u32(0x2c941900),
                BabyBear::from_canonical_u32(0x0557eede),
                BabyBear::from_canonical_u32(0x1580496f),
                BabyBear::from_canonical_u32(0x3a3ea77b),
                BabyBear::from_canonical_u32(0x54f3f271),
                BabyBear::from_canonical_u32(0x0f49b029),
                BabyBear::from_canonical_u32(0x47872fe1),
                BabyBear::from_canonical_u32(0x221e2e36),
                BabyBear::from_canonical_u32(0x1ab7202e),
            ],
            vec![
                BabyBear::from_canonical_u32(0x487779a6),
                BabyBear::from_canonical_u32(0x3851c9d8),
                BabyBear::from_canonical_u32(0x38dc17c0),
                BabyBear::from_canonical_u32(0x209f8849),
                BabyBear::from_canonical_u32(0x268dcee8),
                BabyBear::from_canonical_u32(0x350c48da),
                BabyBear::from_canonical_u32(0x5b9ad32e),
                BabyBear::from_canonical_u32(0x0523272b),
                BabyBear::from_canonical_u32(0x3f89055b),
                BabyBear::from_canonical_u32(0x01e894b2),
                BabyBear::from_canonical_u32(0x13ddedde),
                BabyBear::from_canonical_u32(0x1b2ef334),
                BabyBear::from_canonical_u32(0x7507d8b4),
                BabyBear::from_canonical_u32(0x6ceeb94e),
                BabyBear::from_canonical_u32(0x52eb6ba2),
                BabyBear::from_canonical_u32(0x50642905),
            ],
            vec![
                BabyBear::from_canonical_u32(0x05453f3f),
                BabyBear::from_canonical_u32(0x06349efc),
                BabyBear::from_canonical_u32(0x6922787c),
                BabyBear::from_canonical_u32(0x04bfff9c),
                BabyBear::from_canonical_u32(0x768c714a),
                BabyBear::from_canonical_u32(0x3e9ff21a),
                BabyBear::from_canonical_u32(0x15737c9c),
                BabyBear::from_canonical_u32(0x2229c807),
                BabyBear::from_canonical_u32(0x0d47f88c),
                BabyBear::from_canonical_u32(0x097e0ecc),
                BabyBear::from_canonical_u32(0x27eadba0),
                BabyBear::from_canonical_u32(0x2d7d29e4),
                BabyBear::from_canonical_u32(0x3502aaa0),
                BabyBear::from_canonical_u32(0x0f475fd7),
                BabyBear::from_canonical_u32(0x29fbda49),
                BabyBear::from_canonical_u32(0x018afffd),
            ],
            vec![
                BabyBear::from_canonical_u32(0x0315b618),
                BabyBear::from_canonical_u32(0x6d4497d1),
                BabyBear::from_canonical_u32(0x1b171d9e),
                BabyBear::from_canonical_u32(0x52861abd),
                BabyBear::from_canonical_u32(0x2e5d0501),
                BabyBear::from_canonical_u32(0x3ec8646c),
                BabyBear::from_canonical_u32(0x6e5f250a),
                BabyBear::from_canonical_u32(0x148ae8e6),
                BabyBear::from_canonical_u32(0x17f5fa4a),
                BabyBear::from_canonical_u32(0x3e66d284),
                BabyBear::from_canonical_u32(0x0051aa3b),
                BabyBear::from_canonical_u32(0x483f7913),
                BabyBear::from_canonical_u32(0x2cfe5f15),
                BabyBear::from_canonical_u32(0x023427ca),
                BabyBear::from_canonical_u32(0x2cc78315),
                BabyBear::from_canonical_u32(0x1e36ea47),
            ],
            vec![
                BabyBear::from_canonical_u32(0x5a8053c0),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
            ],
            vec![
                BabyBear::from_canonical_u32(0x693be639),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
            ],
            vec![
                BabyBear::from_canonical_u32(0x3858867d),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
            ],
            vec![
                BabyBear::from_canonical_u32(0x19334f6b),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
            ],
            vec![
                BabyBear::from_canonical_u32(0x128f0fd8),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
            ],
            vec![
                BabyBear::from_canonical_u32(0x4e2b1ccb),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
            ],
            vec![
                BabyBear::from_canonical_u32(0x61210ce0),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
            ],
            vec![
                BabyBear::from_canonical_u32(0x3c318939),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
            ],
            vec![
                BabyBear::from_canonical_u32(0x0b5b2f22),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
            ],
            vec![
                BabyBear::from_canonical_u32(0x2edb11d5),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
            ],
            vec![
                BabyBear::from_canonical_u32(0x213effdf),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
            ],
            vec![
                BabyBear::from_canonical_u32(0x0cac4606),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
            ],
            vec![
                BabyBear::from_canonical_u32(0x241af16d),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
                BabyBear::from_canonical_u32(0x00000000),
            ],
            vec![
                BabyBear::from_canonical_u32(0x7290a80d),
                BabyBear::from_canonical_u32(0x6f7e5329),
                BabyBear::from_canonical_u32(0x598ec8a8),
                BabyBear::from_canonical_u32(0x76a859a0),
                BabyBear::from_canonical_u32(0x6559e868),
                BabyBear::from_canonical_u32(0x657b83af),
                BabyBear::from_canonical_u32(0x13271d3f),
                BabyBear::from_canonical_u32(0x1f876063),
                BabyBear::from_canonical_u32(0x0aeeae37),
                BabyBear::from_canonical_u32(0x706e9ca6),
                BabyBear::from_canonical_u32(0x46400cee),
                BabyBear::from_canonical_u32(0x72a05c26),
                BabyBear::from_canonical_u32(0x2c589c9e),
                BabyBear::from_canonical_u32(0x20bd37a7),
                BabyBear::from_canonical_u32(0x6a2d3d10),
                BabyBear::from_canonical_u32(0x20523767),
            ],
            vec![
                BabyBear::from_canonical_u32(0x5b8fe9c4),
                BabyBear::from_canonical_u32(0x2aa501d6),
                BabyBear::from_canonical_u32(0x1e01ac3e),
                BabyBear::from_canonical_u32(0x1448bc54),
                BabyBear::from_canonical_u32(0x5ce5ad1c),
                BabyBear::from_canonical_u32(0x4918a14d),
                BabyBear::from_canonical_u32(0x2c46a83f),
                BabyBear::from_canonical_u32(0x4fcf6876),
                BabyBear::from_canonical_u32(0x61d8d5c8),
                BabyBear::from_canonical_u32(0x6ddf4ff9),
                BabyBear::from_canonical_u32(0x11fda4d3),
                BabyBear::from_canonical_u32(0x02933a8f),
                BabyBear::from_canonical_u32(0x170eaf81),
                BabyBear::from_canonical_u32(0x5a9c314f),
                BabyBear::from_canonical_u32(0x49a12590),
                BabyBear::from_canonical_u32(0x35ec52a1),
            ],
            vec![
                BabyBear::from_canonical_u32(0x58eb1611),
                BabyBear::from_canonical_u32(0x5e481e65),
                BabyBear::from_canonical_u32(0x367125c9),
                BabyBear::from_canonical_u32(0x0eba33ba),
                BabyBear::from_canonical_u32(0x1fc28ded),
                BabyBear::from_canonical_u32(0x066399ad),
                BabyBear::from_canonical_u32(0x0cbec0ea),
                BabyBear::from_canonical_u32(0x75fd1af0),
                BabyBear::from_canonical_u32(0x50f5bf4e),
                BabyBear::from_canonical_u32(0x643d5f41),
                BabyBear::from_canonical_u32(0x6f4fe718),
                BabyBear::from_canonical_u32(0x5b3cbbde),
                BabyBear::from_canonical_u32(0x1e3afb3e),
                BabyBear::from_canonical_u32(0x296fb027),
                BabyBear::from_canonical_u32(0x45e1547b),
                BabyBear::from_canonical_u32(0x4a8db2ab),
            ],
            vec![
                BabyBear::from_canonical_u32(0x59986d19),
                BabyBear::from_canonical_u32(0x30bcdfa3),
                BabyBear::from_canonical_u32(0x1db63932),
                BabyBear::from_canonical_u32(0x1d7c2824),
                BabyBear::from_canonical_u32(0x53b33681),
                BabyBear::from_canonical_u32(0x0673b747),
                BabyBear::from_canonical_u32(0x038a98a3),
                BabyBear::from_canonical_u32(0x2c5bce60),
                BabyBear::from_canonical_u32(0x351979cd),
                BabyBear::from_canonical_u32(0x5008fb73),
                BabyBear::from_canonical_u32(0x547bca78),
                BabyBear::from_canonical_u32(0x711af481),
                BabyBear::from_canonical_u32(0x3f93bf64),
                BabyBear::from_canonical_u32(0x644d987b),
                BabyBear::from_canonical_u32(0x3c8bcd87),
                BabyBear::from_canonical_u32(0x608758b8),
            ],
        ];
    }
}
