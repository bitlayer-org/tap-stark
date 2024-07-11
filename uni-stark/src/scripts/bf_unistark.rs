use bitcoin::opcodes::{OP_ADD, OP_DROP, OP_SUB, OP_SWAP, OP_TOALTSTACK, OP_TRUE};
use bitcoin::{script, ScriptBuf as Script};
use bitcoin_script::{define_pushable, script};
use itertools::izip;
use p3_field::AbstractField;
use p3_util::log2_strict_usize;
use primitives::field::BfField;
use script_manager::script_info::{self, ScriptInfo};
use scripts::pseudo::{
    OP_4DROP, OP_4DUP, OP_4FROMALTSTACK, OP_4MUL, OP_4PICK, OP_4ROLL, OP_4SWAP, OP_4TOALTSTACK,
    OP_NDUP,
};
use scripts::u31_lib::{
    u31_add, u31_double, u31_mul, u31_sub, u31_sub_u31ext, u31_to_u31ext, u31ext_add,
    u31ext_double, u31ext_equalverify, u31ext_mul, u31ext_mul_u31, u31ext_mul_u31_by_constant,
    u31ext_sub, u31ext_sub_u31, BabyBear4, BabyBearU31,
};

use crate::{get_generator, value_exp_n_minus_one};

define_pushable!();

// * input:
// *      altstack:
// *          empty
// *      stack:
// *          zeta/a            babybear4
// *          (quotient_chunk_nums - 1 - j_i)

// * output:
// *      altstack:
// *          acc_numerator     babybear4
// *      stack:
// *          zeta/a            babybear4
fn compute_acc_numerator<Val: BfField, Challenge: BfField>(
    log_n_conf: usize,
    generator: Val,
    quotient_chunk_nums: usize,
) -> Script {
    script! {
        OP_0 OP_0 OP_0 OP_1  // the accmulator is 1 when intialization
        for _ in 0..(quotient_chunk_nums - 1) {
            OP_4TOALTSTACK                                          //alt: acc        stack: zeta/a index
            OP_4DUP
            OP_4TOALTSTACK
            OP_4TOALTSTACK                                          //alt: zeta/a zeta/a acc  stack:index
            {get_generator::<Val>(generator, quotient_chunk_nums)}  //get w^-j at top
            OP_4FROMALTSTACK                                        //get zeta/babybear_generator at top
            4 OP_ROLL
            {u31ext_mul_u31::<BabyBear4>()}                         //zeta/(babybear_generator * w^j)
            {value_exp_n_minus_one::<Challenge>(log_n_conf)}        //x^n - 1
            OP_4FROMALTSTACK
            OP_4SWAP
            OP_4FROMALTSTACK                                        //acc
            {u31ext_mul::<BabyBear4>()}                             //new_acc  zeta/babybear_generator -j
        }
        OP_4TOALTSTACK
    }
}

pub fn compute_acc_numerator_all<Val: BfField, Challenge: BfField>(
    log_n_conf: usize,
    generator: Val,
    quotient_chunk_nums: usize,
) -> Script {
    script! {
        //push babybeay_generator.inverse()
        {64944062 as u32}
        {u31ext_mul_u31::<BabyBear4>()}   // stack: zeta/a
        for i in 0..quotient_chunk_nums{
            OP_4TOALTSTACK
            for j in 0..quotient_chunk_nums {
                if j != i {
                    {(quotient_chunk_nums - 1 - j) as u32}
                }
            }
            OP_4FROMALTSTACK
            {compute_acc_numerator::<Val, Challenge>(log_n_conf, generator,quotient_chunk_nums)}   //babybear4
        }
        OP_4DROP
        for _ in 0..quotient_chunk_nums {
            OP_4FROMALTSTACK
        }
    }
}

pub fn compute_acc_numerator_script<Val: BfField, Challenge: BfField>(
    zeta: Challenge,
    quotient_chunk_nums: usize,
    degree_bits: usize,
    generator: Val,
    numerators: Vec<Challenge>,
) -> ScriptInfo {
    assert_eq!(numerators.len(), quotient_chunk_nums);
    let mut si = ScriptInfo::new(
        "compute_acc_numerator",
        compute_acc_numerator_all::<Val, Challenge>(degree_bits, generator, quotient_chunk_nums),
    );
    si.add_input(zeta);
    for i in 0..quotient_chunk_nums {
        si.add_output(numerators[i]);
    }
    si
}

// * input:
// *      altstack:
// *          empty
// *      stack:
// *          i
// *          (quotient_chunk_nums-1-j_i)
// *          zps[i]            babybear4

// * output:
// *      altstack:
// *          acc_denominator   babybear
// *      stack:
// *          zps[i]
fn compute_acc_denominator<Val: BfField, Challenge: BfField>(
    log_n_conf: usize,
    generator: Val,
    quotient_chunk_nums: usize,
) -> Script {
    script! {
        OP_1                                                //the accmulator is 1 when intialization
        for _ in 0..(quotient_chunk_nums - 1) {
            OP_TOALTSTACK                                   //alt: acc     s:i,  (S-1-j)
            OP_DUP                                          //alt: acc     s:i,i,(S-1-j)
            OP_TOALTSTACK                                   //alt: i, acc  s:i,  (S-1-j)
            OP_ADD                                          //alt: i, acc  s:i + (S-1-j) = lookup_index
            {get_generator::<Val>(generator, quotient_chunk_nums)}
            {value_exp_n_minus_one::<Val>(log_n_conf)}      //alt: i, acc  s: (w^(i-j))^n - 1
            OP_FROMALTSTACK
            OP_SWAP
            OP_FROMALTSTACK                                 // s: acc, (w^(i-j))^n - 1, i
            {u31_mul::<BabyBearU31>()}                      // s: new_acc i j
        }
        OP_TOALTSTACK
        OP_DROP  //DROP i
    }
}

//  *
//  * compute:
//  *  zps[i] * denominator
//  *
// * input:
// *      altstack:
// *          empty
// *      stack:
// *          zps[i]            babybear4

// * output:
// *      altstack:
// *          zps[i] * acc_denominator  babybear4
// *      stack:
// *          zps[i+1] or empty         babybear4
fn zps_i_mul_denominator<Val: BfField, Challenge: BfField>(
    i: usize,
    log_n_conf: usize,
    generator: Val,
    quotient_chunk_nums: usize,
) -> Script {
    script! {
            for j in 0..quotient_chunk_nums {
                if j != i {
                    {(quotient_chunk_nums - 1 - j) as u32}
                }
            }
            {i as u32}
    // * input:
    // *      altstack:
    // *          empty
    // *      stack:
    // *          i
    // *          (quotient_chunk_nums-1-j_i)
    // *          zps[i]            babybear4
            {compute_acc_denominator::<Val, Challenge>(log_n_conf, generator,quotient_chunk_nums)} //babybear
            OP_FROMALTSTACK
            {u31ext_mul_u31::<BabyBear4>()}
            OP_4TOALTSTACK
        }
}

pub fn zps_mul_denominator_all<Val: BfField, Challenge: BfField>(
    log_n_conf: usize,
    generator: Val,
    quotient_chunk_nums: usize,
) -> Script {
    script! {
        for i in 0..quotient_chunk_nums {
            {zps_i_mul_denominator::<Val, Challenge>(i, log_n_conf, generator,quotient_chunk_nums)}
        }
        for _ in 0..quotient_chunk_nums {
            OP_4FROMALTSTACK
        }

    }
}

pub fn compute_zps_mul_denominator_script<Val: BfField, Challenge: BfField>(
    quotient_chunk_nums: usize,
    degree_bits: usize,
    generator: Val,
    zps: Vec<Challenge>,
    numerators: Vec<Challenge>,
) -> ScriptInfo {
    assert_eq!(numerators.len(), quotient_chunk_nums);
    let mut si = ScriptInfo::new(
        "compute_zps_mul_denominator",
        zps_mul_denominator_all::<Val, Challenge>(degree_bits, generator, quotient_chunk_nums),
    );
    for i in 0..quotient_chunk_nums {
        si.add_input(zps[i]);
        si.add_output(numerators[i]);
    }
    si
}

//  *
//  * compute:
//  *  sum(zps[i] * open_value_i)
//  *
// * input:
// *      altstack:
// *          empty
// *      stack:
// *          open_value_i[0]      babybear4
// *          open_value_i[1]      babybear4
// *          open_value_i[2]      babybear4
// *          open_value_i[3]      babybear4
// *          zps[i]            babybear4

// * output:
// *      altstack:
// *          empty
// *      stack:
// *          quotient_zeta     babybear4
pub fn compute_quotient_zeta<Val: BfField, Challenge: BfField>(
    quotient_chunk_nums: usize,
) -> Script {
    script! {
        OP_0 OP_0 OP_0 OP_0                 //init quotient_zeta to 0
        for _ in 0..quotient_chunk_nums {
            OP_4TOALTSTACK
            {compute_quotient_i::<Val, Challenge>()}
            OP_4FROMALTSTACK
            {u31ext_add::<BabyBear4>()}
        }
    }
}

//SC::Challenge::monomial(e_i) * c
//quotient value is EF, but we use EF as F_slice for commit.
pub fn compute_quotient_i<Val: BfField, Challenge: BfField>() -> Script {
    script! {
        OP_0 OP_0 OP_0 OP_1
        {u31ext_mul::<BabyBear4>()}
        OP_4TOALTSTACK
        OP_0 OP_0 OP_1 OP_0
        {u31ext_mul::<BabyBear4>()}
        OP_4FROMALTSTACK
        {u31ext_add::<BabyBear4>()}
        OP_4TOALTSTACK
        OP_0 OP_1 OP_0 OP_0
        {u31ext_mul::<BabyBear4>()}
        OP_4FROMALTSTACK
        {u31ext_add::<BabyBear4>()}
        OP_4TOALTSTACK
        OP_1 OP_0 OP_0 OP_0
        {u31ext_mul::<BabyBear4>()}
        OP_4FROMALTSTACK
        {u31ext_add::<BabyBear4>()}
        {u31ext_mul::<BabyBear4>()}
    }
}

pub fn compute_quotient_zeta_script<Val: BfField, Challenge: BfField>(
    quotient_chunk_nums: usize,
    zps: Vec<Challenge>,
    open_values: Vec<Vec<Challenge>>,
    quotient_zeta: Challenge,
) -> ScriptInfo {
    assert_eq!(zps.len(), quotient_chunk_nums);
    assert_eq!(open_values.len(), quotient_chunk_nums);
    let mut si = ScriptInfo::new(
        "compute_quotient_zeta",
        compute_quotient_zeta::<Val, Challenge>(quotient_chunk_nums),
    );
    let width = open_values[0].len();
    assert_eq!(width, 4);
    for i in 0..quotient_chunk_nums {
        for j in 0..width {
            si.add_input(open_values[i][j]);
        }
        si.add_input(zps[i]);
    }
    si.add_output(quotient_zeta);
    si
}

// * input:
// *      altstack:
// *          zeta/a            babybear4
// *      stack:
// *          zeta/a            babybear4
// *          zps[i]            babybear4

// * output:
// *      altstack:
// *          zeta/a            babybear4
// *      stack:
// *          zps[i+1] or empty

pub fn verify_quotient_i<Val: BfField, Challenge: BfField>(
    i: usize,
    log_n_conf: usize,
    generator: Val,
    quotient_chunk_nums: usize,
) -> Script {
    println!(
        "verify_quotient i:{}, log_n_conf:{}, quotient_chunk_nums:{}",
        i, log_n_conf, quotient_chunk_nums
    );
    script! {
        OP_4TOALTSTACK
        for j in 0..quotient_chunk_nums {
            if j != i {
                {(quotient_chunk_nums - 1 - j) as u32}
            }
        }
        OP_4FROMALTSTACK
        {compute_acc_numerator::<Val, Challenge>(log_n_conf, generator,quotient_chunk_nums)}   //babybear4

        {zps_i_mul_denominator::<Val, Challenge>(i, log_n_conf, generator,quotient_chunk_nums)}

        OP_4FROMALTSTACK
        OP_4FROMALTSTACK

        {u31ext_equalverify::<BabyBear4>()}
    }
}

// * input:
// *      altstack:
// *
// *      stack:
//            a
//*           zeta
//*           zps[0]
//*           zps[1]
//*           ...
//*           zps[quotient_chunk_nums-1]
pub fn verify_quotient<Val: BfField, Challenge: BfField>(
    quotient_chunk_nums: usize,
    generator: Val,
    log_n_conf: usize,
) -> Script {
    script! {
        {u31ext_mul_u31::<BabyBear4>()}   // stack: zeta/a
        OP_4TOALTSTACK
        for i in 0..quotient_chunk_nums {
            OP_4FROMALTSTACK
            OP_4DUP
            OP_4TOALTSTACK
            {verify_quotient_i::<Val, Challenge>(i, log_n_conf, generator,quotient_chunk_nums)}
        }
        OP_4FROMALTSTACK
        OP_4DROP
        // OP_TRUE
    }
}

pub fn verify_quotient_script<Val: BfField, Challenge: BfField>(
    zeta: Challenge,
    quotient_chunk_nums: usize,
    degree_bits: usize,
    generator: Val,
    zps: Vec<Challenge>,
) -> ScriptInfo {
    assert_eq!(zps.len(), quotient_chunk_nums);
    let mut si = ScriptInfo::new(
        "verify_zps",
        verify_quotient::<Val, Challenge>(quotient_chunk_nums, generator, degree_bits),
    );
    si.add_input(Val::generator().try_inverse().unwrap())
        .add_input(zeta);
    for i in 0..quotient_chunk_nums {
        si.add_input(zps[i]);
    }
    si
}

#[cfg(test)]
mod tests {
    use bitcoin::opcodes::OP_TRUE;
    use bitcoin_script::define_pushable;
    use fri::{FriConfig, TwoAdicFriPcs};
    use itertools::{izip, Itertools};
    use p3_commit::{PolynomialSpace, TwoAdicMultiplicativeCoset};
    use p3_dft::{Radix2Dit, Radix2DitParallel, TwoAdicSubgroupDft};
    use p3_field::{AbstractExtensionField, AbstractField, Field, TwoAdicField};
    use p3_matrix::dense::RowMajorMatrix;
    use p3_matrix::util::reverse_matrix_index_bits;
    use p3_util::log2_strict_usize;
    use primitives::bf_pcs::Pcs;
    use primitives::challenger::{self, Blake3Permutation};
    use primitives::field::BfField;
    use primitives::mmcs::taptree_mmcs::TapTreeMmcs;
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaCha20Rng;
    use script_manager::bc_assignment::DefaultBCAssignment;
    use scripts::pseudo::{OP_4DROP, OP_4DUP, OP_4FROMALTSTACK, OP_4TOALTSTACK};
    use scripts::u31_lib::{u31ext_equalverify, u31ext_mul, BabyBear4};
    use scripts::{execute_script, execute_script_with_inputs, BabyBear, BinomialExtensionField};

    use crate::scripts::bf_unistark::{
        compute_acc_numerator, compute_acc_numerator_script, compute_zps_mul_denominator_script,
        verify_quotient, verify_quotient_script,
    };
    use crate::{prove, StarkConfig};

    define_pushable!();

    type Val = BabyBear;
    type ValMmcs = TapTreeMmcs<Val>;
    type Challenge = BinomialExtensionField<Val, 4>;
    type ChallengeMmcs = TapTreeMmcs<Challenge>;
    type Dft = Radix2DitParallel;
    type MyPcs = TwoAdicFriPcs<Val, Dft, ValMmcs, ChallengeMmcs>;

    fn get_pcs() -> MyPcs {
        let val_mmcs = ValMmcs::new();
        let challenge_mmscs = ChallengeMmcs::new();
        let fri_config = FriConfig {
            log_blowup: 2,
            num_queries: 10,
            proof_of_work_bits: 8,
            mmcs: challenge_mmscs,
        };
        let pcs = MyPcs::new(Dft {}, val_mmcs, fri_config);
        pcs
    }

    #[test]
    fn test_numerator() {
        type Challenge = BinomialExtensionField<BabyBear, 4>;
        type Val = BabyBear;

        let degree = 8; //n
        let log_degree = log2_strict_usize(degree);
        let quotient_degree = 4; //s
        let log_quotient_degree = log2_strict_usize(quotient_degree);

        let mut rng = ChaCha20Rng::seed_from_u64(0u64);

        let zeta = rng.gen::<Challenge>();

        let a = Val::generator().try_inverse().unwrap();

        // let trace_domain = pcs.natural_domain_for_degree(degree);
        let trace_domain = TwoAdicMultiplicativeCoset {
            log_n: log_degree,
            shift: Val::one(),
        };

        let quotient_domain =
            trace_domain.create_disjoint_domain(1 << (log_degree + log_quotient_degree));

        let generator = Val::two_adic_generator(quotient_domain.log_n);

        let quotient_chunks_domains = quotient_domain.split_domains(quotient_degree);

        let quotient_chunk_nums = quotient_chunks_domains.len();

        let numerators = quotient_chunks_domains
            .iter()
            .enumerate()
            .map(|(i, domain)| {
                quotient_chunks_domains
                    .iter()
                    .enumerate()
                    .filter(|(j, _)| *j != i)
                    .map(|(_, other_domain)| other_domain.zp_at_point(zeta))
                    .product::<Challenge>()
            })
            .collect_vec();
        let mut bc_assigner = DefaultBCAssignment::new();
        let mut exec_script_info = compute_acc_numerator_script::<Val, Challenge>(
            zeta,
            quotient_chunk_nums,
            log_degree,
            generator,
            numerators,
        );

        exec_script_info.gen(&mut bc_assigner);

        let res = execute_script_with_inputs(
            exec_script_info.get_eq_script(),
            exec_script_info.witness(),
        );
        assert!(res.success);

        let res = execute_script_with_inputs(
            exec_script_info.get_neq_script(),
            exec_script_info.witness(),
        );
        assert!(!res.success);
    }

    #[test]
    fn test_zps_mul_denominator() {
        let degree = 8; //n
        let log_degree = log2_strict_usize(degree);
        let quotient_degree = 4; //s
        let log_quotient_degree = log2_strict_usize(quotient_degree);

        let mut rng = ChaCha20Rng::seed_from_u64(0u64);

        let zeta = rng.gen::<Challenge>();

        let a = Val::generator().try_inverse().unwrap();

        // let trace_domain = pcs.natural_domain_for_degree(degree);
        let trace_domain = TwoAdicMultiplicativeCoset {
            log_n: log_degree,
            shift: Val::one(),
        };

        let quotient_domain =
            trace_domain.create_disjoint_domain(1 << (log_degree + log_quotient_degree));

        let generator = Val::two_adic_generator(quotient_domain.log_n);

        let quotient_chunks_domains = quotient_domain.split_domains(quotient_degree);

        let quotient_chunk_nums = quotient_chunks_domains.len();

        let zps = quotient_chunks_domains
            .iter()
            .enumerate()
            .map(|(i, domain)| {
                quotient_chunks_domains
                    .iter()
                    .enumerate()
                    .filter(|(j, _)| *j != i)
                    .map(|(_, other_domain)| {
                        other_domain.zp_at_point(zeta)
                            * other_domain.zp_at_point(domain.first_point()).inverse()
                    })
                    .product::<Challenge>()
            })
            .collect_vec();

        let numerators = quotient_chunks_domains
            .iter()
            .enumerate()
            .map(|(i, domain)| {
                quotient_chunks_domains
                    .iter()
                    .enumerate()
                    .filter(|(j, _)| *j != i)
                    .map(|(_, other_domain)| other_domain.zp_at_point(zeta))
                    .product::<Challenge>()
            })
            .collect_vec();

        let mut bc_assigner = DefaultBCAssignment::new();
        let mut exec_script_info = compute_zps_mul_denominator_script::<Val, Challenge>(
            quotient_chunk_nums,
            log_degree,
            generator,
            zps,
            numerators,
        );

        exec_script_info.gen(&mut bc_assigner);

        let res = execute_script_with_inputs(
            exec_script_info.get_eq_script(),
            exec_script_info.witness(),
        );
        assert!(res.success);

        let res = execute_script_with_inputs(
            exec_script_info.get_neq_script(),
            exec_script_info.witness(),
        );
        assert!(!res.success);
    }
}
