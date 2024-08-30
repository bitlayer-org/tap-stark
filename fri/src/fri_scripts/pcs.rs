use bitcoin::ScriptBuf as Script;
use bitcoin_script::{define_pushable, script};
use itertools::izip;
use primitives::field::BfField;
use script_manager::script_info::ScriptInfo;
use scripts::pseudo::{OP_4DROP, OP_4DUP, OP_4FROMALTSTACK, OP_4ROLL, OP_4TOALTSTACK};
use scripts::u31_lib::{
    u31_mul, u31_sub_u31ext, u31ext_add, u31ext_equalverify, u31ext_mul, u31ext_sub, BabyBear4,
    BabyBearU31,
};

define_pushable!();
/**
 * input
    altstack:
        current_alpha_pow <-- top
        alpha
 * output:
    altstack:
        next_alpha_pow <-- top
        alpha
*/
fn compute_next_alpha_pow<Challenge: BfField>() -> Script {
    script! {
        if Challenge::U32_SIZE == 4{
            OP_4FROMALTSTACK
            OP_4FROMALTSTACK
            OP_4DUP
            OP_4TOALTSTACK
            {u31ext_mul::<BabyBear4>()}
            OP_4TOALTSTACK
        }else{
            OP_FROMALTSTACK
            OP_FROMALTSTACK
            OP_DUP
            OP_TOALTSTACK
            {u31_mul::<BabyBearU31>()}
            OP_TOALTSTACK
        }
    }
}
/**
 * compute  alpha_pow * (p(x) - p(z)) at the same index of column  
 * input:
 *      altstack:
 *          cur_alpha_pow  <--top    babybear4
 *          alpha                     babybear4
 *      stack:
 *          prev_accmulator <--top  babybear4
 *          p_at_x_{i}      babybear
 *          p_at_z_{i}      babybear4
 *  output:
 *      altstack:
 *          next_alpha_pow <--top  babybear4
 *          alpha           babybear4
 *      stack:
 *          accmulator = prev_accmulator + cur_alpha_pow*(p_at_x_{i} - p_at_z_{i})  <--top   babybear4
 */
fn alphapow_mul_px_minus_pz<Val: BfField, Challenge: BfField>() -> Script {
    assert_eq!(Val::U32_SIZE, 1);
    assert_eq!(Challenge::U32_SIZE, 4);
    script! {
        OP_4TOALTSTACK  // prev_ro to altstack
        {u31_sub_u31ext::<BabyBear4>()} // babybear4
        OP_4FROMALTSTACK // prev_ro back to stack
        OP_4FROMALTSTACK // cur_alpha_pow to stack
        OP_4DUP
        OP_4TOALTSTACK

        8 OP_4ROLL // places p(x)-p(z) at the top of the stack
        //
        //  expect stack:
        //  p(x) - p(z)  <--top  exists at babybear4
        //  alpha_pow            exists at babybear4
        //  prev_accmulator              exists at babybear4
        {u31ext_mul::<BabyBear4>()}
        {u31ext_add::<BabyBear4>()} // accmulate at accmulator

        {compute_next_alpha_pow::<Challenge>()} // babybear4
    }
}

/**
 * compute:
 * alpha_pow_0 * (p_at_x_0 - p_at_z_0) +   
 * alpha_pow_1  (p_at_x_1 - p_at_z_1) +
 *             ...
 * alpha_pow_i (p_at_x_i - p_at_z_i)
 *         output: alpha_pow_i , res1
 *
 *
 * input:
 *      altstack:
 *          empty
 *      stack:
 *          alpha  
 *          prev_alpha_pow  // the prev_alpha_pow is 1 when intialization
 *          p_at_x_{0..0}
 *          p_at_z_{0..0}
 *               ...
 *          p_at_x_{0..matrix_width}
 *          p_at_z_{0..matrix_width}
 *
 * output
 *      altstack:
 *      stack:
 *          alpha
 *          next_alpha_pow
 *          accmulator
 *
 *
*/
fn compute_accmulator<Val: BfField, Challenge: BfField>(matrix_width: usize) -> Script {
    assert_eq!(Val::U32_SIZE, 1);
    assert_eq!(Challenge::U32_SIZE, 4);
    script! {
        OP_4TOALTSTACK
        OP_4TOALTSTACK

        OP_0 OP_0 OP_0 OP_0  // the accmulator is 0 when intialization
        for i in 0..matrix_width{
            {alphapow_mul_px_minus_pz::<Val,Challenge>()}
        }
        OP_4FROMALTSTACK
        OP_4FROMALTSTACK

    }
}

pub fn accmulator_script<Val: BfField, Challenge: BfField>(
    alpha: Challenge,
    prev_alpha_pow: Challenge,
    p_at_x_row: Vec<Val>,
    p_at_z_row: Vec<Challenge>,
    next_alpha_pow: Challenge,
    accmulator: Challenge,
) -> ScriptInfo {
    assert_eq!(p_at_x_row.len(), p_at_z_row.len());
    let mut si = ScriptInfo::new(
        "compute_accmulator",
        compute_accmulator::<Val, Challenge>(p_at_x_row.len()),
    );
    si.add_input(alpha).add_input(prev_alpha_pow);
    for (px, pz) in izip!(p_at_x_row.clone(), p_at_z_row.clone()) {
        si.add_input(px).add_input(pz);
    }
    si.add_output(alpha)
        .add_output(next_alpha_pow)
        .add_output(accmulator);
    si
}

fn zip<F1: BfField, F2: BfField>(vec1: Vec<F1>, vec2: Vec<F2>) -> Script {
    assert_eq!(vec1.len(), vec2.len());
    script! {
        for i in (0..vec1.len()).rev(){
            for j in (0..F1::U32_SIZE).rev(){
                {vec1[i].as_u32_vec()[j]}
            }
            for j in (0..F2::U32_SIZE).rev(){
                {vec2[i].as_u32_vec()[j]}
            }
        }
    }
}

/**
 *
 * compute:
 *  (ro_final - ro_prev) * (x - z)
 *
 * input:
 *   stack:  
 *     ro_prev    // babybear4
 *     ro_final   // babybear4
 *     x          // babybear
 *     z          // babybear4
 *
 * output:
 *   stack:
 *     accmulator = (ro_final - ro_prev) * (x - z)   // babybear4
 */
fn ro_mul_x_minus_z() -> Script {
    script! {
        {u31ext_sub::<BabyBear4>()} // ro_final-ro_prev
        OP_4TOALTSTACK

        {u31_sub_u31ext::<BabyBear4>()}
        OP_4FROMALTSTACK

        {u31ext_mul::<BabyBear4>()}
    }
}

pub fn ro_mul_x_minus_z_script<Val: BfField, Challenge: BfField>(
    ro_prev: Challenge,
    ro_final: Challenge,
    x: Val,
    z: Challenge,
    accmulator: Challenge,
) -> ScriptInfo {
    let mut si = ScriptInfo::new("ro_mul_x_minus_z", ro_mul_x_minus_z());
    si.add_input(ro_prev)
        .add_input(ro_final)
        .add_input(x)
        .add_input(z)
        .add_output(accmulator);
    si
}

//
// Compute:
//   (ro_final - ro_prev) * (x - z) == accumulator
//
// Input:
//   Stack:
//     --------- accumulator input ---------
//     alpha
//     prev_alpha_pow          // the prev_alpha_pow is 1 during initialization
//     p_at_x_{0..0}
//     p_at_z_{0..0}
//           ...
//     p_at_x_{0..matrix_width}
//     p_at_z_{0..matrix_width}
//     --------- ro_mul_x_minus_z input ---------
//     ro_prev    // babybear4
//     ro_final   // babybear4
//     x          // babybear
//     z          // babybear4
//
//   final_alpha_pow
// Output:
//   Stack:
//     alpha
//     next_alpha_pow
//     accumulator
//
//     (ro_final - ro_prev) * (x - z)   // babybear4
//
//
pub fn verify_quotient<Val: BfField, Challenge: BfField>(matrix_width: usize) -> Script {
    script! {
        {compute_accmulator::<Val,Challenge>(matrix_width)}

        // * output:
        // *   stack:
        // *     accmulator      babybear4
        // *     alpha           babybear4
        // *     next_alpha_pow   babybear4
        // *     ro_prev    babybear4
        // *     ro_final   babybear4
        // *     x          babybear
        // *     z          babybear4
        // *
        // *     final_alpha_pow
        OP_4TOALTSTACK
        OP_4TOALTSTACK
        OP_4TOALTSTACK

        {ro_mul_x_minus_z()}

        // verify accmulator
        OP_4FROMALTSTACK  // back accmulator to stack
        {u31ext_equalverify::<BabyBear4>()}

        OP_4FROMALTSTACK  // back next_alpha_pow to stack
        {u31ext_equalverify::<BabyBear4>()} // verify next_alpha_pow == final_alpha_pow

        OP_4FROMALTSTACK
        OP_4DROP // drop alpha

        OP_TRUE
    }
}

#[cfg(test)]
mod tests {
    
    use bitcoin_script::{define_pushable, script};
    use itertools::izip;
    
    use p3_field::AbstractField;
    
    
    
    use primitives::field::BfField;
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaCha20Rng;
    use script_manager::bc_assignment::DefaultBCAssignment;
    use scripts::pseudo::{OP_4FROMALTSTACK, OP_4TOALTSTACK};
    use scripts::u31_lib::{u31ext_equalverify, BabyBear4};
    use scripts::{execute_script, execute_script_with_inputs, BabyBear, BinomialExtensionField};

    use crate::fri_scripts::pcs::{
        accmulator_script, alphapow_mul_px_minus_pz, compute_accmulator, compute_next_alpha_pow,
        zip,
    };

    define_pushable!();

    #[test]
    fn test_alpha_pow_mul_px_minus_pz() {
        type Challenge = BinomialExtensionField<BabyBear, 4>;
        type Val = BabyBear;

        let mut rng = ChaCha20Rng::seed_from_u64(0u64);

        let index: usize = 1;
        let x = Val::generator();
        let z = Challenge::generator();
        let matrix_width: usize = 3;
        let p_at_x_vector = vec![rng.gen::<Val>()];
        let p_at_z_vector = vec![rng.gen::<Challenge>()];
        let alpha = Challenge::two();
        let init_alpha_pow = Challenge::one();
        let init_ro = Challenge::zero();

        let mut cur_alpha_pow = init_alpha_pow.clone();
        let mut cur_ro = init_ro.clone();
        for (p_at_x, p_at_z) in izip!(p_at_x_vector.clone(), p_at_z_vector.clone()) {
            cur_ro += cur_alpha_pow.clone() * (-p_at_z + p_at_x);
            cur_alpha_pow = cur_alpha_pow * alpha;
        }

        let compute_alpha_pow_script = script! {
            {alpha.as_u32_vec()[3]}{alpha.as_u32_vec()[2]}{alpha.as_u32_vec()[1]}{alpha.as_u32_vec()[0]}
            OP_4TOALTSTACK

            {init_alpha_pow.as_u32_vec()[3]}{init_alpha_pow.as_u32_vec()[2]}{init_alpha_pow.as_u32_vec()[1]}{init_alpha_pow.as_u32_vec()[0]}
            OP_4TOALTSTACK

            {compute_next_alpha_pow::<Challenge>()}

            OP_4FROMALTSTACK
            {alpha.as_u32_vec()[3]}{alpha.as_u32_vec()[2]}{alpha.as_u32_vec()[1]}{alpha.as_u32_vec()[0]}
            {u31ext_equalverify::<BabyBear4>()}

            OP_4FROMALTSTACK
            {alpha.as_u32_vec()[3]}{alpha.as_u32_vec()[2]}{alpha.as_u32_vec()[1]}{alpha.as_u32_vec()[0]}
            {u31ext_equalverify::<BabyBear4>()}

            OP_TRUE
        };

        let res = execute_script(compute_alpha_pow_script);
        if !res.success {
            println!("{:?}", res);
        }
        assert!(res.success);

        // let cur_ro = init_ro + init_alpha_pow * (-p_at_z_vector[0] + p_at_x_vector[0]);
        let alphapow_mul_px_minus_pz_script = script! {
            {alpha.as_u32_vec()[3]}{alpha.as_u32_vec()[2]}{alpha.as_u32_vec()[1]}{alpha.as_u32_vec()[0]}
            OP_4TOALTSTACK

            {init_alpha_pow.as_u32_vec()[3]}{init_alpha_pow.as_u32_vec()[2]}{init_alpha_pow.as_u32_vec()[1]}{init_alpha_pow.as_u32_vec()[0]}
            OP_4TOALTSTACK

            {p_at_z_vector[0].as_u32_vec()[3]}{p_at_z_vector[0].as_u32_vec()[2]}{p_at_z_vector[0].as_u32_vec()[1]}{p_at_z_vector[0].as_u32_vec()[0]}
            {p_at_x_vector[0].as_u32_vec()[0]}

            {init_ro.as_u32_vec()[3]}{init_ro.as_u32_vec()[2]}{init_ro.as_u32_vec()[1]}{init_ro.as_u32_vec()[0]}
            {alphapow_mul_px_minus_pz::<Val,Challenge>()}

            {cur_ro.as_u32_vec()[3]}{cur_ro.as_u32_vec()[2]}{cur_ro.as_u32_vec()[1]}{cur_ro.as_u32_vec()[0]}
            {u31ext_equalverify::<BabyBear4>()}

            OP_4FROMALTSTACK
            {cur_alpha_pow.as_u32_vec()[3]}{cur_alpha_pow.as_u32_vec()[2]}{cur_alpha_pow.as_u32_vec()[1]}{cur_alpha_pow.as_u32_vec()[0]}
            {u31ext_equalverify::<BabyBear4>()}

            OP_4FROMALTSTACK
            {alpha.as_u32_vec()[3]}{alpha.as_u32_vec()[2]}{alpha.as_u32_vec()[1]}{alpha.as_u32_vec()[0]}
            {u31ext_equalverify::<BabyBear4>()}

            OP_TRUE
        };

        let res = execute_script(alphapow_mul_px_minus_pz_script);
        if !res.success {
            println!("{:?}", res);
        }
        assert!(res.success);
    }

    #[test]
    fn test_accmulator() {
        type Challenge = BinomialExtensionField<BabyBear, 4>;
        type Val = BabyBear;

        let mut rng = ChaCha20Rng::seed_from_u64(0u64);

        let index: usize = 1;
        let x = Val::generator();
        let z = Challenge::generator();
        let matrix_width: usize = 3;
        let p_at_x_vector = vec![rng.gen::<Val>(), rng.gen::<Val>(), rng.gen::<Val>()];
        let p_at_z_vector = vec![
            rng.gen::<Challenge>(),
            rng.gen::<Challenge>(),
            rng.gen::<Challenge>(),
        ];
        let alpha = Challenge::two();
        let init_alpha_pow = Challenge::one();
        let init_ro = Challenge::zero();

        let mut cur_alpha_pow = init_alpha_pow.clone();
        let mut cur_ro = init_ro.clone();
        for (p_at_x, p_at_z) in izip!(p_at_x_vector.clone(), p_at_z_vector.clone()) {
            cur_ro += cur_alpha_pow.clone() * (-p_at_z + p_at_x);
            cur_alpha_pow = cur_alpha_pow * alpha;
        }

        let mut bc_assigner = DefaultBCAssignment::new();
        let mut exec_script_info = accmulator_script::<Val, Challenge>(
            alpha,
            init_alpha_pow,
            p_at_x_vector.clone(),
            p_at_z_vector.clone(),
            cur_alpha_pow,
            cur_ro,
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

        let acc_script = script! {
            {zip::<Challenge,Val>(p_at_z_vector,p_at_x_vector)}

            {init_alpha_pow.as_u32_vec()[3]}{init_alpha_pow.as_u32_vec()[2]}{init_alpha_pow.as_u32_vec()[1]}{init_alpha_pow.as_u32_vec()[0]}

            {alpha.as_u32_vec()[3]}{alpha.as_u32_vec()[2]}{alpha.as_u32_vec()[1]}{alpha.as_u32_vec()[0]}

            {compute_accmulator::<Val,Challenge>(matrix_width)}

            {alpha.as_u32_vec()[3]}{alpha.as_u32_vec()[2]}{alpha.as_u32_vec()[1]}{alpha.as_u32_vec()[0]}
            {u31ext_equalverify::<BabyBear4>()}

            {cur_alpha_pow.as_u32_vec()[3]}{cur_alpha_pow.as_u32_vec()[2]}{cur_alpha_pow.as_u32_vec()[1]}{cur_alpha_pow.as_u32_vec()[0]}
            {u31ext_equalverify::<BabyBear4>()}

            {cur_ro.as_u32_vec()[3]}{cur_ro.as_u32_vec()[2]}{cur_ro.as_u32_vec()[1]}{cur_ro.as_u32_vec()[0]}
            {u31ext_equalverify::<BabyBear4>()}

            OP_TRUE
        };

        let res = execute_script(acc_script);
        if !res.success {
            println!("{:?}", res);
        }
        assert!(res.success);

        // let dft = Radix2Dit::default();
        // let log_height:usize = 3;
        // let matrix_width:usize = 4;
        // let poly_len:usize = matrix_width *2^log_height;
        // let log_blowup = 1;
        // let mut rng = ChaCha20Rng::seed_from_u64(0);
        // let evals = RowMajorMatrix::<Val>::rand_nonzero(&mut rng, 1 << log_height, matrix_width);
        // let shift = Val::generator();
        // let mut lde = dft.coset_lde_batch(evals, log_blowup, shift);
        // reverse_matrix_index_bits(&mut lde);

        // interpolate_coset(lde, shift, point)
        // let (low_coset,_) = lde.split_at(matr);
    }
}
