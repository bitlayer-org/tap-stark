use std::marker::PhantomData;

use bitcoin::opcodes::{OP_SUB, OP_TOALTSTACK};
use bitcoin::ScriptBuf as Script;
use bitcoin_script::{define_pushable, script};
use primitives::field::BfField;
use scripts::pseudo::{
    OP_4DUP, OP_4FROMALTSTACK, OP_4MUL, OP_4PICK, OP_4ROLL, OP_4TOALTSTACK, OP_NDUP,
};
use scripts::u31_lib::{
    u31_add, u31_double, u31_mul, u31_sub, u31_sub_u31ext, u31_to_u31ext, u31ext_add,
    u31ext_double, u31ext_equalverify, u31ext_mul, u31ext_mul_u31, u31ext_mul_u31_by_constant,
    u31ext_sub, u31ext_sub_u31, BabyBear4, BabyBearU31,
};

define_pushable!();

// input stack:
//  x  <-- top
//  z
// output stack
// x - z <-- top
pub fn minus<F: BfField>() -> Script {
    script! {
        if F::U32_SIZE == 4{
            {u31ext_sub::<BabyBear4>()}
        }else{
            {u31_sub::<BabyBearU31>()}
        }
    }
}

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
pub fn compute_next_alpha_pow<Challenge: BfField>() -> Script {
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
 *          prev_ro <--top  babybear4
 *          p_at_x_{i}      babybear
 *          p_at_z_{i}      babybear4
 *  output:
 *      altstack:
 *          next_alpha_pow <--top  babybear4
 *          alpha           babybear4
 *      stack:
 *          current_ro = prev_ro + cur_alpha_pow*(p_at_x_{i} - p_at_z_{i})  <--top   babybear4
 */

pub fn alphapow_mul_px_minus_pz<Val: BfField, Challenge: BfField>() -> Script {
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
        //  prev_ro              exists at babybear4
        {u31ext_mul::<BabyBear4>()}
        {u31ext_add::<BabyBear4>()} // accmulate at ro

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
 *          prev_ro         // the prev_ro is 0 when intialization
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
 *          current_ro
 *
 *
*/
pub fn accmulator<Val: BfField, Challenge: BfField>(matrix_width: usize) -> Script {
    assert_eq!(Val::U32_SIZE, 1);
    assert_eq!(Challenge::U32_SIZE, 4);
    script! {
        OP_4TOALTSTACK
        OP_4TOALTSTACK

        for i in 0..matrix_width{
            {alphapow_mul_px_minus_pz::<Val,Challenge>()}
        }
        OP_4FROMALTSTACK
        OP_4FROMALTSTACK

    }
}

pub fn zip<F1: BfField, F2: BfField>(vec1: Vec<F1>, vec2: Vec<F2>) -> Script {
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

struct VerifyQuotinetPoly<Val: BfField, Challenge: BfField> {
    log_height: usize,
    index: usize,
    p_at_x: Vec<Val>,
    x: Val,
    p_at_z: Vec<Val>,
    z: Val,
    prev_ro: Challenge,
    prev_alpha_pow: Challenge,
    _marker: PhantomData<(Val, Challenge)>,
}

impl<Val: BfField, Challenge: BfField> VerifyQuotinetPoly<Val, Challenge> {
    pub fn new(
        log_height: usize,
        index: usize,
        p_at_x: Vec<Val>,
        x: Val,
        p_at_z: Vec<Val>,
        z: Val,
        prev_ro: Challenge,
        prev_alpha_pow: Challenge,
    ) -> Self {
        Self {
            log_height,
            index,
            p_at_x,
            x,
            p_at_z,
            z,
            prev_ro,
            prev_alpha_pow,
            _marker: PhantomData,
        }
    }

    pub fn compute_x(&self) -> Val {
        let x =
            Val::generator() * Val::two_adic_generator(self.log_height).exp_u64(self.index as u64);
        x
    }

    pub fn logic_script() -> Script {
        script! {
            // {compute_next_alpha_pow::<Challenge>()}
        }
    }
}

mod tests {
    use bitcoin::opcodes::{OP_FROMALTSTACK, OP_TRUE};
    use bitcoin::ScriptBuf as Script;
    use bitcoin_script::{define_pushable, script};
    use itertools::izip;
    use p3_dft::{Radix2Dit, TwoAdicSubgroupDft};
    use p3_field::{AbstractExtensionField, AbstractField};
    use p3_interpolation::interpolate_coset;
    use p3_matrix::dense::RowMajorMatrix;
    use p3_matrix::util::reverse_matrix_index_bits;
    use primitives::field::BfField;
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaCha20Rng;
    use scripts::pseudo::{OP_4DROP, OP_4FROMALTSTACK, OP_4TOALTSTACK};
    use scripts::u31_lib::{u31ext_equalverify, BabyBear4};
    use scripts::{execute_script, BabyBear, BinomialExtensionField};

    use crate::fri_scripts::pcs::{
        accmulator, alphapow_mul_px_minus_pz, compute_next_alpha_pow, zip,
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

        // let zip_script = script!{
        //     {zip::<Challenge,Val>(p_at_z_vector,p_at_x_vector)}

        // };

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
    fn test_quotient() {
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

        let acc_script = script! {
            {zip::<Challenge,Val>(p_at_z_vector,p_at_x_vector)}

            {init_ro.as_u32_vec()[3]}{init_ro.as_u32_vec()[2]}{init_ro.as_u32_vec()[1]}{init_ro.as_u32_vec()[0]}

            {init_alpha_pow.as_u32_vec()[3]}{init_alpha_pow.as_u32_vec()[2]}{init_alpha_pow.as_u32_vec()[1]}{init_alpha_pow.as_u32_vec()[0]}

            {alpha.as_u32_vec()[3]}{alpha.as_u32_vec()[2]}{alpha.as_u32_vec()[1]}{alpha.as_u32_vec()[0]}

            {accmulator::<Val,Challenge>(matrix_width)}

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
