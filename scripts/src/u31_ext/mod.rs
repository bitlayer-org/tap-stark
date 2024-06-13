use bitcoin::ScriptBuf as Script;
use bitcoin_script::script;
use p3_field::PrimeField32;

use crate::{pushable, unroll};

mod babybear;
pub use babybear::*;

mod m31;
pub use m31::*;

mod karatsuba;
pub use karatsuba::*;

mod karatsuba_complex;
pub use karatsuba_complex::*;

use crate::u31::{u31_add, u31_double, u31_sub, U31Config};

pub trait U31ExtConfig {
    type BaseFieldConfig: U31Config;
    const DEGREE: u32;

    fn mul_impl() -> Script;
}

pub fn u31ext_add<C: U31ExtConfig>() -> Script {
    script! {
        { unroll(C::DEGREE - 1, |i| {
            let gap = C::DEGREE - i;
            script!{
                { gap } OP_ROLL
                { u31_add::<C::BaseFieldConfig>() }
                OP_TOALTSTACK
        }}) }
        { u31_add::<C::BaseFieldConfig>() }
        { unroll(C::DEGREE - 1, |_| script!{ OP_FROMALTSTACK }) }
    }
}

pub fn u31ext_equalverify<C: U31ExtConfig>() -> Script {
    script! {
        { unroll(C::DEGREE - 1, |i| {
            let gap = C::DEGREE - i;
            script!{
                { gap } OP_ROLL
                OP_EQUALVERIFY
        }}) }
        OP_EQUALVERIFY
    }
}

pub fn u31ext_sub<C: U31ExtConfig>() -> Script {
    script! {
        { unroll(C::DEGREE - 1, |i| {
            let gap = C::DEGREE - i;
            script!{
                { gap } OP_ROLL OP_SWAP
                { u31_sub::<C::BaseFieldConfig>() }
                OP_TOALTSTACK
        }}) }
        { u31_sub::<C::BaseFieldConfig>() }
        { unroll(C::DEGREE - 1, |_| script!{ OP_FROMALTSTACK }) }
    }
}

pub fn u31ext_double<C: U31ExtConfig>() -> Script {
    script! {
        { unroll(C::DEGREE - 1, |_|
            script! {
                { u31_double::<C::BaseFieldConfig>() }
                OP_TOALTSTACK
        })}
        { u31_double::<C::BaseFieldConfig>() }
        { unroll(C::DEGREE - 1, |_| script!{ OP_FROMALTSTACK }) }
    }
}

pub fn u31ext_mul<C: U31ExtConfig>() -> Script {
    C::mul_impl()
}

pub fn ext_fold_degree1<M: U31ExtConfig, F: PrimeField32>(
    degree: u32,
    x: &[F],
    y_0_x: &[F],
    y_0_neg_x: &[F],
    beta: &[F],
    y_1_x_quare: &[F],
) -> Script {
    let x_vec: Vec<u32> = x.into_iter().map(|v| v.as_canonical_u32()).collect();
    let y_0_x_vec: Vec<u32> = y_0_x.into_iter().map(|v| v.as_canonical_u32()).collect();
    let y_0_neg_x_vec: Vec<u32> = y_0_neg_x
        .into_iter()
        .map(|v| v.as_canonical_u32())
        .collect();
    let beta_vec: Vec<u32> = beta.into_iter().map(|v| v.as_canonical_u32()).collect();
    let y_1_x_quare_vec: Vec<u32> = y_1_x_quare
        .into_iter()
        .map(|v| v.as_canonical_u32())
        .collect();
    ext_fold_degree::<M>(
        degree,
        &x_vec,
        &y_0_x_vec,
        &y_0_neg_x_vec,
        &beta_vec,
        &y_1_x_quare_vec,
    )
}

// y_0(r)= g_0,1(r^2) + r g_0,2(r^2)
// y_0(-r)= g_0,1(r^2) -r g_0,2(r^2)
// y_1(r^2) = g_0,1(r^2) + v_0 g_0,2(r^2)
pub fn ext_fold_degree<M: U31ExtConfig>(
    _degree: u32,
    x: &[u32],
    y_0_x: &[u32],
    y_0_neg_x: &[u32],
    beta: &[u32],
    y_1_x_quare: &[u32],
) -> Script {
    script! {

        // calculate 2 * g_0,1(r^2)
        for i in (0..M::DEGREE).rev(){
            {y_0_x[i as usize]}
        }
        for i in (0..M::DEGREE).rev(){
            {y_0_neg_x[i as usize]}
        }
        { u31ext_add::<M>() }
        // calculate 2 * x * g_0,1(r^2)
        for i in (0..M::DEGREE).rev(){
            {x[i as usize]}
        }
        { u31ext_mul::<M>()}

        for _ in 0..M::DEGREE{
            OP_TOALTSTACK
        }

        // calculate 2 * x * g_0,2(r^2)
        for i in (0..M::DEGREE).rev(){
            {y_0_x[i as usize]}
        }
        for i in (0..M::DEGREE).rev(){
            {y_0_neg_x[i as usize]}
        }
        { u31ext_sub::<M>() }
        // calculate 2 * r * beta * g_0,2(r^2)
        for i in (0..M::DEGREE).rev(){
            {beta[i as usize]}
        }
        {u31ext_mul::<M>()}
        // calaulate (2 * r * beta * g_0,2(r^2)) + (2 * r * g_0,1(r^2))
        for _ in 0..M::DEGREE{
            OP_FROMALTSTACK
        }

        { u31ext_add::<M>() }
        for _ in 0..M::DEGREE{
            OP_TOALTSTACK
        }


        // calculate 2*r*y_1(r^2)
        for i in (0..M::DEGREE).rev(){
            {y_1_x_quare[i as usize]}
        }
        {u31ext_double::<M>()}
        for i in (0..M::DEGREE).rev(){
            {x[i as usize]}
        }
        {u31ext_mul::<M>()}

        // Check Equal
        // y_1(r^2) = g_0,1(r^2) + beta g_0,2(r^2)
        // 2r y_1(r^2) = 2r g_0,1(r^2) + 2r beta g_0,2(r^2)
       for _ in 0..M::DEGREE{
            OP_FROMALTSTACK
        }

        { u31ext_equalverify::<BabyBear4>() }
        OP_1
    }
}
