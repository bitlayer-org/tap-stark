pub mod bc_assign;
pub use bc_assign::*;

use bitcoin::opcodes::OP_EQUALVERIFY;
use bitcoin::ScriptBuf as Script;
use bitcoin_script::{define_pushable, script};
use itertools::Itertools;

use scripts::bit_comm_u32::*;
use  crate::field::*;
use scripts::{u31_equalverify, u31ext_equalverify, BabyBear4};
define_pushable!();

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct BitCommitment<F: BfField> {
    pub value: F,
    pub commitments: Vec<BitCommitmentU32>,
}

impl<F: BfField> BitCommitment<F> {
    pub fn new(secret_key: &str, value: F) -> Self {
        let u32_values = value.as_u32_vec();
        let commitments = u32_values
            .iter()
            .map(|v| BitCommitmentU32::new(secret_key, *v))
            .collect_vec();
        Self { value, commitments }
    }

    pub fn message_to_altstack(&self) -> Script {
        script! {
            for _ in 0..F::U32_SIZE{
                OP_TOALTSTACK
            }
        }
    }

    pub fn message_from_altstack(&self) -> Script {
        script! {
            for _ in 0..F::U32_SIZE{
                OP_FROMALTSTACK
            }
        }
    }
}

impl<F: BfField> BitCommitment<F> {
    pub fn recover_message_at_stack(&self) -> Script {
        // we must confirm the stack state look like below after the inputs enter to match the complete_script:
        // bit_commits[0].sig  <- top
        // bit_commits[1].sig
        //       ...
        // bit_commits[N].sig
        let script = script! {
            for i in 0..(F::U32_SIZE-1){
                {self.commitments[i].recover_message_euqal_to_commit_message()}
                {self.commitments[i].value}
                OP_TOALTSTACK
            }

            {self.commitments[F::U32_SIZE-1].recover_message_euqal_to_commit_message()}
            {self.commitments[F::U32_SIZE-1].value}

            for _ in 0..(F::U32_SIZE-1){
                OP_FROMALTSTACK
            }
            // The stake state looks like below:
            // EF.slice(0)  <- top
            // EF.slice(1)
            //    ...
            // EF.slice(EF::D-1)
        };
        script
    }

    pub fn recover_message_at_altstack(&self) -> Script {
        // we must confirm the stack state look like below after the inputs enter to match the recover_message_at_altstack:
        // bit_commits[0].sig  <- top
        // bit_commits[1].sig
        //       ...
        // bit_commits[N].sig
        let script = script! {
            for i in 0..F::U32_SIZE{
                {self.commitments[i].recover_message_euqal_to_commit_message()}
                {self.commitments[i].value}
                OP_TOALTSTACK
            }

            // The altstake state looks like below:
            // EF.slice(EF::D-1)  <- top
            // EF.slice(EF::D-2)
            //    ...
            // EF.slice(1)
        };
        script
    }

    // signuture is the input of this script
    pub fn recover_message_euqal_to_commit_message(&self) -> Script {
        let u32_values = self.value.as_u32_vec();
        script! {
            {self.recover_message_at_stack()}
            for i in (0..F::U32_SIZE).rev(){
                // the value compare sequence: { u32_values[3] } { u32_values[2]} { u32_values[1] } { u32_values[0]}
                {u32_values[i]}
            }

            if F::U32_SIZE == 1{
                {u31_equalverify()}
            }else {
                {u31ext_equalverify::<BabyBear4>()}
            }
        }
    }

    pub fn signature(&self) -> Vec<Vec<u8>> {
        let mut sigs = Vec::new();
        for i in (0..F::U32_SIZE).rev() {
            sigs.append(&mut self.commitments[i].signature());
        }
        sigs
    }
}
#[cfg(test)]
mod test {

    use core::ops::{Add, Mul, Neg};

    use p3_baby_bear::BabyBear;
    use p3_field::{AbstractExtensionField, AbstractField, PrimeField32};
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaCha20Rng;

    use super::*;
    use scripts::{
        execute_script, execute_script_with_inputs, u31ext_add, u31ext_double, u31ext_equalverify,
        BabyBear4,
    };

    type F = BabyBear;
    type EF = p3_field::extension::BinomialExtensionField<BabyBear, 4>;

    #[test]
    fn test_extension_bit_commit() {
        let mut rng = ChaCha20Rng::seed_from_u64(0u64);
        eprintln!("babybear4 add: {}", u31ext_add::<BabyBear4>().len());

        let a = rng.gen::<EF>();
        let b = rng.gen::<EF>();
        let a_commit = BitCommitment::new("b138982ce17ac813d505b5b40b665d404e9528e7", a);
        let b_commit = BitCommitment::new("b138982ce17ac813d505b5b40b665d404e9528e6", b);

        let c = a.add(b);

        let a: &[F] = a.as_base_slice();
        let b: &[F] = b.as_base_slice();
        let c: &[F] = c.as_base_slice();
        let script = script! {
            { a[3].as_canonical_u32() } { a[2].as_canonical_u32() } { a[1].as_canonical_u32() } { a[0].as_canonical_u32() }
            { b[3].as_canonical_u32() } { b[2].as_canonical_u32() } { b[1].as_canonical_u32() } { b[0].as_canonical_u32() }
            { u31ext_add::<BabyBear4>() }
            { c[3].as_canonical_u32() } { c[2].as_canonical_u32() } { c[1].as_canonical_u32() } { c[0].as_canonical_u32() }
            { u31ext_equalverify::<BabyBear4>() }
            OP_PUSHNUM_1
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);

        let script = script! {
            { a_commit.recover_message_at_altstack() }
            { b_commit.recover_message_at_altstack() }
            { b_commit.message_from_altstack()}
            { a_commit.message_from_altstack()}
            { u31ext_add::<BabyBear4>() }
            { c[3].as_canonical_u32() } { c[2].as_canonical_u32() } { c[1].as_canonical_u32() } { c[0].as_canonical_u32() }
            { u31ext_equalverify::<BabyBear4>() }
            OP_1
        };
        let mut a_sigs = a_commit.signature();
        let mut b_sigs: Vec<Vec<u8>> = b_commit.signature();
        b_sigs.append(&mut a_sigs);
        let exec_result = execute_script_with_inputs(script, b_sigs);
        assert!(exec_result.success);
    }

    #[test]
    fn test_extension_bit_commit_sig_verify() {
        let mut rng = ChaCha20Rng::seed_from_u64(0u64);
        let mut a = rng.gen::<EF>();
        a = EF::from_base_slice(
            vec![
                BabyBear::from_u32(1u32),
                BabyBear::from_u32(2u32),
                BabyBear::from_u32(3u32),
                BabyBear::from_u32(4u32),
            ]
            .as_slice(),
        );
        let a_commit = BitCommitment::new("b138982ce17ac813d505b5b40b665d404e9528e7", a);

        let script = script! {
            {a_commit.recover_message_euqal_to_commit_message()}
            OP_1
        };
        let a_sigs = a_commit.signature();
        let exec_result = execute_script_with_inputs(script, a_sigs);
        assert!(exec_result.success);
    }

    #[test]
    fn test_bit_commit_sig_verify() {
        let mut rng = ChaCha20Rng::seed_from_u64(0u64);
        let mut a = rng.gen::<F>();
        a = BabyBear::from_u32(1u32);
        let a_commit = BitCommitment::new("b138982ce17ac813d505b5b40b665d404e9528e7", a);

        let script = script! {
            {a_commit.recover_message_euqal_to_commit_message()}
            OP_1
        };
        let a_sigs = a_commit.signature();
        let exec_result = execute_script_with_inputs(script, a_sigs);
        assert!(exec_result.success);
    }
}
