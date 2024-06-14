use bitcoin::ScriptBuf as Script;
use bitcoin_script::{define_pushable, script};
use itertools::Itertools;

use super::bit_comm_u32::BitCommitmentU32;
use super::{AsU32Vec, Witness};
define_pushable!();

// BitCommitment
// 1. Create a new BitCommitment through BCAssignment is a better way.
// 2. after run this `execute_script_with_wittness(bc.check_commitment_script(), bc.witness())`,
//    the u32 values should be placed on the stack for any bc.

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct BitCommitment<F: AsU32Vec> {
    pub value: F,
    pub u32_values: Vec<u32>,
    pub commitments: Vec<BitCommitmentU32>,
}

impl<F: AsU32Vec> BitCommitment<F> {
    pub fn new(secret_key: &str, value: F) -> Self {
        let u32_values = value.bc_as_u32_vec();
        let commitments = u32_values
            .iter()
            .map(|v| BitCommitmentU32::new(secret_key, *v))
            .collect_vec();
        Self {
            value,
            u32_values,
            commitments,
        }
    }

    // execute with witness
    // check bitcommitment and left u32_values to alt stack
    pub fn check_and_recover_to_altstack(&self) -> Script {
        self.recover_message_at_altstack()
    }

    // execute with witness
    // check bitcommitment and left u32_values to stack
    pub fn check_and_recover(&self) -> Script {
        script! {
            {self.recover_message_at_altstack()}
            {self.message_from_altstack()}
        }
    }

    pub fn witness(&self) -> Witness {
        self.signature()
    }

    fn message_to_altstack(&self) -> Script {
        script! {
            for _ in 0..self.u32_values.len(){
                OP_TOALTSTACK
            }
        }
    }

    fn message_from_altstack(&self) -> Script {
        script! {
            for _ in 0..self.u32_values.len(){
                OP_FROMALTSTACK
            }
        }
    }

    fn recover_message_at_altstack(&self) -> Script {
        // we must confirm the stack state look like below after the inputs enter to match the recover_message_at_altstack:
        // bit_commits[0].sig  <- top
        // bit_commits[1].sig
        //       ...
        // bit_commits[N].sig
        let script = script! {
            for i in 0..self.u32_values.len(){
                {self.commitments[i].recover_message_at_stack()}
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

    fn signature(&self) -> Vec<Vec<u8>> {
        let mut sigs = Vec::new();
        for i in (0..self.u32_values.len()).rev() {
            sigs.append(&mut self.commitments[i].signature());
        }
        sigs
    }
}
#[cfg(test)]
mod test {

    use core::ops::{Add, Mul, Neg};

    use bitcoin_script::{define_pushable, script};
    use p3_baby_bear::BabyBear;
    use p3_field::{AbstractExtensionField, AbstractField, PrimeField32};
    use primitives::field::BfField;
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaCha20Rng;

    use crate::{
        execute_script, execute_script_with_inputs, u31_equalverify, u31ext_add, u31ext_double,
        u31ext_equalverify, BabyBear4,
    };

    // signuture is the input of this script
    pub fn recover_message_euqal_to_commit_message<F: AsU32Vec>(
        checked: BitCommitment<F>,
    ) -> Script {
        let u32_values = checked.value.bc_as_u32_vec();
        script! {
            {checked.check_and_recover()}
            for i in (0..checked.u32_values.len()).rev(){
                // the value compare sequence: { u32_values[3] } { u32_values[2]} { u32_values[1] } { u32_values[0]}
                {u32_values[i]}
            }

            if checked.u32_values.len() == 1{
                {u31_equalverify()}
            }else {
                {u31ext_equalverify::<BabyBear4>()}
            }
        }
    }

    use super::*;

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
        assert_eq!(exec_result.final_stack.len(), 1);
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
            {recover_message_euqal_to_commit_message(a_commit.clone())}
            OP_1
        };
        let a_sigs = a_commit.witness();
        let exec_result = execute_script_with_inputs(script, a_sigs);
        assert!(exec_result.success);
        assert_eq!(exec_result.final_stack.len(), 1);
    }

    #[test]
    fn test_bit_commit_sig_verify() {
        let mut rng = ChaCha20Rng::seed_from_u64(0u64);
        let mut a = rng.gen::<F>();
        a = BabyBear::from_u32(1u32);
        let a_commit = BitCommitment::new("b138982ce17ac813d505b5b40b665d404e9528e7", a);

        let script = script! {
            {recover_message_euqal_to_commit_message(a_commit.clone())}
            OP_1
        };
        let a_sigs = a_commit.witness();
        let exec_result = execute_script_with_inputs(script, a_sigs);
        assert!(exec_result.success);
        assert_eq!(exec_result.final_stack.len(), 1);
    }
}
