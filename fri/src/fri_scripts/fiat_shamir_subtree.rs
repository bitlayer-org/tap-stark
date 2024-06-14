use std::usize;

use bitcoin::opcodes::{
    OP_2SWAP, OP_DROP, OP_ENDIF, OP_EQUALVERIFY, OP_FROMALTSTACK, OP_GREATERTHAN,
    OP_GREATERTHANOREQUAL, OP_LESSTHAN, OP_LESSTHANOREQUAL, OP_PICK, OP_RESERVED2, OP_SUB, OP_SWAP,
    OP_TOALTSTACK,
};
use bitcoin::script::{self, scriptint_vec};
use bitcoin::ScriptBuf as Script;
use bitcoin_script::{define_pushable, script};
use itertools::Itertools;
use p3_field::PrimeField32;
use primitives::bit_comm::{BCAssignment, BitCommitment};
use primitives::challenger::chan_field::{PermutationField, PermutationField, U32, U32};
use primitives::challenger::{
    BfChallenger, BfChallenger, BitExtractor, BitExtractor, Blake3Permutation, Blake3Permutation,
};
use primitives::field::BfField;
use script_manager::bc_assignment::ThreadBCAssignment;
use scripts::bit_comm::bit_comm::BitCommitment;
use scripts::bit_comm_u32::*;
use scripts::pseudo::{
    OP_4DROP, OP_4DROP, OP_4FROMALTSTACK, OP_4FROMALTSTACK, OP_4TOALTSTACK, OP_4TOALTSTACK,
};
use scripts::u32_rrot::{u32_rrot, u32_rrot, u8_extract_hbit, u8_extract_hbit};
use scripts::u32_std::{
    u32_compress, u32_compress, u32_equal, u32_equal, u32_equalverify, u32_equalverify, u32_push,
    u32_push,
};
use scripts::{blake3, BabyBearU31};

/// fiat shamir subtree contains a series script leafs and coressponding
trait SubTree {
    fn locking_leafs(&self) -> Vec<Script>;
    fn unlock_witnesses(&self) -> Vec<Vec<Vec<u8>>>; // will fail to run, because each leaf is correct !
}

#[derive(Clone, Debug)]
struct Commit {
    locking_script: Script,
    unlock_witness: Vec<Vec<u8>>,
}

/// This subtree includes a series of bitcoin scripts for challenging the FS-transform.
#[derive(Default)]
struct FiatShamirSubTree<F>
where
    F: BfField,
{
    // inner construct from FriChanllenger
    inputs: Vec<[U32; 16]>,
    outputs: Vec<[U32; 8]>,

    // commit inner state from inputs and outputs
    input_commits: Vec<[Commit; 16]>,
    output_commits: Vec<[Commit; 8]>,

    state_leafs_num: u32,

    // sample inputs and outpus
    sample_inputs: Vec<Vec<U32>>,
    sample_outputs: Vec<F>,

    sample_input_commits: Vec<Vec<Commit>>,
    sample_output_commits: Vec<Commit>,

    sample_leafs_num: u32,

    // pow check
    grind_bits: Option<usize>,
    grind_out: F,
    grind_commit: Vec<Commit>,
    grind_leaf_idx: u32,
}

impl<F> FiatShamirSubTree<F>
where
    F: BfField + BitExtractor,
{
    /// currently just implement Blake3Permuation with U32;16
    fn new_from_fri_challenger(
        challenger: &BfChallenger<F, U32, Blake3Permutation, 16>,
        bc_assignment: &mut ThreadBCAssignment,
    ) -> FiatShamirSubTree<F> {
        assert_eq!(
            challenger.permutation_input_records.len(),
            challenger.permutation_output_records.len()
        );

        let state_length = challenger.permutation_input_records.len();

        assert_eq!(
            challenger.sample_input.len(),
            challenger.sample_output.len()
        );
        let sample_length = challenger.sample_input.len();

        let mut fs_subtree = FiatShamirSubTree::<F> {
            inputs: vec![],
            outputs: vec![],
            input_commits: vec![],
            output_commits: vec![],
            state_leafs_num: state_length as u32,

            sample_inputs: vec![],
            sample_outputs: vec![],
            sample_input_commits: vec![],
            sample_output_commits: vec![],
            sample_leafs_num: sample_length as u32,

            grind_bits: challenger.grind_bits,
            grind_out: challenger.grind_output,
            grind_commit: vec![],
            grind_leaf_idx: state_length as u32 + sample_length as u32,
        };

        for idx in 0..state_length {
            fs_subtree.inputs.push(
                challenger.permutation_input_records[idx]
                    .clone()
                    .try_into()
                    .unwrap(),
            );

            fs_subtree.outputs.push(
                challenger.permutation_output_records[idx]
                    .clone()
                    .try_into()
                    .unwrap(),
            );
        }

        for idx in 0..sample_length {
            fs_subtree
                .sample_inputs
                .push(challenger.sample_input[idx].clone());
            fs_subtree
                .sample_outputs
                .push(challenger.sample_output[idx]);
        }

        fs_subtree.commit(bc_assignment);

        fs_subtree
    }

    fn commit(&mut self, bc_assignment: &mut ThreadBCAssignment) {
        self.input_commits.clear();
        self.output_commits.clear();
        self.sample_input_commits.clear();
        self.sample_output_commits.clear();

        assert_eq!(self.inputs.len(), self.outputs.len());
        assert_eq!(self.inputs.len(), self.state_leafs_num as usize);

        for idx in 0..self.state_leafs_num as usize {
            let input_commit: [Commit; 16] = (0..16)
                .map(|i| new_u32_bit_commit(bc_assignment, self.inputs[idx][i]))
                .collect_vec()
                .try_into()
                .unwrap();
            self.input_commits.push(input_commit);
            let output_commit: [Commit; 8] = (0..8)
                .map(|i| new_u32_bit_commit(bc_assignment, self.outputs[idx][i]))
                .collect_vec()
                .try_into()
                .unwrap();
            self.output_commits.push(output_commit);
        }

        for idx in 0..self.sample_leafs_num as usize {
            self.sample_input_commits.push(
                self.sample_inputs[idx]
                    .clone()
                    .into_iter()
                    .map(|x| new_u32_bit_commit(bc_assignment, x))
                    .collect(),
            );
            self.sample_output_commits.push(new_challenge_commit(
                bc_assignment,
                self.sample_outputs[idx],
            ));
        }

        self.grind_commit
            .push(new_challenge_commit(bc_assignment, self.grind_out));
    }
}

// let input_commit = new_u32_bit_commit(self.inputs[idx]);
// let output_commit = new_u32_bit_commit(self.outputs[idx]);

// for each leaf, unlock script:
//
// input_bitCommitment_preimage
// output_bitCommitment_preimage
//
// for each leaf, locking script:
//
// output_bitCommitment
// verify
// input_bitCommitment
// verify
// verify blake3 with input and output

// return locking

fn U32_to_u32(input: U32) -> u32 {
    u32::from_le_bytes(input.as_u8_array())
}

// extend to babybear
// TODO: extend to babybear extension
fn u32_to_compressed_babybear() -> Script {
    script!(
        u32_compress
        // if u32 is less than 0
        OP_DUP 0 OP_LESSTHAN
        OP_IF
        OP_ABS
        {0x7ffffff}
        OP_ADD
        OP_ENDIF
        // if u32 is more than 0
        OP_DUP {0x78000001} OP_GREATERTHANOREQUAL
        OP_IF
        {0x78000001}
        OP_SUB
        OP_ENDIF
    )
}

fn new_u32_bit_commit(bc_assignment: &mut ThreadBCAssignment, value: U32) -> Commit {
    let mut bitcommit = bc_assignment.assign(U32_to_u32(value));
    let locking = script! {
        { bitcommit.commitments.get(0).unwrap().checksig_verify_script() }
    };
    Commit {
        locking_script: locking,
        unlock_witness: bitcommit.witness(),
    }
}

fn new_challenge_commit<F>(bc_assignment: &mut ThreadBCAssignment, value: F) -> Commit
where
    F: BfField,
{
    let bitcommit: BitCommitment<F> = bc_assignment.assign(value);
    let locking = script! {
        { bitcommit.check_and_recover() }
    };
    Commit {
        locking_script: locking,
        unlock_witness: bitcommit.witness(),
    }
}

impl<F> SubTree for FiatShamirSubTree<F>
where
    F: BfField,
{
    fn locking_leafs(&self) -> Vec<Script> {
        let mut output: Vec<Script> = vec![];
        for idx in 0..self.state_leafs_num {
            output.push(script! {
                // verify OutputCommit
                for i in 0..8 {
                    {self.output_commits[idx as usize][i].clone().locking_script}
                    OP_4TOALTSTACK
                }

                // verify InputCommit
                for i in 0..16 {
                    {self.input_commits[idx as usize][i].clone().locking_script}
                    OP_4TOALTSTACK
                }

                // pop input from alt stack
                for _ in 0..16 {
                    OP_4FROMALTSTACK
                }

                // blake3 verify
                {blake3::blake3_var_length(64)}

                // pop and check output from alt stack
                for _ in 0..8 {
                    OP_4FROMALTSTACK
                    u32_equalverify
                }

                OP_1
            });
        }

        for idx in 0..self.sample_leafs_num {
            output.push(script! {
                // verify OutputCommit
                {self.sample_output_commits[idx as usize].clone().locking_script}
                for _ in 0..F::U32_SIZE {
                    OP_TOALTSTACK
                }

                // verify InputCommit
                for i in 0..self.sample_input_commits[idx as usize].len() {
                    {self.sample_input_commits[idx as usize][i].clone().locking_script}
                    u32_to_compressed_babybear
                    OP_TOALTSTACK
                }

                for _ in 0..self.sample_input_commits[idx as usize].len() {
                    OP_FROMALTSTACK
                }

                if F::U32_SIZE == 4 {
                    OP_SWAP
                    OP_2SWAP
                    OP_SWAP
                }

                for _ in 0..F::U32_SIZE {
                    OP_FROMALTSTACK
                    OP_EQUALVERIFY
                }

                OP_1
            });
        }

        match self.grind_bits {
            Some(zero_bits) => output.push(script! {
                {self.grind_commit.first().unwrap().clone().locking_script}

                {(1<<(32-zero_bits))-1}
                OP_LESSTHANOREQUAL

                OP_TOALTSTACK

                for _ in 0..F::U32_SIZE-1 {
                    OP_DROP
                }

                OP_FROMALTSTACK

            }),
            None => {}
        }

        output
    }

    fn unlock_witnesses(&self) -> Vec<Vec<Vec<u8>>> {
        let mut output: Vec<Vec<Vec<u8>>> = vec![];
        for idx in 0..self.state_leafs_num {
            let mut witness: Vec<Vec<u8>> = vec![];
            // input bitCommitment preimage
            for i in 0..16 {
                witness.extend(
                    self.input_commits[idx as usize][15 - i]
                        .clone()
                        .unlock_witness,
                );
            }
            // output bitCommitment preimage
            for i in 0..8 {
                witness.extend(
                    self.output_commits[idx as usize][7 - i]
                        .clone()
                        .unlock_witness,
                );
            }
            output.push(witness);
        }

        for idx in 0..self.sample_leafs_num {
            let mut witness: Vec<Vec<u8>> = vec![];
            let sample_input_commits_length = self.sample_input_commits[idx as usize].len();
            // input bitCommitment preimage
            for i in 0..sample_input_commits_length {
                witness.extend(
                    self.sample_input_commits[idx as usize][sample_input_commits_length - 1 - i]
                        .clone()
                        .unlock_witness,
                );
            }

            // output bitCommitment preimage
            witness.extend(
                self.sample_output_commits[idx as usize]
                    .clone()
                    .unlock_witness,
            );
            output.push(witness);
        }

        match self.grind_bits {
            Some(_) => {
                let mut witness: Vec<Vec<u8>> = vec![];
                witness.extend(self.grind_commit.first().unwrap().clone().unlock_witness);
                output.push(witness);
            }
            None => {}
        }

        output
    }
}

#[cfg(test)]
mod test {
    use std::fmt::Debug;

    use bitcoin::opcodes::OP_EQUALVERIFY;
    use bitcoin::{OutPoint, ScriptBuf as Script};
    use bitcoin_script::{define_pushable, script};
    use itertools::Itertools;
    use p3_baby_bear::BabyBear;
    use p3_challenger::{CanObserve, CanSample, CanSampleBits};
    use p3_field::extension::BinomialExtensionField;
    use p3_field::{AbstractField, PrimeField32};
    use primitives::bit_comm::BCAssignment;
    use primitives::challenger::chan_field::{PermutationField, PermutationField, U32, U32};
    use primitives::challenger::{
        BfChallenger, BfChallenger, BfGrindingChallenger, BfGrindingChallenger, Blake3Permutation,
        Blake3Permutation,
    };
    use script_manager::bc_assignment::ThreadBCAssignment;
    use scripts::bit_comm::pushable;
    use scripts::bit_comm::winternitz::{pushable, to_digits};
    use scripts::u31_lib::BabyBear4;
    use scripts::{
        execute_script, execute_script_with_inputs, execute_script_with_inputs, to_digits,
    };

    use super::{new_challenge_commit, new_u32_bit_commit, Commit, FiatShamirSubTree, SubTree};

    fn verify_u32_4bytes_script(value: u32) -> Script {
        let message = to_digits(value, 8);
        let mut commit_message = vec![0u8; 8 / 2];
        for i in 0..8 / 2 {
            let index = 8 / 2 - 1 - i;
            commit_message[i] = message[2 * index] ^ (message[2 * index + 1] << 4);
        }
        script! {
            for i in 0..4{
                {commit_message[ 8 / 2 - 1 - i]} OP_EQUALVERIFY
            }
        }
    }

    #[test]
    fn test_bitcommit() {
        let mut bc_assignment = ThreadBCAssignment::new();
        let scripts = new_u32_bit_commit(&mut bc_assignment, U32::from_u64(0x28121614));
        println!("verify scripts: {:?}", verify_u32_4bytes_script(0x28121614));
        let exec_script = script! {
            {scripts.locking_script}
            {verify_u32_4bytes_script(0x28121614)}
            OP_1
        };

        let res = execute_script_with_inputs(exec_script, scripts.unlock_witness);
        assert!(res.success);
    }

    #[test]
    fn test_bitcommit2() {
        for value in [0x28121614, 0x68121614] {
            let point = BabyBear::from_canonical_u64(value);
            let point_as_u32 = point.as_canonical_u32();

            let mut bc_assignment = ThreadBCAssignment::new();
            let scripts = new_challenge_commit(&mut bc_assignment, point);
            let exec_script = script! {
                {scripts.locking_script}
                {point_as_u32}
                OP_EQUALVERIFY
                OP_1
            };

            let res = execute_script_with_inputs(exec_script, scripts.unlock_witness);
            println!(
                "stack: {:?}, stack_length: {:?}",
                res.final_stack,
                res.final_stack.len()
            );
            assert!(res.success);
        }
    }

    fn blake3_compute(input: [U32; 16]) -> [U32; 8] {
        let mut hasher = blake3::Hasher::new();
        for chunk in input.clone() {
            hasher.update(&chunk);
        }
        let hashed: [u8; 32] = hasher.finalize().into();
        let mut output: [U32; 8] = Default::default();

        for idx in 0..8 {
            output[idx] = U32::from_u8_array(&hashed[idx * 4..idx * 4 + 4]);
        }

        output
    }

    #[test]
    fn test_mock_fs_subtree() {
        let mut bc_assignment = ThreadBCAssignment::new();
        let mut fs_subtree: FiatShamirSubTree<BabyBear> = Default::default();
        fs_subtree.state_leafs_num = 1;

        let input_data: [U32; 16] = (0..16)
            .map(|i| U32::from_u64(i))
            .collect_vec()
            .try_into()
            .unwrap();

        let output_data: [U32; 8] = blake3_compute(input_data);

        // for inputs
        let input_commit: [Commit; 16] = (0..16)
            .map(|i| new_u32_bit_commit(&mut bc_assignment, input_data[i]))
            .collect_vec()
            .try_into()
            .unwrap();
        fs_subtree.input_commits.push(input_commit);
        fs_subtree.inputs.push(input_data);

        let output: [Commit; 8] = (0..8)
            .map(|i| new_u32_bit_commit(&mut bc_assignment, output_data[i]))
            .collect_vec()
            .try_into()
            .unwrap();
        fs_subtree.output_commits.push(output);
        fs_subtree.outputs.push(output_data);

        let leafs = fs_subtree.locking_leafs();
        let witnesses = fs_subtree.unlock_witnesses();

        let exec_script = script! {
            {leafs[0].clone()}
        };
        let res = execute_script_with_inputs(exec_script, witnesses[0].clone());
        println!(
            "stack: {:?}, stack_length: {:?}",
            res.final_stack,
            res.final_stack.len()
        );
        assert_eq!(res.final_stack.len(), 1);
        assert!(res.success);
    }

    #[test]
    fn test_fs_subtree_from_challenger() {
        let mut bc_assignment = ThreadBCAssignment::new();

        let permutation = Blake3Permutation {};
        let mut challenger: BfChallenger<BabyBear, [u8; 4], Blake3Permutation, 16> =
            BfChallenger::new(permutation).unwrap();

        challenger.observe([U32::from_u64(0x1234); 8]);
        let _ = challenger.sample();
        challenger.observe([U32::from_u64(0x4567); 8]);
        challenger.observe([U32::from_u64(0x1234); 8]);
        let _ = challenger.sample_bits(8);

        let fs_subtree =
            FiatShamirSubTree::new_from_fri_challenger(&challenger, &mut bc_assignment);

        let leafs = fs_subtree.locking_leafs();
        let witnesses = fs_subtree.unlock_witnesses();

        for idx in 0..fs_subtree.state_leafs_num as usize {
            let exec_script = script! {
                {leafs[idx].clone()}
            };
            let res = execute_script_with_inputs(exec_script, witnesses[idx].clone());
            println!(
                "stack: {:?}, stack_length: {:?}",
                res.final_stack,
                res.final_stack.len()
            );
            assert_eq!(res.final_stack.len(), 1);
            assert!(res.success);
        }
    }

    #[test]
    fn test_fs_subtree_from_challenger_with_grind() {
        let mut bc_assignment = ThreadBCAssignment::new();

        let permutation = Blake3Permutation {};
        let mut challenger: BfChallenger<BabyBear, [u8; 4], Blake3Permutation, 16> =
            BfChallenger::new(permutation).unwrap();

        challenger.observe([U32::from_u64(0x1234); 8]);
        let _ = challenger.sample();
        challenger.observe([U32::from_u64(0x4567); 8]);
        challenger.observe([U32::from_u64(0x1234); 8]);

        challenger.grind(8);

        let fs_subtree =
            FiatShamirSubTree::new_from_fri_challenger(&challenger, &mut bc_assignment);

        let leafs = fs_subtree.locking_leafs();
        let witnesses = fs_subtree.unlock_witnesses();

        let idx = (fs_subtree.grind_leaf_idx) as usize; // challenge leaf
        let exec_script = script! {
            {leafs[idx].clone()}
        };
        let res = execute_script_with_inputs(exec_script, witnesses[idx].clone());
        println!(
            "stack: {:?}, stack_length: {:?}",
            res.final_stack,
            res.final_stack.len()
        );
        assert_eq!(res.final_stack.len(), 1);
        assert!(res.success);
    }

    #[test]
    fn test_fs_subtree_from_challenger_with_grind8() {
        let mut bc_assignment = ThreadBCAssignment::new();

        let permutation = Blake3Permutation {};
        let mut challenger: BfChallenger<BabyBear, [u8; 4], Blake3Permutation, 16> =
            BfChallenger::new(permutation).unwrap();

        challenger.observe([U32::from_u64(0x1234); 8]);
        let _ = challenger.sample();
        challenger.observe([U32::from_u64(0x4567); 8]);
        challenger.observe([U32::from_u64(0x1234); 8]);

        challenger.grind(8);

        let fs_subtree =
            FiatShamirSubTree::new_from_fri_challenger(&challenger, &mut bc_assignment);

        let leafs = fs_subtree.locking_leafs();
        let witnesses = fs_subtree.unlock_witnesses();

        let idx = (fs_subtree.grind_leaf_idx) as usize; // challenge leaf
        let exec_script = script! {
            {leafs[idx].clone()}
        };
        let res = execute_script_with_inputs(exec_script, witnesses[idx].clone());
        println!(
            "stack: {:?}, stack_length: {:?}",
            res.final_stack,
            res.final_stack.len()
        );
        assert_eq!(res.final_stack.len(), 1);
        assert!(res.success);
    }

    #[test]
    fn test_fs_subtree_from_challenger_with_grind10() {
        let mut bc_assignment = ThreadBCAssignment::new();

        let permutation = Blake3Permutation {};
        let mut challenger: BfChallenger<BabyBear, [u8; 4], Blake3Permutation, 16> =
            BfChallenger::new(permutation).unwrap();

        challenger.observe([U32::from_u64(0x1234); 8]);
        let _ = challenger.sample();
        challenger.observe([U32::from_u64(0x4567); 8]);
        challenger.observe([U32::from_u64(0x1234); 8]);

        challenger.grind(10);

        let fs_subtree =
            FiatShamirSubTree::new_from_fri_challenger(&challenger, &mut bc_assignment);

        let leafs = fs_subtree.locking_leafs();
        let witnesses = fs_subtree.unlock_witnesses();

        let idx = (fs_subtree.grind_leaf_idx) as usize; // challenge leaf
        let exec_script = script! {
            {leafs[idx].clone()}
        };
        let res = execute_script_with_inputs(exec_script, witnesses[idx].clone());
        println!(
            "stack: {:?}, stack_length: {:?}",
            res.final_stack,
            res.final_stack.len()
        );
        assert_eq!(res.final_stack.len(), 1);
        assert!(res.success);
    }

    #[test]
    fn test_fs_subtree_from_challenger_with_grind_random() {
        for grind_i in 2..15 {
            let mut bc_assignment = ThreadBCAssignment::new();

            let permutation = Blake3Permutation {};
            let mut challenger: BfChallenger<BabyBear, [u8; 4], Blake3Permutation, 16> =
                BfChallenger::new(permutation).unwrap();

            challenger.observe([U32::from_u64(0x1234); 8]);
            let _ = challenger.sample();
            challenger.observe([U32::from_u64(0x4567); 8]);
            challenger.observe([U32::from_u64(0x1234); 8]);

            challenger.grind(grind_i);

            let fs_subtree =
                FiatShamirSubTree::new_from_fri_challenger(&challenger, &mut bc_assignment);

            let leafs = fs_subtree.locking_leafs();
            let witnesses = fs_subtree.unlock_witnesses();

            let idx = (fs_subtree.grind_leaf_idx) as usize; // challenge leaf
            let exec_script = script! {
                {leafs[idx].clone()}
            };
            let res = execute_script_with_inputs(exec_script, witnesses[idx].clone());
            assert_eq!(res.final_stack.len(), 1);
            assert!(res.success);
            println!("grind index: {:?} is ok", grind_i);
        }
    }

    #[test]
    fn test_fs_subtree_from_challenger_with_grind_random_and_sample() {
        let mut bc_assignment = ThreadBCAssignment::new();

        let permutation = Blake3Permutation {};
        let mut challenger: BfChallenger<BabyBear, [u8; 4], Blake3Permutation, 16> =
            BfChallenger::new(permutation).unwrap();

        challenger.observe([U32::from_u64(0x1234); 8]);
        let _ = challenger.sample();
        challenger.observe([U32::from_u64(0x4567); 8]);
        challenger.observe([U32::from_u64(0x1234); 8]);

        challenger.grind(10);

        let _ = challenger.sample();
        let _ = challenger.sample();

        let fs_subtree =
            FiatShamirSubTree::new_from_fri_challenger(&challenger, &mut bc_assignment);

        let leafs = fs_subtree.locking_leafs();
        let witnesses = fs_subtree.unlock_witnesses();

        let idx = (fs_subtree.state_leafs_num) as usize; // the first sample_leaf
        let exec_script = script! {
            {leafs[idx].clone()}
        };
        let res = execute_script_with_inputs(exec_script, witnesses[idx].clone());

        println!(
            "stack: {:?}, stack_length: {:?}",
            res.final_stack,
            res.final_stack.len()
        );

        assert_eq!(res.final_stack.len(), 1);
        assert!(res.success);
    }

    #[test]
    fn test_fs_subtree_from_challenger_with_grind_random_and_sample2() {
        let mut bc_assignment = ThreadBCAssignment::new();

        let permutation = Blake3Permutation {};
        let mut challenger: BfChallenger<BabyBear, [u8; 4], Blake3Permutation, 16> =
            BfChallenger::new(permutation).unwrap();

        challenger.observe([U32::from_u64(0x1234); 8]);
        let _ = challenger.sample();
        challenger.observe([U32::from_u64(0x4567); 8]);
        let _ = challenger.sample();
        challenger.observe([U32::from_u64(0x1234); 8]);
        let _ = challenger.sample();
        challenger.observe([U32::from_u64(0x1234); 8]);

        challenger.grind(10);

        let _ = challenger.sample();
        let _ = challenger.sample();
        let _ = challenger.sample();
        let _ = challenger.sample();

        let fs_subtree =
            FiatShamirSubTree::new_from_fri_challenger(&challenger, &mut bc_assignment);

        let leafs = fs_subtree.locking_leafs();
        let witnesses = fs_subtree.unlock_witnesses();

        assert_eq!(leafs.len(), witnesses.len());
        for idx in 0..leafs.len() {
            let exec_script = script! {
                {leafs[idx].clone()}
            };
            let res = execute_script_with_inputs(exec_script, witnesses[idx].clone());
            assert!(res.success);
        }
    }

    #[test]
    fn test_babybear4() {
        let mut bc_assignment = ThreadBCAssignment::new();

        let permutation = Blake3Permutation {};
        let mut challenger: BfChallenger<
            BinomialExtensionField<BabyBear, 4>,
            [u8; 4],
            Blake3Permutation,
            16,
        > = BfChallenger::new(permutation).unwrap();

        challenger.observe([U32::from_u64(0x1234); 8]);
        let _ = challenger.sample();

        let fs_subtree =
            FiatShamirSubTree::new_from_fri_challenger(&challenger, &mut bc_assignment);

        let leafs = fs_subtree.locking_leafs();
        let witnesses = fs_subtree.unlock_witnesses();

        assert_eq!(leafs.len(), witnesses.len());
        let idx = 1;
        let exec_script = script! {
            {leafs[idx].clone()}
        };
        let res = execute_script_with_inputs(exec_script, witnesses[idx].clone());
        println!(
            "stack: {:?}, stack_length: {:?}",
            res.final_stack,
            res.final_stack.len()
        );
    }

    #[test]
    fn test_babybear4_more() {
        let mut bc_assignment = ThreadBCAssignment::new();

        let permutation = Blake3Permutation {};
        let mut challenger: BfChallenger<
            BinomialExtensionField<BabyBear, 4>,
            [u8; 4],
            Blake3Permutation,
            16,
        > = BfChallenger::new(permutation).unwrap();

        challenger.observe([U32::from_u64(0x1234); 8]);
        let _ = challenger.sample();
        challenger.observe([U32::from_u64(0x4567); 8]);
        let _ = challenger.sample();
        challenger.observe([U32::from_u64(0x1234); 8]);
        let _ = challenger.sample();
        challenger.observe([U32::from_u64(0x1234); 8]);

        challenger.grind(10);

        let _ = challenger.sample();
        let _ = challenger.sample();
        let _ = challenger.sample();
        let _ = challenger.sample();

        let fs_subtree =
            FiatShamirSubTree::new_from_fri_challenger(&challenger, &mut bc_assignment);

        let leafs = fs_subtree.locking_leafs();
        let witnesses = fs_subtree.unlock_witnesses();

        assert_eq!(leafs.len(), witnesses.len());
        // for idx in 0..leafs.len() {
        let idx = 15;
        let exec_script = script! {
            {leafs[idx].clone()}
        };
        let res = execute_script_with_inputs(exec_script, witnesses[idx].clone());
        println!(
            "idx fail: {:?}, stack: {:?}, stack_length: {:?}",
            idx,
            res.final_stack,
            res.final_stack.len()
        );
        // }
    }
}
