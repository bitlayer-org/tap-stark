// the leaf script maybe include
// different field [M31, BabyBear, Babybear EXTField]
// one evaluation from one polynomial or multiple evaluations from multi-polynomials
// different bit-commitment
// how to searlize the leaf
// use which hash to hash the leaf script

use std::usize;

use bitcoin::ScriptBuf as Script;
use bitcoin_script::{define_pushable, script};
use p3_field::TwoAdicField;
use primitives::field::BfField;
use script_manager::bc_assignment::DefaultBCAssignment;
use scripts::bit_comm::bit_comm::BitCommitment;
use scripts::execute_script_with_inputs;
use scripts::secret_generator::ConstantSecretGen;
use scripts::u31_lib::{
    u31_add, u31_equalverify, u31ext_add, u31ext_equalverify, BabyBear4, BabyBearU31,
};
use segment::SegmentLeaf;

use super::verify_folding::{
    cal_neg_x_with_input, fold_degree_with_input, index_to_rou, reverse_bits_len_script_with_input,
    value_square_with_input,
};

define_pushable!();
pub struct RevIndexLeaf {
    sub_group_bits: u32,
    index: u32,
    index_bc: BitCommitment<u32>,
    rev_index: u32,
    rev_index_bc: BitCommitment<u32>,
}
impl RevIndexLeaf {
    pub fn new_from_assign(
        sub_group_bits: u32,
        index: u32,
        rev_index: u32,
        assign: &mut DefaultBCAssignment,
    ) -> Self {
        let index_bc = assign.assign(index);
        let rev_index_bc = assign.assign(rev_index);
        Self::new(sub_group_bits, index, index_bc, rev_index, rev_index_bc)
    }

    pub fn new(
        sub_group_bits: u32,
        index: u32,
        index_bc: BitCommitment<u32>,
        rev_index: u32,
        rev_index_bc: BitCommitment<u32>,
    ) -> Self {
        Self {
            sub_group_bits,
            index,
            index_bc,
            rev_index,
            rev_index_bc,
        }
    }
}

impl SegmentLeaf for RevIndexLeaf {
    fn input(&self) -> Vec<Vec<u8>> {
        let mut sigs1 = self.index_bc.witness();
        let mut sigs0 = self.rev_index_bc.witness();
        sigs1.append(&mut sigs0);
        sigs1
    }

    fn check_input(&self) -> Script {
        script! {
            {self.rev_index_bc.recover_message_euqal_to_commit_message()}
            {self.index_bc.recover_message_euqal_to_commit_message()}
            OP_1
        }
    }

    fn leaf_script(&self) -> Script {
        script! {
            {self.rev_index_bc.check_and_recover_to_altstack()}
            {self.index_bc.check_and_recover()}
            {self.rev_index_bc.message_from_altstack()}
            {reverse_bits_len_script_with_input(self.index,self.sub_group_bits as usize )}
        }
    }
}

pub struct SquareFLeaf<const NUM_POLY: usize, F: BfField> {
    value_bc: BitCommitment<F>,
    value_square_bc: BitCommitment<F>,
}
impl<const NUM_POLY: usize, F: BfField> SquareFLeaf<NUM_POLY, F> {
    pub fn new_from_assign(value: F, value_suqare: F, assign: &mut DefaultBCAssignment) -> Self {
        assert_eq!(value * value, value_suqare);
        let val_bc = assign.assign(value);
        let val_square_bc = assign.assign(value_suqare);
        Self::new(val_bc, val_square_bc)
    }

    pub fn new(value_bc: BitCommitment<F>, value_square_bc: BitCommitment<F>) -> Self {
        Self {
            value_bc,
            value_square_bc,
        }
    }
}

impl<const NUM_POLY: usize, F: BfField> SegmentLeaf for SquareFLeaf<NUM_POLY, F> {
    fn input(&self) -> Vec<Vec<u8>> {
        let mut sigs1 = self.value_square_bc.witness();
        let mut sigs0 = self.value_bc.witness();
        sigs1.append(&mut sigs0);
        sigs1
    }

    fn check_input(&self) -> Script {
        script! {
            {self.value_bc.recover_message_euqal_to_commit_message()}
            {self.value_square_bc.recover_message_euqal_to_commit_message()}
            OP_1
        }
    }

    fn leaf_script(&self) -> Script {
        script! {
            {self.value_bc.check_and_recover_to_altstack()}
            {self.value_square_bc.check_and_recover()}
            {self.value_bc.message_from_altstack()}
            {value_square_with_input::<F>()}
        }
    }
}

pub struct CalNegXLeaf<const NUM_POLY: usize, F: BfField> {
    x_bc: BitCommitment<F>,
    neg_x_bc: BitCommitment<F>,
}
impl<const NUM_POLY: usize, F: BfField> CalNegXLeaf<NUM_POLY, F> {
    pub fn new_from_assign(x: F, neg_x: F, assign: &mut DefaultBCAssignment) -> Self {
        let x_bc = assign.assign(x);
        let neg_x_bc = assign.assign(neg_x);
        Self::new(x_bc, neg_x_bc)
    }

    pub fn new(x_bc: BitCommitment<F>, neg_x_bc: BitCommitment<F>) -> Self {
        CalNegXLeaf { x_bc, neg_x_bc }
    }
}

impl<const NUM_POLY: usize, F: BfField> SegmentLeaf for CalNegXLeaf<NUM_POLY, F> {
    fn input(&self) -> Vec<Vec<u8>> {
        let mut sigs1 = self.neg_x_bc.witness();
        let mut sigs0 = self.x_bc.witness();
        sigs1.append(&mut sigs0);
        sigs1
    }

    fn check_input(&self) -> Script {
        script! {
            {self.x_bc.recover_message_euqal_to_commit_message()}
            {self.neg_x_bc.recover_message_euqal_to_commit_message()}
            OP_1
        }
    }

    fn leaf_script(&self) -> Script {
        script! {
            {self.x_bc.check_and_recover_to_altstack()}
            {self.neg_x_bc.check_and_recover()}
            {self.x_bc.message_from_altstack()}
            {cal_neg_x_with_input::<F>()}
        }
    }
}

// todo: update index to bit-commitment
pub struct IndexToROULeaf<const NUM_POLY: usize, F: BfField> {
    index: usize,
    subgroup_bit_size: usize,
    generator: F,
    index_bc: BitCommitment<u32>,
    x_bc: BitCommitment<F>,
}
impl<const NUM_POLY: usize, F: BfField> IndexToROULeaf<NUM_POLY, F> {
    pub fn new_from_assign(
        index: usize,
        subgroup_bit_size: usize,
        x: F,
        assign: &mut DefaultBCAssignment,
    ) -> Self {
        let x_bc = assign.assign(x);
        let index_bc = assign.assign(index as u32);
        let gen = F::two_adic_generator(subgroup_bit_size);
        Self::new(index, subgroup_bit_size, gen, index_bc, x_bc)
    }

    pub fn new(
        index: usize,
        subgroup_bit_size: usize,
        generator: F,
        index_bc: BitCommitment<u32>,
        x_bc: BitCommitment<F>,
    ) -> Self {
        IndexToROULeaf {
            index,
            subgroup_bit_size,
            generator,
            index_bc: index_bc,
            x_bc: x_bc,
        }
    }

    pub fn generator(&self) -> F {
        F::two_adic_generator(self.subgroup_bit_size)
    }
}

impl<const NUM_POLY: usize, F: BfField> SegmentLeaf for IndexToROULeaf<NUM_POLY, F> {
    fn input(&self) -> Vec<Vec<u8>> {
        let sigs0 = self.x_bc.witness();
        let mut sigs1 = self.index_bc.witness();
        sigs1.extend(sigs0);
        sigs1
    }

    fn check_input(&self) -> Script {
        script! {
            {self.x_bc.recover_message_euqal_to_commit_message()}
            {self.index_bc.recover_message_euqal_to_commit_message()}
           OP_1
        }
    }

    fn leaf_script(&self) -> Script {
        script! {
            // Stack State:
            //  x_preimage   <-- top
            //  index_preimage
            //  generator
            {self.x_bc.check_and_recover_to_altstack()}
            {self.index_bc.check_and_recover()}
            {self.x_bc.message_from_altstack()}
            // Stack State:
            //  x   <-- top
            //  index
            //  generator
            { index_to_rou::<F>(self.subgroup_bit_size as u32) }

        }
    }
}

pub struct ReductionLeaf<const NUM_POLY: usize, F: BfField> {
    prev_fold_bc: BitCommitment<F>,
    opening_bc: BitCommitment<F>,
    result_bc: BitCommitment<F>,
}

impl<const NUM_POLY: usize, F: BfField> ReductionLeaf<NUM_POLY, F> {
    pub fn new_from_assign<'a>(
        prev_fold: F,
        opening: F,
        result: F,
        assign: &'a mut DefaultBCAssignment,
    ) -> Self {
        let prev_fold_bc = assign.assign(prev_fold);
        let opening_bc = assign.assign(opening);
        let result_bc = assign.assign(result);
        Self::new(prev_fold_bc, opening_bc, result_bc)
    }

    fn new(
        prev_fold_bc: BitCommitment<F>,
        opening_bc: BitCommitment<F>,
        result_bc: BitCommitment<F>,
    ) -> Self {
        ReductionLeaf {
            prev_fold_bc,
            opening_bc,
            result_bc,
        }
    }
}

impl<const NUM_POLY: usize, F: BfField> SegmentLeaf for ReductionLeaf<NUM_POLY, F> {
    fn input(&self) -> Vec<Vec<u8>> {
        let mut sigs0 = self.result_bc.witness();
        let sigs1 = self.opening_bc.witness();
        let sigs2 = self.prev_fold_bc.witness();

        sigs0.extend(sigs1.iter().cloned());
        sigs0.extend(sigs2.iter().cloned());
        sigs0
    }

    fn check_input(&self) -> Script {
        script! {
            {self.prev_fold_bc.recover_message_euqal_to_commit_message()}
            {self.opening_bc.recover_message_euqal_to_commit_message()}
            {self.result_bc.recover_message_euqal_to_commit_message()}
            OP_1
        }
    }

    fn leaf_script(&self) -> Script {
        script! {
            {self.prev_fold_bc.check_and_recover_to_altstack()}
            {self.opening_bc.check_and_recover_to_altstack()}
            {self.result_bc.check_and_recover()}
            {self.opening_bc.message_from_altstack()}
            {self.prev_fold_bc.message_from_altstack()}
            if F::U32_SIZE == 1 {
                { u31_add::<BabyBearU31>() }
                { u31_equalverify() }
            }else if F::U32_SIZE == 4{
                {u31ext_add::<BabyBear4>()}
                {u31ext_equalverify::<BabyBear4>()}
            }
            OP_1
        }
    }
}

//Warning! The code only works for Babybear now
pub struct VerifyFoldingLeaf<const NUM_POLY: usize, F: BfField> {
    y_0_x_bc: BitCommitment<F>,
    y_0_neg_x_bc: BitCommitment<F>,
    x_bc: BitCommitment<F>,
    beta_bc: BitCommitment<F>,
    y_1_x_square_bc: BitCommitment<F>,
}

impl<'a, const NUM_POLY: usize, F: BfField> VerifyFoldingLeaf<NUM_POLY, F> {
    pub fn new_from_assign(
        y_0_x: F,
        y_0_neg_x: F,
        x: F,
        beta: F,
        y_1_x_square: F,
        assgin: &'a mut DefaultBCAssignment,
    ) -> Self {
        let x_bc = assgin.assign(x);
        let beta_bc = assgin.assign(beta);
        let y_0_x_bc = assgin.assign(y_0_x);
        let y_0_neg_x_bc = assgin.assign(y_0_neg_x);
        let y_1_x_square_bc = assgin.assign(y_1_x_square);
        Self::new(y_0_x_bc, y_0_neg_x_bc, x_bc, beta_bc, y_1_x_square_bc)
    }

    pub fn new(
        y_0_x_bc: BitCommitment<F>,
        y_0_neg_x_bc: BitCommitment<F>,
        x_bc: BitCommitment<F>,
        beta_bc: BitCommitment<F>,
        y_1_x_square_bc: BitCommitment<F>,
    ) -> Self {
        VerifyFoldingLeaf {
            x_bc,
            beta_bc,
            y_0_x_bc,
            y_0_neg_x_bc,
            y_1_x_square_bc,
        }
    }

    fn input(&self) -> Vec<Vec<u8>> {
        let mut sigs0 = self.y_1_x_square_bc.witness();
        let sigs1 = self.beta_bc.witness();
        let sigs2 = self.x_bc.witness();
        let sigs3 = self.y_0_neg_x_bc.witness();
        let sigs4 = self.y_0_x_bc.witness();

        sigs0.extend(sigs1.iter().cloned());
        sigs0.extend(sigs2.iter().cloned());
        sigs0.extend(sigs3.iter().cloned());
        sigs0.extend(sigs4.iter().cloned());
        sigs0
    }

    fn check_input(&self) -> Script {
        script! {
            {self.y_0_x_bc.recover_message_euqal_to_commit_message()}
            {self.y_0_neg_x_bc.recover_message_euqal_to_commit_message()}
            {self.x_bc.recover_message_euqal_to_commit_message()}
            {self.beta_bc.recover_message_euqal_to_commit_message()}
            {self.y_1_x_square_bc.recover_message_euqal_to_commit_message()}
            OP_1
        }
    }

    fn leaf_script(&self) -> Script {
        script! {
            {self.y_0_x_bc.check_and_recover_to_altstack()}
            {self.y_0_neg_x_bc.check_and_recover_to_altstack()}
            {self.x_bc.check_and_recover_to_altstack()}
            {self.beta_bc.check_and_recover_to_altstack()}
            {self.y_1_x_square_bc.check_and_recover()}
            {self.beta_bc.message_from_altstack()}
            {self.x_bc.message_from_altstack()}
            {self.y_0_neg_x_bc.message_from_altstack()}
            {self.y_0_x_bc.message_from_altstack()}
            {fold_degree_with_input::<F>()}
        }
    }

    pub fn execute_leaf_script(&self) -> bool {
        let result = execute_script_with_inputs(self.leaf_script(), self.input());
        result.success
    }

    fn leaf_script_witn_noeuqal(&self) -> Script {
        //todo: update to noeuqal
        self.leaf_script()
    }
}

impl<'a, const NUM_POLY: usize, F: BfField> SegmentLeaf for VerifyFoldingLeaf<NUM_POLY, F> {
    fn input(&self) -> Vec<Vec<u8>> {
        let mut sigs0 = self.y_1_x_square_bc.witness();
        let sigs1 = self.beta_bc.witness();
        let sigs2 = self.x_bc.witness();
        let sigs3 = self.y_0_neg_x_bc.witness();
        let sigs4 = self.y_0_x_bc.witness();

        sigs0.extend(sigs1.iter().cloned());
        sigs0.extend(sigs2.iter().cloned());
        sigs0.extend(sigs3.iter().cloned());
        sigs0.extend(sigs4.iter().cloned());
        sigs0
    }

    fn check_input(&self) -> Script {
        script! {
            {self.y_0_x_bc.recover_message_euqal_to_commit_message()}
            {self.y_0_neg_x_bc.recover_message_euqal_to_commit_message()}
            {self.x_bc.recover_message_euqal_to_commit_message()}
            {self.beta_bc.recover_message_euqal_to_commit_message()}
            {self.y_1_x_square_bc.recover_message_euqal_to_commit_message()}
            OP_1
        }
    }

    fn leaf_script(&self) -> Script {
        script! {
            {self.y_0_x_bc.check_and_recover_to_altstack()}
            {self.y_0_neg_x_bc.check_and_recover_to_altstack()}
            {self.x_bc.check_and_recover_to_altstack()}
            {self.beta_bc.check_and_recover_to_altstack()}
            {self.y_1_x_square_bc.check_and_recover()}
            {self.beta_bc.message_from_altstack()}
            {self.x_bc.message_from_altstack()}
            {self.y_0_neg_x_bc.message_from_altstack()}
            {self.y_0_x_bc.message_from_altstack()}
            {fold_degree_with_input::<F>()}
        }
    }
}

pub struct EvaluationLeaf<const NUM_POLY: usize, F: BfField> {
    leaf_index: usize,
    x: F,
    x_commitment: BitCommitment<F>,
    neg_x_commitment: BitCommitment<F>,
    evaluations: Vec<F>,
    evaluations_commitments: Vec<BitCommitment<F>>,
}

impl<const NUM_POLY: usize, F: BfField> EvaluationLeaf<NUM_POLY, F> {
    pub fn new(leaf_index: usize, x: F, evaluations: Vec<F>) -> Self {
        assert_eq!(evaluations.len(), NUM_POLY);

        let x_commitment = BitCommitment::new::<ConstantSecretGen>(x);
        let neg_x_commitment = BitCommitment::new::<ConstantSecretGen>(F::field_mod() - x);
        let mut evaluations_commitments = Vec::new();
        for i in 0..NUM_POLY {
            evaluations_commitments.push(BitCommitment::new::<ConstantSecretGen>(evaluations[i]));
        }

        Self {
            leaf_index,
            x,
            x_commitment,
            neg_x_commitment,
            evaluations,
            evaluations_commitments,
        }
    }

    pub fn leaf_script(&self) -> Script {
        // equal to x script
        let scripts = script! {
            { self.x_commitment.commitments[0].checksig_verify_script() }
            { self.x_commitment.commitments[0].commit_u32_as_4bytes_script() }
            // todo: calculate to equal to -x
            for i in 0..NUM_POLY{
                { self.evaluations_commitments[NUM_POLY-1-i].commitments[0].checksig_verify_script() }
                { self.evaluations_commitments[NUM_POLY-1-i].commitments[0].commit_u32_as_4bytes_script() }
            }
            OP_1
        };

        scripts
    }

    pub fn two_point_leaf_script(&self) -> Script {
        // equal to x script
        let scripts = script! {
            { self.x_commitment.commitments[0].checksig_verify_script() }
            { self.x_commitment.commitments[0].commit_u32_as_4bytes_script() }
            { self.neg_x_commitment.commitments[0].checksig_verify_script() }
            { self.neg_x_commitment.commitments[0].commit_u32_as_4bytes_script() }
            for i in 0..NUM_POLY{
                { self.evaluations_commitments[NUM_POLY-1-i].commitments[0].checksig_verify_script() }
                { self.evaluations_commitments[NUM_POLY-1-i].commitments[0].commit_u32_as_4bytes_script() }
            }
            OP_1
        };
        scripts
    }
}

pub fn u8_to_hex_str(byte: &u8) -> String {
    format!("{:02X}", byte)
}

#[cfg(test)]
mod test {
    use p3_baby_bear::BabyBear;
    use p3_field::extension::BinomialExtensionField;
    use p3_field::{AbstractField, TwoAdicField};
    use p3_util::reverse_bits_len;
    use primitives::mmcs::taptree::EvaluationLeaf;
    use rand::Rng;
    use scripts::execute_script;

    type AF = BabyBear;
    type F = BinomialExtensionField<BabyBear, 4>;
    use scripts::execute_script_with_inputs;

    use super::*;

    #[test]
    fn test_rev_index_leaf() {
        let mut assign = DefaultBCAssignment::new();

        let bits = 10;

        for index in 0..100 {
            let rev_index = reverse_bits_len(index, bits);
            let leaf = RevIndexLeaf::new_from_assign(
                bits as u32,
                index as u32,
                rev_index as u32,
                &mut assign,
            );
            let success = leaf.execute_leaf_script();
            assert_eq!(success, true);
        }
    }

    #[test]
    fn test_value_square_leaf() {
        let mut assign = DefaultBCAssignment::new();
        let index = 6;
        let subgroup_bit_size = 3;

        let value = BabyBear::from_canonical_u32(1234);
        let value_square = value * value;

        let leaf = SquareFLeaf::<1, BabyBear>::new_from_assign(value, value_square, &mut assign);
        let check_input_script = leaf.check_input();
        let result = execute_script_with_inputs(check_input_script, leaf.input());
        assert!(result.success);
        let success = leaf.execute_leaf_script();
        assert_eq!(success, true);

        let value = F::from_canonical_u32(1234);
        let value_square = value * value;

        let leaf = SquareFLeaf::<1, F>::new_from_assign(value, value_square, &mut assign);
        let check_input_script = leaf.check_input();
        let result = execute_script_with_inputs(check_input_script, leaf.input());
        assert!(result.success);
        let success = leaf.execute_leaf_script();
        assert_eq!(success, true);
    }

    #[test]
    fn test_cal_neg_x_leaf() {
        let mut assign = DefaultBCAssignment::new();
        let index = 6;
        let subgroup_bit_size = 3;

        let x = BabyBear::two_adic_generator(subgroup_bit_size).exp_u64(index as u64);
        let neg_x = x * BabyBear::two_adic_generator(1);

        let leaf = CalNegXLeaf::<1, BabyBear>::new_from_assign(x, neg_x, &mut assign);
        let check_input_script = leaf.check_input();
        let result = execute_script_with_inputs(check_input_script, leaf.input());
        assert!(result.success);
        let success = leaf.execute_leaf_script();
        assert_eq!(success, true);

        let x = F::two_adic_generator(subgroup_bit_size).exp_u64(index as u64);
        let neg_x: BinomialExtensionField<BabyBear, 4> = x * F::two_adic_generator(1);

        let leaf = CalNegXLeaf::<1, F>::new_from_assign(x, neg_x, &mut assign);
        let check_input_script = leaf.check_input();
        let result = execute_script_with_inputs(check_input_script, leaf.input());
        assert!(result.success);
        let success = leaf.execute_leaf_script();
        assert_eq!(success, true);
    }

    #[test]
    fn test_index_to_root_of_unity_leaf() {
        let mut assign = DefaultBCAssignment::new();
        let num: usize = 100;
        let subgroup_bit_size = 12;
        for index in 0..num {
            let x = BabyBear::two_adic_generator(subgroup_bit_size).exp_u64(index as u64);
            let leaf = IndexToROULeaf::<1, BabyBear>::new_from_assign(
                index as usize,
                subgroup_bit_size,
                x,
                &mut assign,
            );
            let check_input_script = leaf.check_input();
            let result = execute_script_with_inputs(check_input_script, leaf.input());
            assert!(result.success);
            let success = leaf.execute_leaf_script();
            assert_eq!(success, true);
        }
    }

    #[test]
    fn test_index_to_root_of_unity_leaf_over_extension() {
        let mut assign = DefaultBCAssignment::new();
        let num: usize = 100;
        let subgroup_bit_size = 12;
        for index in 0..num {
            let x = F::two_adic_generator(subgroup_bit_size).exp_u64(index as u64);
            let leaf = IndexToROULeaf::<1, F>::new_from_assign(
                index as usize,
                subgroup_bit_size,
                x,
                &mut assign,
            );
            let check_input_script = leaf.check_input();
            let result = execute_script_with_inputs(check_input_script, leaf.input());
            assert!(result.success);
            let success = leaf.execute_leaf_script();
            assert_eq!(success, true);
        }
    }

    #[test]
    fn test_reduction_leaf() {
        let mut assign = DefaultBCAssignment::new();
        let a = BabyBear::from_canonical_u32(133);
        let b = BabyBear::from_canonical_u32(2222);
        let c = a + b;
        let reduction_leaf = ReductionLeaf::<1, BabyBear>::new_from_assign(a, b, c, &mut assign);
        let input = reduction_leaf.input();
        let check_input_script = reduction_leaf.check_input();
        let result = execute_script_with_inputs(check_input_script, input);
        assert!(result.success);

        let input = reduction_leaf.input();
        let reduction_script = reduction_leaf.leaf_script();
        let result = execute_script_with_inputs(reduction_script, input);
        assert!(result.success);

        let mut assign = DefaultBCAssignment::new();
        let a = F::from_canonical_u32(133);
        let b = F::from_canonical_u32(2222);
        let c = a + b;
        let reduction_leaf = ReductionLeaf::<1, F>::new_from_assign(a, b, c, &mut assign);
        let input = reduction_leaf.input();
        let check_input_script = reduction_leaf.check_input();
        let result = execute_script_with_inputs(check_input_script, input);
        assert!(result.success);

        let input = reduction_leaf.input();
        let reduction_script = reduction_leaf.leaf_script();
        let result = execute_script_with_inputs(reduction_script, input);
        assert!(result.success);
    }

    #[test]
    fn test_folding_leaf() {
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

            let mut assign = DefaultBCAssignment::new();

            for j in 0..n as usize {
                let x_index = j;
                let x_nge_index = (n / 2 + x_index) % n;
                let x = subgroup[x_index as usize];
                let y0_x = BabyBear::from_canonical_u32(y0[x_index]);
                let y0_neg_x = BabyBear::from_canonical_u32(y0[x_nge_index]);
                let y_1_x_quare = BabyBear::from_canonical_u32(y1[x_index % (n / 2)]);

                let folding_leaf = VerifyFoldingLeaf::<1, BabyBear>::new_from_assign(
                    y0_x,
                    y0_neg_x,
                    x,
                    beta,
                    y_1_x_quare,
                    &mut assign,
                );

                let input = folding_leaf.input();
                let check_input_script = folding_leaf.check_input();
                let result = execute_script_with_inputs(check_input_script, input);
                assert!(result.success);

                let input = folding_leaf.input();
                let folding_script = folding_leaf.leaf_script();
                let result = execute_script_with_inputs(folding_script, input);
                assert!(result.success);
            }
        }
    }

    #[test]
    fn test_push_bytes() {
        let scripts1 = script! {
            0x00bc
            OP_DROP
            OP_1
        };

        let scripts2 = script! {
            0x50
            OP_DROP
            OP_1
        };

        let scripts3 = script! {
            <0x90>
            OP_DROP
            OP_1
        };

        // let script4 = Script::parse_asm("OP_PUSHDATA1 90 OP_DROP OP_PUSHNUM_1");
        let scripts4 = Script::parse_asm("OP_PUSHBYTES_1 90 OP_DROP OP_PUSHNUM_1").unwrap();
        println!("{:?}", scripts1);
        println!("{:?}", scripts2);
        println!("{:?}", scripts3);
        println!("{:?}", scripts4);
        let result = execute_script(scripts4);
        assert!(result.success);
    }
}
