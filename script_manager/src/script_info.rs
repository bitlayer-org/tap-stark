use std::borrow::BorrowMut;
use std::collections::VecDeque;
use std::sync::Arc;

use bitcoin::opcodes::{OP_EQUALVERIFY, OP_FALSE, OP_FROMALTSTACK, OP_RESERVED};
use bitcoin::ScriptBuf;
use bitcoin_script::script;
use scripts::bit_comm::bit_comm::{pushable, BitCommitment};
use scripts::bit_comm_u32::BitCommitmentU32;
use scripts::secret_generator::ThreadSecretGen;
use scripts::treepp::Script;
use scripts::{unroll, winternitz, AsU32Vec};

// Implement basic script, and can be commpiled by planner
struct ScriptInfo {
    name: String,
    intput_values: Vec<Arc<Box<dyn AsU32Vec>>>,
    output_values: Vec<Arc<Box<dyn AsU32Vec>>>,
    script: ScriptBuf,

    final_script: Option<(ScriptBuf, Vec<Vec<u8>>)>,
}

impl ScriptInfo {
    pub fn new(name: &str, script: ScriptBuf) -> Self {
        Self {
            name: name.clone().into(),
            intput_values: vec![],
            output_values: vec![],
            script,
            final_script: None,
        }
    }
    pub fn add_input<F: AsU32Vec + 'static>(&mut self, input: F) -> &mut Self {
        self.intput_values.push(Arc::new(Box::new(input)));
        self
    }

    pub fn add_output<F: AsU32Vec + 'static>(&mut self, output: F) -> &mut Self {
        self.output_values.push(Arc::new(Box::new(output)));
        self
    }

    /// After executing this script, the stacks will be like this.
    /// stack: [..., input1, input0], altstack: [..., output1, ouput0]
    fn check_witness(&mut self) -> ScriptBuf {
        match self.final_script.clone() {
            Some((script, _)) => script,
            None => {
                let (script, _) = self.bc_gen();
                script
            }
        }
    }

    // witness: [..., input1, input0, output0, output1, ...]
    // success with eq_script, and fail in neq_script
    pub fn witness(&mut self) -> Vec<Vec<u8>> {
        match self.final_script.clone() {
            Some((_, witness)) => witness,
            None => {
                let (_, witness) = self.bc_gen();
                witness
            }
        }
    }

    fn bc_gen(&mut self) -> (ScriptBuf, Vec<Vec<u8>>) {
        assert!(self.final_script.is_none());

        let mut script_bytes = vec![];
        let mut move_back_bytes = vec![];
        let mut witness: VecDeque<Vec<u8>> = Default::default();

        for value in (&self.output_values).into_iter().rev() {
            let value_commitment = BitCommitment::new_with_box::<ThreadSecretGen>(value);
            script_bytes.extend_from_slice(
                script! {
                    {value_commitment.as_ref().check_and_recover()}
                    {value_commitment.as_ref().message_to_altstack()}
                }
                .as_bytes(),
            );

            // witness.extend(value_commitment.witness());
            value_commitment
                .witness()
                .iter()
                .rev()
                .for_each(|x| witness.push_front(x.clone()));
        }

        for value in &self.intput_values {
            let value_commitment = BitCommitment::new_with_box::<ThreadSecretGen>(value);
            script_bytes.extend_from_slice(
                script! {
                    {value_commitment.as_ref().check_and_recover()}
                    {value_commitment.as_ref().message_to_altstack()}
                }
                .as_bytes(),
            );

            move_back_bytes.extend_from_slice(
                script! {
                    {value_commitment.as_ref().message_from_altstack()}
                }
                .as_bytes(),
            );

            let _ = value_commitment
                .witness()
                .iter()
                .rev()
                .for_each(|x| witness.push_front(x.clone()));
        }

        script_bytes.extend(move_back_bytes);

        let final_script = (Script::from(script_bytes), witness.into());
        self.final_script = Some(final_script.clone());
        final_script
    }

    pub fn ext_equalverify(size: u32, eq: bool) -> Script {
        script! {
            for _ in 0..size {
                OP_FROMALTSTACK
            }

            { unroll(size - 1, |i| {
                let gap = size - i;
                script!{
                    { gap } OP_ROLL
                    if eq {OP_EQUALVERIFY} else {OP_EQUAL OP_FALSE OP_EQUALVERIFY}
            }}) }
            if eq {OP_EQUALVERIFY} else {OP_EQUAL OP_FALSE OP_EQUALVERIFY}
        }
    }

    // for debug and unit test
    pub fn get_eq_script(&mut self) -> ScriptBuf {
        script! {
            {self.check_witness()}
            {self.script.clone()}
            // OP_RESERVED
            // check equal
            for value in &self.output_values {
                {Self::ext_equalverify(value.bc_as_u32_vec().len() as u32, true)}
            }
            OP_TRUE
        }
    }

    // for release
    pub fn get_neq_script(&mut self) -> ScriptBuf {
        script! {
            {self.check_witness()}
            {self.script.clone()}
            // check no equal
            for value in &self.output_values {
                {Self::ext_equalverify(value.bc_as_u32_vec().len() as u32, false)}
            }
            OP_TRUE
        }
    }

    // TODO: pub fn merge(&self, other &Self) -> ScriptInfo;

    pub fn script_size(&mut self) -> usize {
        self.get_neq_script().len()
    }

    pub fn witness_size(&mut self) -> usize {
        let mut res = 0;
        self.witness().iter().for_each(|x| res += x.len());
        res
    }
}

// macro_rules! script_info {
// ($name:expr, $script:expr, {$($inputs:expr)*}, {$($outputs:expr)*}) => {{
// let mut temp_script_info = ScriptInfo::new($name, $script);
// $(temp_script_info.add_input($inputs))*
// $(temp_script_info.add_output($outputs))*
// temp_script_info
// }};
// }

macro_rules! script_info {
    ($name:expr, $script:expr, [$($inputs:expr),*], [$($outputs:expr),*]) => {{
        let mut temp_script_info = ScriptInfo::new($name, $script);
        $(temp_script_info.add_input($inputs);)*
        $(temp_script_info.add_output($outputs);)*
        temp_script_info
    }};
}

#[cfg(test)]
mod test {
    use std::ops::Mul;

    use bitcoin::opcodes::{OP_FROMALTSTACK, OP_TOALTSTACK};
    use bitcoin_script::script;
    use p3_baby_bear::BabyBear;
    use p3_field::AbstractField;
    use primitives::field::BinomialExtensionField;
    use scripts::bit_comm::bit_comm::{pushable, BitCommitment};
    use scripts::secret_generator::ThreadSecretGen;
    use scripts::{execute_script_with_inputs, BabyBear4, U31ExtConfig};

    use super::ScriptInfo;

    type B4 = BinomialExtensionField<BabyBear, 4>;

    #[test]
    fn test_basic_script_info_norun() {
        let script_info = ScriptInfo::new(
            "add_{i}+{j}+{c}",
            script! {
                OP_ADD
                OP_ADD
            },
        )
        .add_input(1)
        .add_input(2)
        .add_input(3)
        .add_output(BabyBear::from_canonical_u16(0x12));
    }

    #[test]
    fn test_basic_script_info() {
        let mut x = script_info!(
            "add",
            script! {
                OP_ADD
                // OP_ADD
            },
            [1, 2],
            [3]
        );

        // let bc = BitCommitment::new_with_box::<ThreadSecretGen>(&x.output_values[0].clone());
        // let res = execute_script_with_inputs(bc.check_and_recover(), bc.witness());
        let res = execute_script_with_inputs(x.get_eq_script(), x.witness());
        println!("res: {:?}", res);
        assert!(res.success);
        let res = execute_script_with_inputs(x.get_neq_script(), x.witness());
        assert!(!res.success);
    }

    #[test]
    fn test_basic_script_info2() {
        let mut x = script_info!(
            "add",
            script! {
                OP_ADD
                OP_ADD
            },
            [9, 10, 11],
            [30]
        );

        // let bc = BitCommitment::new_with_box::<ThreadSecretGen>(&x.output_values[0].clone());
        // let res = execute_script_with_inputs(bc.check_and_recover(), bc.witness());
        let res = execute_script_with_inputs(x.get_eq_script(), x.witness());
        println!("res: {:?}", res);
        assert!(res.success);
        let res = execute_script_with_inputs(x.get_neq_script(), x.witness());
        assert!(!res.success);
    }

    #[test]
    fn test_basic_script_info3() {
        assert_eq!(
            B4::from_canonical_u32(10).mul(B4::from_canonical_u32(12)),
            B4::from_canonical_u32(120)
        );
        let mut x = script_info!(
            "add",
            script! {
                {BabyBear4::mul_impl()}
            },
            [B4::from_canonical_u32(10), B4::from_canonical_u32(12)],
            [B4::from_canonical_u32(10).mul(B4::from_canonical_u32(12))]
        );

        // let bc = BitCommitment::new_with_box::<ThreadSecretGen>(&x.output_values[0].clone());
        // let res = execute_script_with_inputs(bc.check_and_recover(), bc.witness());
        let res = execute_script_with_inputs(x.get_eq_script(), x.witness());
        println!("res stack: {:?}", res);
        assert!(res.success);
        let res = execute_script_with_inputs(x.get_neq_script(), x.witness());
        assert!(!res.success);
    }

    #[test]
    fn test_basic_script_info4() {
        assert_eq!(
            B4::from_canonical_u32(10).mul(B4::from_canonical_u32(12)),
            B4::from_canonical_u32(120)
        );
        let mut x = script_info!(
            "add",
            script! {
                OP_ADD
                OP_TOALTSTACK
                {BabyBear4::mul_impl()}
                OP_FROMALTSTACK
            },
            [1, 2, B4::from_canonical_u32(10), B4::from_canonical_u32(12)],
            [3, B4::from_canonical_u32(120)]
        );

        // let bc = BitCommitment::new_with_box::<ThreadSecretGen>(&x.output_values[0].clone());
        // let res = execute_script_with_inputs(bc.check_and_recover(), bc.witness());
        let res = execute_script_with_inputs(x.get_eq_script(), x.witness());
        println!("res stack: {:?}", res);
        assert!(res.success);
        let res = execute_script_with_inputs(x.get_neq_script(), x.witness());
        assert!(!res.success);
    }
}
