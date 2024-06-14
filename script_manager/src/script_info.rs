use std::sync::Arc;

use bitcoin::ScriptBuf;
use bitcoin_script::script;
use scripts::bit_comm::bit_comm::BitCommitment;
use scripts::bit_comm_u32::BitCommitmentU32;
use scripts::AsU32Vec;

// Implement basic script, and can be commpiled by planner
struct ScriptInfo {
    name: String,
    intput_commits: Vec<Box<dyn AsU32Vec>>,
    output_commits: Vec<Box<dyn AsU32Vec>>,
    script: ScriptBuf,
}

impl ScriptInfo {
    pub fn new(name: &str, script: ScriptBuf) -> Self {
        Self {
            name: name.clone().into(),
            intput_commits: vec![],
            output_commits: vec![],
            script,
        }
    }
    pub fn add_input<F: AsU32Vec + 'static>(&mut self, input: F) -> &mut Self {
        self.intput_commits.push(Box::new(input));
        self
    }

    pub fn add_output<F: AsU32Vec + 'static>(&mut self, output: F) -> &mut Self {
        self.output_commits.push(Box::new(output));
        self
    }

    // for debug and unit test
    pub fn get_eq_script(&self) -> ScriptBuf {
        script!()
    }

    // for release
    pub fn get_neq_script(&self) -> ScriptBuf {
        script!()
    }

    // success with eq_script, and fail in neq_script
    pub fn witness(&self) -> Vec<Vec<u8>> {
        vec![]
    }

    // #[no_use]
    // pub fn check(&self) -> Bool;

    // pub fn merge(&self, other &Self) -> ScriptInfo;
    // pub fn size(&self) -> usize;
}

#[cfg(test)]
mod test {
    use bitcoin_script::script;
    use p3_baby_bear::BabyBear;
    use p3_field::AbstractField;

    use super::ScriptInfo;

    #[test]
    fn test_basic_script_info() {
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
}
