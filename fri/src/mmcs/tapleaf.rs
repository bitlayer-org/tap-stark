use alloc::vec::Vec;

use crate::fri_scripts::leaf::SegmentLeaf;
use bitcoin::{witness, ScriptBuf as Script, TapNodeHash};
pub trait Tapleaf {
    fn unlock_witness(&self) -> Vec<Vec<u8>>;
    fn script(&self) -> Script;
}

pub struct VerifierLeaf {
    pub witness: Vec<Vec<u8>>,
    pub script: Script,
}

impl VerifierLeaf {
    fn new(witness: Vec<Vec<u8>>, script: Script) -> Self {
        Self { witness, script }
    }

    fn new_from_segment_leaf<L: SegmentLeaf>(leaf: L) -> Self {
        let script = leaf.leaf_script_witn_noeuqal();
        let witness = leaf.input();
        Self::new(witness, script)
    }
}

impl<L: SegmentLeaf> From<L> for VerifierLeaf {
    fn from(leaf: L) -> Self {
        let script = leaf.leaf_script_witn_noeuqal();
        let witness = leaf.input();
        Self { witness, script }
    }
}

impl Tapleaf for VerifierLeaf {
    fn unlock_witness(&self) -> Vec<Vec<u8>> {
        self.witness.clone()
    }

    fn script(&self) -> Script {
        self.script.clone()
    }
}
