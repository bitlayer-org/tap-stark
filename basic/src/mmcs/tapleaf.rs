use bitcoin::ScriptBuf as Script;

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

}


impl Tapleaf for VerifierLeaf {
    fn unlock_witness(&self) -> Vec<Vec<u8>> {
        self.witness.clone()
    }

    fn script(&self) -> Script {
        self.script.clone()
    }
}
