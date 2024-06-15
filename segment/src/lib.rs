use bitcoin::ScriptBuf as Script;
use scripts::execute_script_with_inputs;
pub trait SegmentLeaf {
    fn input(&self) -> Vec<Vec<u8>>;
    fn check_input(&self) -> Script;
    fn leaf_script(&self) -> Script;

    fn execute_leaf_script(&self) -> bool {
        let result = execute_script_with_inputs(self.leaf_script(), self.input());
        result.success
    }

    fn leaf_script_witn_noeuqal(&self) -> Script {
        self.leaf_script()
    }
}
