use bitcoin::ScriptBuf;

use crate::bc_assignment::DefaultBCAssignment;
use crate::script_info::ScriptInfo;

struct TaprootLeaf {
    script_buf: ScriptBuf,
    witness: Vec<Vec<u8>>,
    meta_info: Vec<String>, // record name of combined scriptInfo
    debug: bool,
}

type DefaultPlanner = SimplePlanner;
const SCRIPT_LIMIT: usize = 350 * 1000; // 350kb

trait Planner {
    /// combine
    fn combine(infos: Vec<ScriptInfo>) -> Vec<ScriptInfo>;
    /// compile infos to a set of success taprootleafs in debug mode
    fn compile_to_eq(infos: Vec<ScriptInfo>) -> (Vec<TaprootLeaf>, DefaultBCAssignment) {
        let mut acc = 0;
        let mut combined_infos: Vec<ScriptInfo> = vec![];
        let mut res = vec![];
        for mut info in infos {
            let info_size = info.script_size() + info.witness_size();
            if acc + info_size < SCRIPT_LIMIT {
                acc += info_size;
                combined_infos.push(info);
            } else {
                res.push(Self::combine(combined_infos));

                // clear status
                combined_infos = vec![info];
                acc = info_size;
            }
        }

        // now process res infos

        todo!()
    }
    /// compile infos to a set of fail taprootleafs in release mode
    fn compile_to_neq(infos: Vec<ScriptInfo>) -> (Vec<TaprootLeaf>, DefaultBCAssignment);
    /// check whether all infos can be linked with commitments
    fn integrity_check(infos: Vec<ScriptInfo>) -> bool;
}

/// There no too much combine rules in the simple planner
/// 1. Simple planner just combine neighbouring script infos, so the order of vector<ScriptInfo> is a important hint.
/// 2. Some small script infos will be combined to a big one, limited by the `SCRIPT_LIMIT`.
/// 3. For before script's output and after script's input, equivalent bitcommitment is eliminated.
/// 4. u32_add_1 or u32_dec_1 can be thinked of it as equivalent.
struct SimplePlanner {}
// impl Planner for SimplePlanner {}

mod test {
    // some tests
}