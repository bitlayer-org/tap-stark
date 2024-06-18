use std::fmt::DebugList;
use std::hash::DefaultHasher;

use bitcoin::ScriptBuf;

use crate::bc_assignment::DefaultBCAssignment;
use crate::script_info::ScriptInfo;

struct TaprootLeaf {
    script_buf: ScriptBuf,
    witness: Vec<Vec<u8>>,
    meta_info: String, // record name of combined scriptInfo
    debug: bool,
}

impl TaprootLeaf {
    fn from_eq(value: &ScriptInfo) -> Self {
        Self {
            script_buf: value.get_eq_script(),
            witness: value.witness(),
            meta_info: value.name(),
            debug: true,
        }
    }

    fn from_neq(value: &ScriptInfo) -> Self {
        Self {
            script_buf: value.get_neq_script(),
            witness: value.witness(),
            meta_info: value.name(),
            debug: true,
        }
    }
}

type DefaultPlanner = SimplePlanner;
const SCRIPT_LIMIT: usize = 350 * 1000; // 350kb

trait Planner {
    /// combine
    fn core_combine(infos: Vec<ScriptInfo>) -> ScriptInfo;

    fn combine(infos: Vec<ScriptInfo>) -> Vec<ScriptInfo> {
        let mut acc = 0;
        let mut combined_infos: Vec<ScriptInfo> = vec![];
        let mut res = vec![];
        for mut info in infos {
            let info_size = info.script_size() + info.witness_size();
            if acc + info_size < SCRIPT_LIMIT {
                acc += info_size;
                combined_infos.push(info);
            } else {
                res.push(Self::core_combine(combined_infos));

                // clear status
                combined_infos = vec![info];
                acc = info_size;
            }
        }
        res
    }

    /// compile infos to a set of success taprootleafs in debug mode
    fn compile_to_eq(infos: Vec<ScriptInfo>) -> (Vec<TaprootLeaf>, DefaultBCAssignment) {
        // now process res infos
        let mut bc_assginer = DefaultBCAssignment::new();
        let taproot_leafs = Self::combine(infos)
            .iter_mut()
            .map(|info: &mut ScriptInfo| TaprootLeaf::from_eq(info.gen(&mut bc_assginer)))
            .collect::<Vec<TaprootLeaf>>();

        (taproot_leafs, bc_assginer)
    }

    /// compile infos to a set of fail taprootleafs in release mode
    fn compile_to_neq(infos: Vec<ScriptInfo>) -> (Vec<TaprootLeaf>, DefaultBCAssignment) {
        // now process res infos
        let mut bc_assginer = DefaultBCAssignment::new();
        let taproot_leafs = Self::combine(infos)
            .iter_mut()
            .map(|info: &mut ScriptInfo| TaprootLeaf::from_eq(info.gen(&mut bc_assginer)))
            .collect::<Vec<TaprootLeaf>>();

        (taproot_leafs, bc_assginer)
    }

    /// check whether all infos can be linked with commitments
    fn integrity_check(infos: Vec<ScriptInfo>) -> bool {
        todo!()
    }
}

/// There no too much combine rules in the simple planner
/// 1. Simple planner just combine neighbouring script infos, so the order of vector<ScriptInfo> is a important hint.
/// 2. Some small script infos will be combined to a big one, limited by the `SCRIPT_LIMIT`.
/// 3. For before script's output and after script's input, equivalent bitcommitment is eliminated.
/// 4. u32_add_1 or u32_dec_1 can be thinked of it as equivalent.
struct SimplePlanner {}
impl Planner for SimplePlanner {
    fn core_combine(infos: Vec<ScriptInfo>) -> ScriptInfo {
        todo!()
    }
}

mod test {
    // some tests
}
