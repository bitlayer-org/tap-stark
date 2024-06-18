use std::collections::VecDeque;

use bitcoin::opcodes::OP_TOALTSTACK;
use bitcoin::{witness, ScriptBuf};
use bitcoin_script::script;
use scripts::pushable;

use crate::bc_assignment::DefaultBCAssignment;
use crate::script_info;
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
    fn core_combine(infos: Vec<ScriptInfo>, debug: bool) -> ScriptInfo;

    fn combine(infos: Vec<ScriptInfo>, debug: bool) -> Vec<ScriptInfo> {
        let mut acc = 0;
        let mut combined_infos: Vec<ScriptInfo> = vec![];
        let mut res = vec![];
        for mut info in infos {
            let info_size = info.script_size() + info.witness_size();
            if acc + info_size < SCRIPT_LIMIT {
                acc += info_size;
                combined_infos.push(info);
            } else {
                res.push(Self::core_combine(combined_infos, debug));

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
        let taproot_leafs = Self::combine(infos, true)
            .iter_mut()
            .map(|info: &mut ScriptInfo| TaprootLeaf::from_eq(info.gen(&mut bc_assginer)))
            .collect::<Vec<TaprootLeaf>>();

        (taproot_leafs, bc_assginer)
    }

    /// compile infos to a set of fail taprootleafs in release mode
    fn compile_to_neq(infos: Vec<ScriptInfo>) -> (Vec<TaprootLeaf>, DefaultBCAssignment) {
        // now process res infos
        let mut bc_assginer = DefaultBCAssignment::new();
        let taproot_leafs = Self::combine(infos, false)
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

/// A inner helper structure
#[derive(Clone, Default)]
struct Cell {
    value: u32,
    source: u32, // TODO: inc and dec
}

impl From<&u32> for Cell {
    fn from(value: &u32) -> Self {
        Self {
            value: value.clone(),
            source: 0,
        }
    }
}

/// There are no much combine rules in the simple planner
/// 1. Simple planner just combine neighbouring script infos, so the order of vector<ScriptInfo> is a important hint.
/// 2. Some small script infos will be combined to a big one, limited by the `SCRIPT_LIMIT`.
/// 3. For before script's output and after script's input, equivalent bitcommitment is eliminated.
/// 4. u32_add_1 or u32_dec_1 can be thinked of it as equivalent.

struct SimplePlanner {}
impl Planner for SimplePlanner {
    fn core_combine(infos: Vec<ScriptInfo>, debug: bool) -> ScriptInfo {
        let combined_name: String = infos
            .iter()
            .map(|x| x.name())
            .collect::<Vec<String>>()
            .join("+");

        let mut big_table: Vec<Vec<Cell>> = vec![];
        for info in infos.clone() {
            let mut witness: Vec<Cell> = Default::default();
            info.intput_values.iter().for_each(|input| {
                witness.extend(
                    input
                        .bc_as_u32_vec()
                        .iter()
                        .map(|x| x.into())
                        .collect::<Vec<Cell>>(),
                );
            });
            info.output_values.iter().for_each(|output| {
                witness.extend(
                    output
                        .bc_as_u32_vec()
                        .iter()
                        .map(|x| x.into())
                        .collect::<Vec<Cell>>(),
                );
            });
            big_table.push(witness.into());
        }

        // the max size of big_table is 1000, so it will be ok to find in a two-layer loop
        // pre assign offset to cell
        let mut offset: u32 = 0;
        for (i, cells) in big_table.iter_mut().enumerate() {
            for cell in cells.iter_mut() {
                cell.source = offset;
                offset += 1;
            }
        }

        let mut offset: u32 = 0;
        let mut bc_values = vec![];
        let cloned_table = big_table.clone();
        for (i, cells) in big_table.iter_mut().enumerate() {
            for cell in cells.iter_mut() {
                // Can this cell be founded before ?
                for j in 0..i - 1 {
                    let dup_cell = cloned_table
                        .get(j)
                        .unwrap()
                        .iter()
                        .find(|x| x.value == cell.value);
                    match dup_cell {
                        Some(inner_cell) => {
                            // Push currect offset
                            cell.source = inner_cell.source;
                            break;
                        }
                        None => cell.source = offset,
                    }
                }
                offset += 1;
            }
        }

        // process big table from begin to end and dup-push to correspond offset
        let mut offset = 0;
        let mut copy_script = vec![];
        for cells in big_table {
            for cell in cells {
                if cell.source != offset {
                    // TODO: can be optimized more
                    copy_script.extend_from_slice(
                        script! {
                            for _ in 0..cell.source {
                                OP_TOALTSTACK
                            }
                            OP_DUP // not just OP_DUP, possible OP_DUP, OP_ADD1
                            for _ in 0..(offset - cell.source) {
                                OP_SWAP OP_TOALTSTACK
                            }

                            for _ in 0..(offset) {
                                OP_FROMALTSTACK
                            }
                        }
                        .as_bytes(),
                    );
                } else {
                    bc_values.push(cell.value);
                }
                offset += 1;
            }
        }

        let script = script_info! {
            &combined_name,
            script! {
                for info in infos {
                    {info.script.clone()}
                    {ScriptInfo::ext_equalverify(info.get_output_total_size(), debug)}
                }
            },
            [bc_values],
            []
        };

        script
    }
}

mod test {
    // some tests
    #[test]
    fn test_simple_planner() {
        assert!(true)
    }
}
