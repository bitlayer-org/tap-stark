use std::collections::VecDeque;

use bitcoin::opcodes::{OP_RESERVED, OP_TOALTSTACK};
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
const SOFT_u32_LIMIT: usize = 20 * 20; // a bitcommitment for u32 cost 20 element in the stack,  limit the stack to 600

trait Planner {
    /// combine
    fn core_combine(infos: Vec<ScriptInfo>, debug: bool) -> ScriptInfo;

    fn combine(mut infos: Vec<ScriptInfo>, debug: bool) -> Vec<ScriptInfo> {
        Self::dry_run_infos(&mut infos);

        let mut script_cnt = 0;
        let mut u32_bc_cnt = 0;
        let mut combined_infos: Vec<ScriptInfo> = vec![];
        let mut res = vec![];
        for info in infos {
            let info_size = info.script_size() + info.witness_size();
            let bc_u32_size = info.witness().len();
            if script_cnt + info_size <= SCRIPT_LIMIT && u32_bc_cnt + bc_u32_size <= SOFT_u32_LIMIT
            {
                script_cnt += info_size;
                u32_bc_cnt += bc_u32_size;
                combined_infos.push(info);
            } else {
                res.push(Self::core_combine(combined_infos, debug));

                // clear status
                script_cnt = info_size;
                u32_bc_cnt = bc_u32_size;
                combined_infos = vec![info];
            }
        }

        // combine last infos
        if !combined_infos.is_empty() {
            res.push(Self::core_combine(combined_infos, debug));
        }

        res
    }

    fn dry_run_infos(infos: &mut Vec<ScriptInfo>) {
        let mut mock_bc_assginer = DefaultBCAssignment::new();
        for info in infos {
            info.gen(&mut mock_bc_assginer);
        }
    }

    /// compile infos to a set of success taprootleafs in debug mode
    fn compile_to_eq(infos: Vec<ScriptInfo>) -> (Vec<TaprootLeaf>, DefaultBCAssignment) {
        // now process res infos
        let mut bc_assigner = DefaultBCAssignment::new();
        let taproot_leafs = Self::combine(infos, true)
            .iter_mut()
            .map(|info: &mut ScriptInfo| TaprootLeaf::from_eq(info.gen(&mut bc_assigner)))
            .collect::<Vec<TaprootLeaf>>();

        (taproot_leafs, bc_assigner)
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
    // warninig: this function shouldn't be use alone, because the res is depended on the `debug` flag.
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
                for j in 0..i {
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
                    // println!("put source {} to offset {}", cell.source, offset);
                } else {
                    bc_values.push(cell.value);
                }
                offset += 1;
            }
        }

        // println!("copy scripts len = {}", copy_script.len());

        let script = script_info! {
            &combined_name,
            script! {
                {ScriptBuf::from(copy_script)}
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

#[cfg(test)]
mod test {
    use bitcoin_script::script;
    use rand_chacha::rand_core::le;
    use scripts::{execute_script_with_inputs, pushable};

    use crate::bc_assignment::{self, DefaultBCAssignment};
    use crate::planner::{Planner, SimplePlanner};
    use crate::script_info;
    use crate::script_info::ScriptInfo;

    // some tests
    #[test]
    fn test_simple_planner() {
        let mut bc_assigner = DefaultBCAssignment::new();
        let mut script1 = script_info!(
            "add1",
            script! {
                OP_ADD
                // OP_ADD
            },
            [1, 2],
            [3]
        );

        let mut script2 = script_info!(
            "add1",
            script! {
                OP_ADD
                // OP_ADD
            },
            [3, 1],
            [4]
        );

        let mut script = SimplePlanner::core_combine(vec![script1, script2], true);
        script.gen(&mut bc_assigner);
        let res = execute_script_with_inputs(script.get_eq_script(), script.witness());
        assert!(res.success);
        assert_eq!(bc_assigner.value_assigns.len(), 4);
    }

    #[test]
    fn test_simple_planner2() {
        let mut bc_assigner = DefaultBCAssignment::new();
        let mut script1 = script_info!(
            "add1",
            script! {
                OP_ADD
                OP_ADD
            },
            [10, 11, 12],
            [33]
        );

        let mut script2 = script_info!(
            "add1",
            script! {
                OP_ADD
                OP_ADD
            },
            [33, 10, 11],
            [54]
        );

        let mut script = SimplePlanner::core_combine(vec![script1, script2], true);
        script.gen(&mut bc_assigner);
        let res = execute_script_with_inputs(script.get_eq_script(), script.witness());
        assert!(res.success);
        assert_eq!(bc_assigner.value_assigns.len(), 5);
    }

    // loop test
    #[test]
    fn test_simple_planner_for_loop() {
        let mut bc_assigner = DefaultBCAssignment::new();
        let mut scripts = vec![];
        let mut sum: u32 = 0;
        for i in 0..10 {
            // record prestate
            let pre_sum = sum;
            sum += 100;
            // record state
            scripts.push(script_info!(
                &format!("add_{}", i),
                script! {
                    {100}
                    OP_ADD
                },
                [pre_sum],
                [sum]
            ));
        }
        assert_eq!(sum, 1000);

        let mut script = SimplePlanner::core_combine(scripts, true);
        script.gen(&mut bc_assigner);
        let res = execute_script_with_inputs(script.get_eq_script(), script.witness());
        assert!(res.success);
        assert_eq!(bc_assigner.value_assigns.len(), 11);
    }

    // two-layer loop test
    #[test]
    fn test_simple_planner_for_loop2() {
        let mut bc_assigner = DefaultBCAssignment::new();
        let mut scripts = vec![];
        let mut sum: u32 = 0;
        for i in 0..10 {
            for j in 0..2 {
                // record prestate
                let pre_sum = sum;
                sum += 10;
                // record state
                scripts.push(script_info!(
                    &format!("add_{}_{}", i, j),
                    script! {
                        {10}
                        OP_ADD
                    },
                    [pre_sum],
                    [sum]
                ));
            }
        }

        println!(
            "single script_size = {}, combined_size = {}",
            scripts
                .get_mut(0)
                .unwrap()
                .gen(&mut bc_assigner)
                .script_size(),
            scripts.len()
        );

        assert_eq!(sum, 200);
        let mut script = SimplePlanner::core_combine(scripts, true);
        script.gen(&mut bc_assigner);
        println!(
            "combined script_size = {}, script_name = {}",
            script.script_size(),
            script.name()
        );
        let res = execute_script_with_inputs(script.get_eq_script(), script.witness());
        println!("res: {:?}", res);
        assert!(res.success);
        // assert_eq!(bc_assigner.value_assigns.len(), 101);
    }

    #[test]
    fn test_simple_planner_for_loop3() {
        let mut bc_assigner = DefaultBCAssignment::new();
        let mut scripts = vec![];
        let mut sum: u32 = 0;
        for i in 0..10 {
            // more loop will lead to be over the stack limit
            for j in 0..4 {
                // record prestate
                let pre_sum = sum;
                sum += 10;
                // record state
                scripts.push(script_info!(
                    &format!("add_{}_{}", i, j),
                    script! {
                        {10}
                        OP_ADD
                    },
                    [pre_sum],
                    [sum]
                ));
            }
        }

        println!(
            "single script_size = {}, combined_size = {}",
            scripts
                .get_mut(0)
                .unwrap()
                .gen(&mut bc_assigner)
                .script_size(),
            scripts.len()
        );

        let mut script = SimplePlanner::core_combine(scripts, true);
        script.gen(&mut bc_assigner);
        println!(
            "combined script_size = {}, script_name = {}",
            script.script_size(),
            script.name()
        );
        let res = execute_script_with_inputs(script.get_eq_script(), script.witness());
        println!("res: {:?}", res);
        assert!(res.success);
        // assert_eq!(bc_assigner.value_assigns.len(), 101);
    }

    #[test]
    fn test_simple_planner_for_loop4() {
        let mut bc_assigner = DefaultBCAssignment::new();
        let mut scripts = vec![];
        let mut sum: u32 = 0;
        for i in 0..10 {
            // more loop will lead to be over the stack limit
            for j in 0..10 {
                // record prestate
                let pre_sum = sum;
                sum += 10;
                // record state
                scripts.push(script_info!(
                    &format!("add_{}_{}", i, j),
                    script! {
                        {10}
                        OP_ADD
                    },
                    [pre_sum],
                    [sum]
                ));
            }
        }

        println!(
            "single script_size = {}, script_info_cnt = {}, total = {}",
            scripts
                .get_mut(0)
                .unwrap()
                .gen(&mut bc_assigner)
                .script_size(),
            scripts.len(),
            scripts
                .get_mut(0)
                .unwrap()
                .gen(&mut bc_assigner)
                .script_size()
                * scripts.len()
        );

        let (leafs, _) = SimplePlanner::compile_to_eq(scripts);
        println!(
            "single combined script_size = {}, combined_script_cnt = {}, total = {}",
            leafs.get(0).unwrap().script_buf.len(),
            leafs.len(),
            leafs.get(0).unwrap().script_buf.len() * leafs.len(),
        );
        for leaf in leafs {
            let res = execute_script_with_inputs(leaf.script_buf, leaf.witness);
            assert_eq!(res.success, true);
        }
    }

    #[test]
    fn test_simple_planner_for_complicated_scripts() {
        let mut bc_assigner = DefaultBCAssignment::new();
        let mut scripts = vec![];
        let mut sum: u32 = 0;
        for i in 0..10 {
            // more loop will lead to be over the stack limit
            let added: u32 = i;
            for j in 0..10 {
                // record prestate
                let pre_sum = sum;
                sum += added;
                // record state
                scripts.push(script_info!(
                    &format!("add_{}_{}", i, j),
                    script! {
                        OP_ADD
                    },
                    [added, pre_sum],
                    [sum]
                ));
            }
        }

        println!(
            "single script_size = {}, script_info_cnt = {}, total = {}",
            scripts
                .get_mut(0)
                .unwrap()
                .gen(&mut bc_assigner)
                .script_size(),
            scripts.len(),
            scripts
                .get_mut(0)
                .unwrap()
                .gen(&mut bc_assigner)
                .script_size()
                * scripts.len()
        );

        let (leafs, _) = SimplePlanner::compile_to_eq(scripts);
        println!(
            "single combined script_size = {}, combined_script_cnt = {}, total = {}",
            leafs.get(0).unwrap().script_buf.len(),
            leafs.len(),
            leafs.get(0).unwrap().script_buf.len() * leafs.len(),
        );
        for leaf in leafs {
            let res = execute_script_with_inputs(leaf.script_buf, leaf.witness);
            assert_eq!(res.success, true);
        }
    }
}
