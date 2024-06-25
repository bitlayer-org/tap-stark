#![feature(generic_const_exprs)]
use bitcoin::blockdata::transaction;
use bitcoin::blockdata::transaction::Transaction;
use bitcoin::hashes::Hash;
// use bitcoin::TapLeafHash;
use bitcoin::taproot::TapLeafHash;
use bitcoin_script::define_pushable;
use bitcoin_scriptexec::{Exec, ExecCtx, ExecutionResult, Options, TxTemplate};

pub mod bit_comm;
pub use bit_comm::*;

pub mod pseudo;

pub use bitvm::hash::blake3;
pub use bitvm::u32::*;

define_pushable!();

#[allow(dead_code)]
pub mod u31_lib {
    pub use bitcoin::ScriptBuf as Script;
    pub use bitcoin_script::{define_pushable, script};
    define_pushable!();

    pub use rust_bitcoin_u31_or_u30::{
        u31_add, u31_double, u31_mul, u31_sub, u31ext_add, u31ext_double, u31ext_equalverify,
        u31ext_mul, u31ext_sub, BabyBear as BabyBearU31, BabyBear4,
    };

    pub fn u31_equalverify() -> Script {
        script! {
            OP_EQUALVERIFY
        }
    }
}
#[allow(dead_code)]
// Re-export what is needed to write treepp scripts
pub mod treepp {
    pub use bitcoin_script::{define_pushable, script};

    pub use crate::execute_script;

    define_pushable!();
    pub use bitcoin::ScriptBuf as Script;
}

pub fn unroll<F, T>(count: u32, mut closure: F) -> Vec<T>
where
    F: FnMut(u32) -> T,
    T: pushable::Pushable,
{
    let mut result = vec![];

    for i in 0..count {
        result.push(closure(i))
    }
    result
}

pub fn execute_script(script: bitcoin::ScriptBuf) -> ExecutionResult {
    let mut exec = Exec::new(
        ExecCtx::Tapscript,
        Options::default(),
        TxTemplate {
            tx: Transaction {
                version: transaction::Version::TWO,
                lock_time: bitcoin::locktime::absolute::LockTime::ZERO,
                input: vec![],
                output: vec![],
            },
            prevouts: vec![],
            input_idx: 0,
            taproot_annex_scriptleaf: Some((TapLeafHash::all_zeros(), None)),
        },
        script,
        vec![],
    )
    .expect("error creating exec");

    loop {
        if exec.exec_next().is_err() {
            break;
        }
    }
    let res = exec.result().unwrap();
    res.clone()
}

pub fn execute_script_with_inputs(
    script: bitcoin::ScriptBuf,
    witness: Vec<Vec<u8>>,
) -> ExecutionResult {
    let mut exec = Exec::new(
        ExecCtx::Tapscript,
        Options::default(),
        TxTemplate {
            tx: Transaction {
                version: bitcoin::transaction::Version::TWO,
                lock_time: bitcoin::locktime::absolute::LockTime::ZERO,
                input: vec![],
                output: vec![],
            },
            prevouts: vec![],
            input_idx: 0,
            taproot_annex_scriptleaf: Some((TapLeafHash::all_zeros(), None)),
        },
        script,
        witness,
    )
    .expect("error creating exec");

    loop {
        let temp_res = exec.exec_next();
        match temp_res {
            Ok(()) => (),
            Err(err) => {
                if err.success == false {
                    println!("temp_res: {:?}", temp_res);
                }
                break;
            }
        }
    }

    let res = exec.result().unwrap();
    res.clone()
}
