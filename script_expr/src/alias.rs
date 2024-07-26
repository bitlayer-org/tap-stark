use std::cell::{Cell, Ref, RefCell};
use std::collections::BTreeMap;
use std::fmt::Debug;
use std::sync::{Arc, RwLock, RwLockReadGuard, RwLockWriteGuard};

use bitcoin_script::script;
use bitcoin_script_stack::stack::StackTracker;
use p3_field::AbstractField;
use primitives::field::BfField;
use scripts::treepp::*;
use scripts::u31_lib::{
    u31_add, u31_mul, u31_neg, u31_sub, u31_sub_u31ext, u31_to_u31ext, u31ext_add, u31ext_add_u31,
    u31ext_equalverify, u31ext_mul, u31ext_mul_u31, u31ext_neg, u31ext_sub, u31ext_sub_u31,
    u32_to_u31, BabyBear4, BabyBearU31,
};

use crate::script_gen::*;
use crate::{CopyVar, Expression, ScriptExprError, StackVariable, Variable};

pub type ExprPtr = Arc<RwLock<Box<dyn Expression>>>;
pub type ExprRead<'a> = RwLockReadGuard<'a, Box<dyn Expression>>;
pub type ExprWrite<'a> = RwLockWriteGuard<'a, Box<dyn Expression>>;
// impl ExprPtr{

// }
