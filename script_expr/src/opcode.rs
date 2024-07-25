use std::cell::{Cell, Ref, RefCell};
use std::collections::BTreeMap;
use std::fmt::Debug;
use std::sync::{Arc, RwLock};

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

pub(crate) enum OpcodeId {
    Add,
    Mul,
    Sub,
    Neg,
}

pub(crate) struct Opcode<const INPUT_NUM: usize, const OUTPUT_NUM: usize> {
    var_size: u32,
    ops: Vec<Arc<RwLock<Box<dyn Expression>>>>,
    value: Option<Vec<u32>>,
    debug: Cell<bool>,
    to_copy_expr: RefCell<Option<Arc<RwLock<Box<dyn Expression>>>>>,
    script_gen: Arc<Box<OpScriptGen>>,
}
impl<const INPUT_NUM: usize, const OUTPUT_NUM: usize> Debug for Opcode<INPUT_NUM, OUTPUT_NUM> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Opcode")
            .field("var_size", &self.var_size)
            .field("ops", &self.ops.len())
            .field("value", &self.value)
            .field("debug", &self.debug)
            .field("to_copy_expr", &self.to_copy_expr.borrow().is_some())
            .finish()
    }
}

impl<const INPUT_NUM: usize, const OUTPUT_NUM: usize> Clone for Opcode<INPUT_NUM, OUTPUT_NUM> {
    fn clone(&self) -> Self {
        Self {
            var_size: self.var_size,
            ops: self.ops.clone(),
            value: self.value.clone(),
            debug: self.debug.clone(),
            to_copy_expr: RefCell::new(self.to_copy_expr.borrow().clone()),
            script_gen: self.script_gen.clone(),
        }
    }
}
impl<const INPUT_NUM: usize, const OUTPUT_NUM: usize> Opcode<INPUT_NUM, OUTPUT_NUM> {
    pub(crate) fn new(
        ops: Vec<Arc<RwLock<Box<dyn Expression>>>>,
        var_size: u32,
        script_gen: Box<OpScriptGen>,
    ) -> Self {
        Self {
            ops: ops,
            var_size: var_size,
            value: None,
            debug: Cell::new(false),
            to_copy_expr: RefCell::new(None),
            script_gen: Arc::new(script_gen),
        }
    }
}

impl<const INPUT_NUM: usize, const OUTPUT_NUM: usize> Expression for Opcode<INPUT_NUM, OUTPUT_NUM> {
    fn as_arc_ptr(self) -> Arc<RwLock<Box<dyn Expression>>> {
        Arc::new(RwLock::new(Box::new(self)))
    }
    fn express_to_script(
        &self,
        stack: &mut StackTracker,
        input_variables: &BTreeMap<Variable, StackVariable>,
    ) {
        for op in self.ops.iter() {
            op.as_ref()
                .read()
                .unwrap()
                .express_to_script(stack, input_variables);
        }

        let vars = (self.script_gen)(vec![1, 1], stack, self.to_copy_expr.borrow());

        if self.debug.get() == true {
            stack.debug();
        }
    }

    fn var_size(&self) -> u32 {
        self.var_size
    }

    fn set_debug(&self) {
        self.debug.set(true);
    }

    fn to_copy(&self) -> Result<Arc<RwLock<Box<dyn Expression>>>, ScriptExprError> {
        if self.to_copy_expr.borrow().is_some() {
            return Err(ScriptExprError::DoubleCopy);
        }

        let copy_self = Arc::new(RwLock::new(
            Box::new(CopyVar::new(self.var_size())) as Box<dyn Expression>
        ));

        *self.to_copy_expr.borrow_mut() = Some(copy_self.clone());
        Ok(copy_self)
    }
}

#[cfg(test)]
mod tests {

    use common::BabyBear;

    use super::*;
    use crate::FieldScriptExpression;

    #[test]
    fn test_for_gen() {
        let op_add_instance: Opcode<2, 1> = Opcode::new(
            vec![
                Arc::new(RwLock::new(
                    Box::new(FieldScriptExpression::from(BabyBear::one())) as Box<dyn Expression>,
                )),
                Arc::new(RwLock::new(
                    Box::new(FieldScriptExpression::from(BabyBear::one())) as Box<dyn Expression>,
                )),
            ],
            4,
            Box::new(op_add::<BabyBear>),
        );

        // let op_add = op_add_instance.as_arc_ptr();
    }
}
