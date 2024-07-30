use std::cell::{Cell, Ref, RefCell};
use std::collections::BTreeMap;
use std::fmt::Debug;
use std::marker::PhantomData;
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
use crate::{CopyVar, ExprPtr, Expression, ScriptExprError, StackVariable, Variable};

fn to_copy(
    low_var: StackVariable,
    stack: &mut StackTracker,
    copy_ref: Ref<Option<Arc<RwLock<Box<dyn Expression>>>>>,
) -> Option<StackVariable> {
    if copy_ref.is_none() {
        return None;
    }
    let top_var = stack.copy_var(low_var);
    copy_ref
        .as_ref()
        .unwrap()
        .read()
        .unwrap()
        .set_copy_var(low_var);
    Some(top_var)
}

pub(crate) struct Opcode<const INPUT_NUM: usize, const OUTPUT_NUM: usize> {
    var_size: u32,
    ops: Vec<ExprPtr>,
    debug: Cell<bool>,
    to_copy_expr: RefCell<Option<ExprPtr>>,
}

impl<const INPUT_NUM: usize, const OUTPUT_NUM: usize> Debug for Opcode<INPUT_NUM, OUTPUT_NUM> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Opcode")
            .field("var_size", &self.var_size)
            .field("ops", &self.ops.len())
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
            debug: self.debug.clone(),
            to_copy_expr: RefCell::new(self.to_copy_expr.borrow().clone()),
        }
    }
}

impl<const INPUT_NUM: usize, const OUTPUT_NUM: usize> Opcode<INPUT_NUM, OUTPUT_NUM> {
    pub(crate) fn new(ops: Vec<Arc<RwLock<Box<dyn Expression>>>>, var_size: u32) -> Self {
        Self {
            ops: ops,
            var_size: var_size,
            debug: Cell::new(false),
            to_copy_expr: RefCell::new(None),
        }
    }

    fn check_input_num(&self) {
        assert_eq!(self.ops.len(), INPUT_NUM);
    }

    fn var_size(&self) -> u32 {
        if self.var_size == 1 || self.var_size == 4 {
            self.var_size
        } else {
            panic!("Invalid var_size")
        }
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

pub(crate) struct StandardOpcode<const INPUT_NUM: usize, const OUTPUT_NUM: usize> {
    opcode: Opcode<INPUT_NUM, OUTPUT_NUM>,
    opcode_id: StandardOpcodeId,
    script_gen: Arc<Box<StandardOpScriptGen>>,
}
impl<const INPUT_NUM: usize, const OUTPUT_NUM: usize> StandardOpcode<INPUT_NUM, OUTPUT_NUM> {
    pub(crate) fn new(
        ops: Vec<Arc<RwLock<Box<dyn Expression>>>>,
        var_size: u32,
        opcode: StandardOpcodeId,
    ) -> Self {
        Self {
            opcode: Opcode::new(ops, var_size),
            opcode_id: opcode,
            script_gen: Arc::new(standard_script_genreator(opcode)),
        }
    }

    fn check_input_num(&self) {
        self.opcode.check_input_num();
    }
}

impl<const INPUT_NUM: usize, const OUTPUT_NUM: usize> Debug
    for StandardOpcode<INPUT_NUM, OUTPUT_NUM>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StandardOpcode")
            .field("opcode", &self.opcode)
            .field("opcode_Id", &self.opcode_id)
            .finish()
    }
}

impl<const INPUT_NUM: usize, const OUTPUT_NUM: usize> Clone
    for StandardOpcode<INPUT_NUM, OUTPUT_NUM>
{
    fn clone(&self) -> Self {
        Self {
            opcode: self.opcode.clone(),
            opcode_id: self.opcode_id,
            script_gen: self.script_gen.clone(),
        }
    }
}

impl<const INPUT_NUM: usize, const OUTPUT_NUM: usize> Expression
    for StandardOpcode<INPUT_NUM, OUTPUT_NUM>
{
    fn as_expr_ptr(self) -> ExprPtr {
        Arc::new(RwLock::new(Box::new(self)))
    }
    fn express_to_script(
        &self,
        stack: &mut StackTracker,
        input_variables: &BTreeMap<Variable, StackVariable>,
    ) -> Vec<StackVariable> {
        self.check_input_num();

        let vars_size: Vec<u32> = self
            .opcode
            .ops
            .iter()
            .map(|op| {
                op.as_ref()
                    .read()
                    .unwrap()
                    .express_to_script(stack, input_variables);
                op.as_ref().read().unwrap().var_size()
            })
            .collect();

        let mut vars = (self.script_gen)(vars_size, stack, self.opcode.to_copy_expr.borrow());

        // check output
        assert_eq!(vars.len(), OUTPUT_NUM);

        // copy case
        if OUTPUT_NUM == 1 {
            let copy_var = to_copy(vars[0], stack, self.opcode.to_copy_expr.borrow());
            if copy_var.is_some() {
                println!("copy case custom");
                vars = vec![copy_var.unwrap()];
            }
        }
        stack.debug();
        if self.opcode.debug.get() == true {
            stack.debug();
        }
        vars
    }

    fn var_size(&self) -> u32 {
        if self.opcode.var_size == 1 || self.opcode.var_size == 4 {
            self.opcode.var_size
        } else {
            panic!("Invalid var_size")
        }
    }

    fn set_debug(&self) {
        self.opcode.debug.set(true);
    }

    fn to_copy(&self) -> Result<Arc<RwLock<Box<dyn Expression>>>, ScriptExprError> {
        if self.opcode.to_copy_expr.borrow().is_some() {
            return Err(ScriptExprError::DoubleCopy);
        }

        let copy_self = Arc::new(RwLock::new(
            Box::new(CopyVar::new(self.var_size())) as Box<dyn Expression>
        ));

        *self.opcode.to_copy_expr.borrow_mut() = Some(copy_self.clone());
        Ok(copy_self)
    }
}

pub(crate) struct CustomOpcode<const INPUT_NUM: usize, const OUTPUT_NUM: usize, F: BfField> {
    opcode: Opcode<INPUT_NUM, OUTPUT_NUM>,
    custom: Vec<u32>,
    opcode_id: CustomOpcodeId,
    script_gen: Arc<Box<CustomOpScriptGen>>,
    _marker: PhantomData<F>,
}
impl<const INPUT_NUM: usize, const OUTPUT_NUM: usize, F: BfField>
    CustomOpcode<INPUT_NUM, OUTPUT_NUM, F>
{
    pub(crate) fn new(
        custom_data: Vec<u32>,
        ops: Vec<Arc<RwLock<Box<dyn Expression>>>>,
        var_size: u32,
        opcode: CustomOpcodeId,
    ) -> Self {
        Self {
            custom: custom_data,
            opcode: Opcode::new(ops, var_size),
            opcode_id: opcode,
            script_gen: Arc::new(custom_script_generator::<F>(opcode)),
            _marker: PhantomData,
        }
    }

    fn check_input_num(&self) {
        self.opcode.check_input_num();
    }
}

impl<const INPUT_NUM: usize, const OUTPUT_NUM: usize, F: BfField> Debug
    for CustomOpcode<INPUT_NUM, OUTPUT_NUM, F>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ValueOpcode")
            .field("opcode", &self.opcode)
            .field("opcode_Id", &self.opcode_id)
            .finish()
    }
}

impl<const INPUT_NUM: usize, const OUTPUT_NUM: usize, F: BfField> Clone
    for CustomOpcode<INPUT_NUM, OUTPUT_NUM, F>
{
    fn clone(&self) -> Self {
        Self {
            custom: self.custom.clone(),
            opcode: self.opcode.clone(),
            opcode_id: self.opcode_id,
            script_gen: self.script_gen.clone(),
            _marker: PhantomData,
        }
    }
}

impl<const INPUT_NUM: usize, const OUTPUT_NUM: usize, F: BfField> Expression
    for CustomOpcode<INPUT_NUM, OUTPUT_NUM, F>
{
    fn as_expr_ptr(self) -> ExprPtr {
        Arc::new(RwLock::new(Box::new(self)))
    }
    fn express_to_script(
        &self,
        stack: &mut StackTracker,
        input_variables: &BTreeMap<Variable, StackVariable>,
    ) -> Vec<StackVariable> {
        self.check_input_num();

        let vars_size: Vec<u32> = self
            .opcode
            .ops
            .iter()
            .map(|op| {
                op.as_ref()
                    .read()
                    .unwrap()
                    .express_to_script(stack, input_variables);
                op.as_ref().read().unwrap().var_size()
            })
            .collect();

        let mut vars = (self.script_gen)(
            self.custom.clone(),
            vars_size,
            stack,
            self.opcode.to_copy_expr.borrow(),
        );

        // check output
        assert_eq!(vars.len(), OUTPUT_NUM);

        // copy case
        if OUTPUT_NUM == 1 {
            let copy_var = to_copy(vars[0], stack, self.opcode.to_copy_expr.borrow());
            if copy_var.is_some() {
                vars = vec![copy_var.unwrap()];
            }
        }
        stack.debug();
        if self.opcode.debug.get() == true {
            stack.debug();
        }
        vars
    }

    fn var_size(&self) -> u32 {
        if self.opcode.var_size == 1 || self.opcode.var_size == 4 {
            self.opcode.var_size
        } else {
            panic!("Invalid var_size")
        }
    }

    fn set_debug(&self) {
        self.opcode.debug.set(true);
    }

    fn to_copy(&self) -> Result<Arc<RwLock<Box<dyn Expression>>>, ScriptExprError> {
        if self.opcode.to_copy_expr.borrow().is_some() {
            return Err(ScriptExprError::DoubleCopy);
        }

        let copy_self = Arc::new(RwLock::new(
            Box::new(CopyVar::new(self.var_size())) as Box<dyn Expression>
        ));

        *self.opcode.to_copy_expr.borrow_mut() = Some(copy_self.clone());
        Ok(copy_self)
    }
}
