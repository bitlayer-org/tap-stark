use std::cell::{Cell, Ref, RefCell};
use std::collections::BTreeMap;
use std::fmt::Debug;
use std::marker::PhantomData;
use std::sync::{Arc, RwLock};

use bitcoin::psbt::Input;
use bitcoin_script::script;
use bitcoin_script_stack::stack::StackTracker;
use p3_field::AbstractField;
use primitives::field::BfField;

use crate::script_gen::*;
use crate::variable::VarWithValue;
use crate::{
    CopyVar, ExprPtr, Expression, FieldScriptExpression, ScriptExprError, StackVariable,
    ValueVariable, Variable,
};

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

    pub(crate) fn get_op_expr_ptr(&self, index: usize) -> ExprPtr {
        self.ops[index].clone()
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

        let mut vars = (self.script_gen)(vars_size, stack);

        // check output
        assert_eq!(vars.len(), OUTPUT_NUM);

        // copy case
        if OUTPUT_NUM == 1 {
            let copy_var = to_copy(vars[0], stack, self.opcode.to_copy_expr.borrow());
            if copy_var.is_some() {
                vars = vec![copy_var.unwrap()];
            }
        }

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

    fn opcode(&self) -> OpcodeId {
        self.opcode_id.into()
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

        let mut vars = (self.script_gen)(self.custom.clone(), vars_size, stack);

        // check output
        assert_eq!(vars.len(), OUTPUT_NUM);

        // copy case
        if OUTPUT_NUM == 1 {
            let copy_var = to_copy(vars[0], stack, self.opcode.to_copy_expr.borrow());
            if copy_var.is_some() {
                vars = vec![copy_var.unwrap()];
            }
        }

        if self.opcode.debug.get() == true {
            stack.debug();
        }
        vars
    }

    fn var_size(&self) -> u32 {
        if self.opcode.var_size == 1 || self.opcode.var_size == 4 || self.opcode.var_size == 0 {
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

    fn opcode(&self) -> OpcodeId {
        self.opcode_id.into()
    }
}

pub(crate) struct InputOpcode<const INPUT_NUM: usize, const OUTPUT_NUM: usize> {
    opcode: Opcode<INPUT_NUM, OUTPUT_NUM>,
    input_var: Variable,
    opcode_id: InputOpcodeId,
    script_gen: Arc<Box<InputOpScriptGen>>,
}
impl<const INPUT_NUM: usize, const OUTPUT_NUM: usize> InputOpcode<INPUT_NUM, OUTPUT_NUM> {
    pub(crate) fn new(
        input_var: Variable,
        ops: Vec<Arc<RwLock<Box<dyn Expression>>>>,
        var_size: u32,
        opcode: InputOpcodeId,
    ) -> Self {
        Self {
            input_var: input_var,
            opcode: Opcode::new(ops, var_size),
            opcode_id: opcode,
            script_gen: Arc::new(input_script_generator(opcode)),
        }
    }

    fn check_input_num(&self) {
        self.opcode.check_input_num();
    }
}

impl<const INPUT_NUM: usize, const OUTPUT_NUM: usize> Debug for InputOpcode<INPUT_NUM, OUTPUT_NUM> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ValueOpcode")
            .field("opcode", &self.opcode)
            .field("opcode_id", &self.opcode_id)
            .finish()
    }
}

impl<const INPUT_NUM: usize, const OUTPUT_NUM: usize> Clone for InputOpcode<INPUT_NUM, OUTPUT_NUM> {
    fn clone(&self) -> Self {
        Self {
            input_var: self.input_var.clone(),
            opcode: self.opcode.clone(),
            opcode_id: self.opcode_id,
            script_gen: self.script_gen.clone(),
        }
    }
}

impl<const INPUT_NUM: usize, const OUTPUT_NUM: usize> Expression
    for InputOpcode<INPUT_NUM, OUTPUT_NUM>
{
    fn as_expr_ptr(self) -> ExprPtr {
        Arc::new(RwLock::new(Box::new(self)))
    }
    fn express_to_script(
        &self,
        stack: &mut StackTracker,
        var_getter: &BTreeMap<Variable, StackVariable>,
    ) -> Vec<StackVariable> {
        self.check_input_num();

        let mut vars = (self.script_gen)(
            self.input_var,
            vec![self.opcode.var_size()],
            stack,
            var_getter,
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

    fn opcode(&self) -> OpcodeId {
        self.opcode_id.into()
    }
}

pub(crate) struct InputManager<F: BfField> {
    trace_open: Vec<ValueVariable<F>>,
    public_vars: Vec<VarWithValue>,
    counter: usize,
    input_vars: Vec<VarWithValue>,
    var_getter: BTreeMap<Variable, StackVariable>,
}

impl<F: BfField> InputManager<F> {
    pub(crate) fn new() -> Self {
        Self {
            trace_open: Vec::new(),
            public_vars: Vec::new(),
            counter: 0,
            input_vars: vec![],
            var_getter: BTreeMap::new(),
        }
    }

    pub(crate) fn assign_input_var(&mut self, value: Vec<u32>) -> Variable {
        let input_var = VarWithValue::new(value, 5, self.counter);
        self.counter += 1;
        self.input_vars.push(input_var.clone());
        input_var.var
    }

    pub(crate) fn assign_input_opcode(&mut self, value: Vec<u32>) -> InputOpcode<0, 1> {
        InputOpcode::new(
            self.assign_input_var(value.clone()),
            vec![],
            value.len() as u32,
            InputOpcodeId::InputVarMove,
        )
    }

    pub(crate) fn assign_input_expr(&mut self, value: Vec<u32>) -> FieldScriptExpression<F> {
        FieldScriptExpression::InputVarMove(self.assign_input_opcode(value.clone()))
    }

    pub(crate) fn simulate_input(&mut self) -> (StackTracker, &BTreeMap<Variable, StackVariable>) {
        let mut stack = StackTracker::new();
        self.input_vars.iter().rev().for_each(|var| {
            let stack_var = stack.bignumber(var.value.clone());
            self.var_getter.insert(var.var, stack_var);
        });
        (stack, &self.var_getter)
    }

    // pub(crate) fn end(&mut self, stack: &mut StackTracker){
    //     self.input_vars.iter().for_each(|var|{
    //         let stack_var = self.var_getter.get(&var.var).unwrap();
    //         println!("Dropping {:?}",stack_var);
    //         stack.drop(stack_var.clone());
    //     });
    // }

    fn generate_input(&self) {}
}
