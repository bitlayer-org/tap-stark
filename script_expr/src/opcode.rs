use std::cell::{Cell, RefCell};
use std::fmt::Debug;
use std::marker::PhantomData;
use std::ops::Deref;
use std::sync::{Arc, RwLock};

use basic::field::BfField;

use crate::script_gen::*;
use crate::{ExprPtr, Expression, Variable};

pub(crate) struct Opcode<const INPUT_NUM: usize, const OUTPUT_NUM: usize> {
    id: u32,
    name: RefCell<Option<String>>,
    var_size: u32,
    ops: Vec<ExprPtr>,
    debug: Cell<bool>,
}

impl<const INPUT_NUM: usize, const OUTPUT_NUM: usize> Debug for Opcode<INPUT_NUM, OUTPUT_NUM> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Opcode")
            .field("id", &self.id)
            .field("var_size", &self.var_size)
            .field("ops", &self.ops.len())
            .field("debug", &self.debug)
            .finish()
    }
}

impl<const INPUT_NUM: usize, const OUTPUT_NUM: usize> Clone for Opcode<INPUT_NUM, OUTPUT_NUM> {
    fn clone(&self) -> Self {
        Self {
            id: self.id.clone(),
            name: self.name.clone(),
            var_size: self.var_size,
            ops: self.ops.clone(),
            debug: self.debug.clone(),
        }
    }
}

impl<const INPUT_NUM: usize, const OUTPUT_NUM: usize> Opcode<INPUT_NUM, OUTPUT_NUM> {
    pub(crate) fn new(id: u32, ops: Vec<Arc<RwLock<Box<dyn Expression>>>>, var_size: u32) -> Self {
        Self {
            id: id,
            name: RefCell::new(None),
            ops: ops,
            var_size: var_size,
            debug: Cell::new(false),
        }
    }

    pub(crate) fn get_id(&self) -> u32 {
        self.id
    }

    pub(crate) fn get_name(&self) -> Option<String> {
        self.name.borrow().deref().clone()
    }

    pub(crate) fn set_id(&mut self, id: u32) {
        self.id = id;
    }

    pub(crate) fn set_name(&self, name: String) {
        *self.name.borrow_mut() = Some(name);
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
}

impl<const INPUT_NUM: usize, const OUTPUT_NUM: usize> Expression for Opcode<INPUT_NUM, OUTPUT_NUM> {
    fn as_expr_ptr(self) -> ExprPtr {
        Arc::new(RwLock::new(Box::new(self)))
    }

    fn get_input_number(&self) -> usize {
        INPUT_NUM
    }

    fn get_output_number(&self) -> usize {
        OUTPUT_NUM
    }

    fn get_ops(&self) -> &Vec<ExprPtr> {
        &self.ops
    }

    fn generate_script_fn(&self) -> Arc<Box<StandardOpScriptGen>> {
        unimplemented!()
    }

    fn var_size(&self) -> u32 {
        if self.var_size == 1 || self.var_size == 4 {
            self.var_size
        } else {
            panic!("Invalid var_size")
        }
    }

    fn get_id(&self) -> u32 {
        self.id
    }

    fn set_debug(&self) {
        self.debug.set(true);
    }

    fn is_debug(&self) -> bool {
        self.debug.get()
    }

    fn opcode(&self) -> StandardOpcodeId {
        unimplemented!()
    }
}

pub(crate) struct StandardOpcode<const INPUT_NUM: usize, const OUTPUT_NUM: usize> {
    opcode: Opcode<INPUT_NUM, OUTPUT_NUM>,
    opcode_id: StandardOpcodeId,
    script_gen: Arc<Box<StandardOpScriptGen>>,
}

impl<const INPUT_NUM: usize, const OUTPUT_NUM: usize> StandardOpcode<INPUT_NUM, OUTPUT_NUM> {
    pub(crate) fn new(
        id: u32,
        ops: Vec<Arc<RwLock<Box<dyn Expression>>>>,
        var_size: u32,
        opcode: StandardOpcodeId,
    ) -> Self {
        Self {
            opcode: Opcode::new(id, ops, var_size),
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

    fn get_input_number(&self) -> usize {
        INPUT_NUM
    }

    fn get_output_number(&self) -> usize {
        OUTPUT_NUM
    }

    fn get_ops(&self) -> &Vec<ExprPtr> {
        &self.opcode.ops
    }

    fn generate_script_fn(&self) -> Arc<Box<StandardOpScriptGen>> {
        self.script_gen.clone()
    }

    fn var_size(&self) -> u32 {
        if self.opcode.var_size == 1 || self.opcode.var_size == 4 {
            self.opcode.var_size
        } else {
            panic!("Invalid var_size")
        }
    }

    fn get_id(&self) -> u32 {
        self.opcode.get_id()
    }

    fn set_debug(&self) {
        self.opcode.debug.set(true);
    }

    fn is_debug(&self) -> bool {
        self.opcode.debug.get()
    }

    fn opcode(&self) -> StandardOpcodeId {
        self.opcode_id.into()
    }
}

pub(crate) struct CustomOpcode<const INPUT_NUM: usize, const OUTPUT_NUM: usize, F: BfField> {
    opcode: Opcode<INPUT_NUM, OUTPUT_NUM>,
    custom: Vec<Vec<u32>>,
    opcode_id: StandardOpcodeId,
    script_gen: Arc<Box<StandardOpScriptGen>>,
    _marker: PhantomData<F>,
}
impl<const INPUT_NUM: usize, const OUTPUT_NUM: usize, F: BfField>
    CustomOpcode<INPUT_NUM, OUTPUT_NUM, F>
{
    pub(crate) fn new(
        id: u32,
        custom_data: Vec<Vec<u32>>,
        ops: Vec<Arc<RwLock<Box<dyn Expression>>>>,
        var_size: u32,
        opcode: StandardOpcodeId,
    ) -> Self {
        Self {
            custom: custom_data.clone(),
            opcode: Opcode::new(id, ops, var_size),
            opcode_id: opcode,
            script_gen: Arc::new(custom_script_generator::<F>(opcode, custom_data)),
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

    fn get_input_number(&self) -> usize {
        INPUT_NUM
    }
    fn get_output_number(&self) -> usize {
        OUTPUT_NUM
    }

    fn get_ops(&self) -> &Vec<ExprPtr> {
        &self.opcode.ops
    }

    fn generate_script_fn(&self) -> Arc<Box<StandardOpScriptGen>> {
        self.script_gen.clone()
    }

    fn var_size(&self) -> u32 {
        if self.opcode.var_size == 1 || self.opcode.var_size == 4 || self.opcode.var_size == 0 {
            self.opcode.var_size
        } else {
            panic!("Invalid var_size")
        }
    }

    fn get_id(&self) -> u32 {
        self.opcode.get_id()
    }

    fn set_debug(&self) {
        self.opcode.debug.set(true);
    }

    fn is_debug(&self) -> bool {
        self.opcode.debug.get()
    }

    fn opcode(&self) -> StandardOpcodeId {
        self.opcode_id.into()
    }
}

pub(crate) struct InputOpcode<const INPUT_NUM: usize, const OUTPUT_NUM: usize> {
    opcode: Opcode<INPUT_NUM, OUTPUT_NUM>,
    input_var: Variable,
    opcode_id: StandardOpcodeId,
    script_gen: Arc<Box<StandardOpScriptGen>>,
}
impl<const INPUT_NUM: usize, const OUTPUT_NUM: usize> InputOpcode<INPUT_NUM, OUTPUT_NUM> {
    pub(crate) fn new(
        id: u32,
        input_var: Variable,
        ops: Vec<Arc<RwLock<Box<dyn Expression>>>>,
        var_size: u32,
        opcode: StandardOpcodeId,
    ) -> Self {
        Self {
            input_var: input_var,
            opcode: Opcode::new(id, ops, var_size),
            opcode_id: opcode,
            script_gen: Arc::new(input_script_generator(opcode, input_var)),
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

    fn get_input_number(&self) -> usize {
        INPUT_NUM
    }
    fn get_output_number(&self) -> usize {
        OUTPUT_NUM
    }

    fn get_ops(&self) -> &Vec<ExprPtr> {
        &self.opcode.ops
    }

    fn generate_script_fn(&self) -> Arc<Box<StandardOpScriptGen>> {
        self.script_gen.clone()
    }

    fn var_size(&self) -> u32 {
        if self.opcode.var_size == 1 || self.opcode.var_size == 4 || self.opcode.var_size == 0 {
            self.opcode.var_size
        } else {
            panic!("Invalid var_size")
        }
    }

    fn get_id(&self) -> u32 {
        self.opcode.get_id()
    }

    fn set_debug(&self) {
        self.opcode.debug.set(true);
    }

    fn is_debug(&self) -> bool {
        self.opcode.debug.get()
    }

    fn opcode(&self) -> StandardOpcodeId {
        self.opcode_id.into()
    }
}
