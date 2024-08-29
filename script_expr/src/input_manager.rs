use std::collections::BTreeMap;
use std::sync::{Arc, Mutex, RwLock};

use bitcoin_script_stack::stack::StackTracker;
use primitives::field::BfField;
use tracing::warn;

use crate::script_gen::*;
use crate::variable::VarWithValue;
use crate::{
    get_opid, Dsl, ExprPtr, Expression, IdCount, InputOpcode, StackVariable, ValueCounter, Variable,
};

pub struct ManagerAssign {
    managers: Vec<Arc<Mutex<Box<InputManager>>>>,
    current_index: Option<usize>,
}

impl IntoIterator for ManagerAssign {
    type Item = Arc<Mutex<Box<InputManager>>>;
    type IntoIter = std::vec::IntoIter<Self::Item>;
    fn into_iter(self) -> Self::IntoIter {
        self.managers.into_iter()
    }
}

impl ManagerAssign {
    pub fn new() -> Self {
        Self {
            managers: vec![],
            current_index: None,
        }
    }

    pub fn managers(&self) -> Vec<Arc<Mutex<Box<InputManager>>>> {
        self.managers.clone()
    }

    pub fn clear(&mut self) {
        self.managers = vec![];
        self.current_index = None;
    }

    pub fn add_manager(&mut self) -> Arc<Mutex<Box<InputManager>>> {
        let manager: Arc<Mutex<Box<InputManager>>> =
            Arc::new(Mutex::new(Box::new(InputManager::new())));
        self.managers.push(manager.clone());
        manager
    }

    pub fn add_manager_with_name(&mut self, name: String) -> Arc<Mutex<Box<InputManager>>> {
        let manager: Arc<Mutex<Box<InputManager>>> =
            Arc::new(Mutex::new(Box::new(InputManager::new_with_name(name))));
        self.managers.push(manager.clone());
        manager
    }

    pub fn next_manager(&mut self) -> Arc<Mutex<Box<InputManager>>> {
        if self.current_index.is_none() {
            self.current_index = Some(0);
        } else {
            self.current_index = Some(self.current_index.unwrap() + 1);
        }
        self.add_manager()
    }

    pub fn next_manager_with_name(&mut self, name: String) -> Arc<Mutex<Box<InputManager>>> {
        if self.current_index.is_none() {
            self.current_index = Some(0);
        } else {
            self.current_index = Some(self.current_index.unwrap() + 1);
        }
        self.add_manager_with_name(name)
    }

    pub fn current_manager(&self) -> Arc<Mutex<Box<InputManager>>> {
        self.managers
            .get(self.current_index.unwrap())
            .unwrap()
            .clone()
    }

    pub fn move_current_index(&mut self, index: usize) -> Arc<Mutex<Box<InputManager>>> {
        assert!(index < self.managers.len());
        self.current_index = Some(index);
        self.managers.get(index).unwrap().clone()
    }

    pub fn get_manager(&mut self, index: usize) -> Arc<Mutex<Box<InputManager>>> {
        assert!(index < self.managers.len());
        self.managers.get(index).unwrap().clone()
    }

    pub fn assign_input<EF: BfField>(&self, value: Vec<u32>) -> Dsl<EF> {
        self.current_manager().lock().unwrap().assign_input(value)
    }

    pub fn assign_input_f<EF: BfField>(&self, value: EF) -> Dsl<EF> {
        self.current_manager()
            .lock()
            .unwrap()
            .assign_input(value.as_u32_vec())
    }

    pub fn simulate_input(&self) -> (StackTracker, BTreeMap<Variable, StackVariable>) {
        let binding = self.current_manager();
        let (stack, var_getter) = binding.lock().unwrap().simulate_input();
        (stack, var_getter)
    }

    pub fn set_value_count(&self, value_count: &mut ValueCounter) {
        self.managers.iter().for_each(|manager| {
            let manager = manager.lock().unwrap();
            manager.input_var.iter().for_each(|var| {
                var.value.iter().for_each(|value| {
                    value_count.get_or_set(*value);
                });
            });
        });
    }
}

pub struct InputManager {
    name: String,
    counter: usize,
    input_var: Vec<VarWithValue>,
    input_hint: Vec<VarWithValue>,
    exec_dsl: Option<ExprPtr>,
    hint: Vec<ExprPtr>,
    var_getter: BTreeMap<Variable, StackVariable>,
    id_mapper: BTreeMap<u32, IdCount>,
    stack: StackTracker,
}

impl InputManager {
    pub(crate) fn new() -> Self {
        Self::new_with_name("".to_string())
    }

    pub(crate) fn new_with_name(name: String) -> Self {
        Self {
            name: name,
            counter: 0,
            input_var: vec![],
            input_hint: vec![],
            exec_dsl: None,
            hint: vec![],
            var_getter: BTreeMap::new(),
            stack: StackTracker::new(),
            id_mapper: BTreeMap::new(),
        }
    }

    fn set_name(&mut self, name: String) {
        self.name = name;
    }

    pub fn set_exec_dsl(&mut self, exec_dsl: ExprPtr) {
        self.exec_dsl = Some(exec_dsl);
    }

    pub(crate) fn assign_input_hint(&mut self, value: Vec<u32>) -> Variable {
        let input_var = VarWithValue::new(value, 5, self.counter);
        self.counter += 1;
        self.input_hint.push(input_var.clone());
        input_var.var
    }

    pub(crate) fn assign_input_var(&mut self, value: Vec<u32>) -> Variable {
        let input_var = VarWithValue::new(value, 5, self.counter);
        self.counter += 1;
        self.input_var.push(input_var.clone());
        input_var.var
    }

    pub(crate) fn assign_input_opcode(&mut self, value: Vec<u32>) -> InputOpcode<0, 1> {
        InputOpcode::new(
            get_opid(),
            self.assign_input_var(value.clone()),
            vec![],
            value.len() as u32,
            StandardOpcodeId::InputVarMove,
        )
    }

    pub(crate) fn assign_input_hint_opcode(&mut self, value: Vec<u32>) -> InputOpcode<0, 1> {
        InputOpcode::new(
            get_opid(),
            self.assign_input_hint(value.clone()),
            vec![],
            value.len() as u32,
            StandardOpcodeId::InputVarMove,
        )
    }

    pub fn assign_input<EF: BfField>(&mut self, value: Vec<u32>) -> Dsl<EF> {
        Dsl::<EF>::new(Arc::new(RwLock::new(Box::new(
            self.assign_input_opcode(value),
        ))))
    }

    pub fn assign_input_f<EF: BfField>(&mut self, value: EF) -> Dsl<EF> {
        self.assign_input(value.as_u32_vec())
    }

    pub(crate) fn assign_hint_input<EF: BfField>(&mut self, value: Vec<u32>) -> Dsl<EF> {
        Dsl::<EF>::new(Arc::new(RwLock::new(Box::new(
            self.assign_input_hint_opcode(value),
        ))))
    }

    pub fn assign_hint_input_f<EF: BfField>(&mut self, value: EF) -> Dsl<EF> {
        self.assign_hint_input(value.as_u32_vec())
    }

    pub fn add_hint_verify(&mut self, expr: ExprPtr) {
        self.hint.push(expr);
    }

    pub fn embed_hint_verify<F: BfField>(&mut self) {
        self.hint.iter().for_each(|hint| {
            self.exec_dsl = Some(
                Dsl::<F>::new(self.exec_dsl.clone().unwrap())
                    .equal(Dsl::<F>::new(hint.clone()))
                    .into(),
            );
        })
    }

    pub(crate) fn simulate_input(&mut self) -> (StackTracker, BTreeMap<Variable, StackVariable>) {
        self.input_var.iter().rev().for_each(|var| {
            let stack_var = self.stack.bignumber(var.value.clone());
            self.var_getter.insert(var.var, stack_var);
        });

        self.input_hint.iter().rev().for_each(|var| {
            let stack_var = self.stack.bignumber(var.value.clone());
            self.var_getter.insert(var.var, stack_var);
        });
        (self.stack.clone(), self.var_getter.clone())
    }

    pub fn run(&mut self, debug: bool) {
        if self.exec_dsl.is_none() {
            warn!("No expression to run");
            return;
        }
        self.simulate_input();
        self.exec_dsl
            .clone()
            .unwrap()
            .read()
            .unwrap()
            .simulate_express(&mut self.id_mapper);
        self.exec_dsl
            .clone()
            .unwrap()
            .read()
            .unwrap()
            .express_to_script(&mut self.stack, &self.var_getter, &mut self.id_mapper, true);

        if debug {
            self.stack.debug();
        }
        assert!(self.stack.run().success);
    }

    pub fn get_script_len(&self) -> usize {
        if self.exec_dsl.is_none() {
            warn!("No expression to run");
            return 0;
        }
        self.stack.get_script().len()
    }

    pub fn print_script_len(&self) -> usize {
        let sl = self.get_script_len() / 1024;
        println!("name:{} ; script_len: {}-kb", self.name, sl);
        sl
    }
}

#[cfg(test)]
mod tests {
    use common::{BabyBear, BinomialExtensionField};
    use p3_field::AbstractField;
    use primitives::field::BfField;

    use super::InputManager;
    use crate::{Dsl, ManagerAssign, ValueCounter};

    #[test]
    fn test_input_manager_assign() {
        let mut input_manager = InputManager::new();
        let val = BabyBear::from_u32(3);
        let val_inv = BabyBear::one() / val;
        let a = input_manager.assign_input::<BabyBear>(val.as_u32_vec());
        let b = input_manager.assign_input::<BabyBear>(BabyBear::from_u32(3).as_u32_vec());
        let c = input_manager.assign_input::<BabyBear>(BabyBear::from_u32(100).as_u32_vec());

        let c = (a.clone() + b.clone() + b.square()) * c;
        let equal = c.equal_for_f(BabyBear::from_canonical_u32(1500));
        input_manager.set_exec_dsl(equal.into());

        let val_inv_dsl = input_manager.assign_hint_input_f::<BabyBear>(val_inv);
        let hint1 = a * val_inv_dsl;
        input_manager.add_hint_verify(hint1.into());

        input_manager.embed_hint_verify::<BabyBear>();
        input_manager.run(false);
    }

    #[test]
    fn test_manager_assign() {
        type EF = BinomialExtensionField<BabyBear, 4>;
        let mut manager_assign = ManagerAssign::new();
        for _ in 0..10 {
            manager_assign.next_manager();
            let a = manager_assign.assign_input::<BabyBear>(BabyBear::from_u32(3).as_u32_vec());
            let b = manager_assign.assign_input::<BabyBear>(BabyBear::from_u32(3).as_u32_vec());
            let c = manager_assign.assign_input_f::<BabyBear>(BabyBear::from_u32(100));
            let (mut stack, var_getter) = manager_assign.simulate_input();

            let c = (a + b.clone() + b.square()) * c + BabyBear::from_u32(1);
            let d = c.mul_ext(Dsl::<EF>::from(EF::from_u32(2)));
            let equal = d.equal_for_f(EF::from_u32(3002));
            let res = equal.express1(&mut stack, &var_getter, true);
            assert!(stack.run().success);
        }

        for _ in 0..10 {
            let cur_manager = manager_assign.next_manager();
            let a = cur_manager
                .lock()
                .unwrap()
                .assign_input::<BabyBear>(BabyBear::from_u32(3).as_u32_vec());
            let b = cur_manager
                .lock()
                .unwrap()
                .assign_input::<BabyBear>(BabyBear::from_u32(3).as_u32_vec());
            let c = cur_manager
                .lock()
                .unwrap()
                .assign_input_f::<BabyBear>(BabyBear::from_u32(100));
            let (mut stack, var_getter) = cur_manager.lock().unwrap().simulate_input();

            let c = (a + b.clone() + b.square()) * c + BabyBear::from_u32(1);
            let d = c.mul_ext(Dsl::<EF>::from(EF::from_u32(2)));
            let equal = d.equal_for_f(EF::from_u32(3002));
            equal.express1(&mut stack, &var_getter, true);
            assert!(stack.run().success);
        }

        let mut vc = ValueCounter::new();
        manager_assign.set_value_count(&mut vc);
        println!("value count: {}", vc.get_value_num());
        assert_eq!(vc.get_value_num(), 2);
    }
}
