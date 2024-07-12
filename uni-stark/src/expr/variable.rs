use core::cell::Cell;
use core::fmt::Debug;
use core::ops::{Add, Mul, Sub};

use bitcoin_script_stack::stack::StackVariable;
use p3_field::Field;
use primitives::field::BfField;

use super::ScriptExpression;
use crate::symbolic_variable::SymbolicVariable;
use crate::Entry;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ValueVariable<F: BfField> {
    var: Variable,
    value: Option<F>,
}

impl<F: BfField> ValueVariable<F> {
    pub fn new(var: Variable, value: F) -> Self {
        Self {
            var,
            value: Some(value),
        }
    }

    pub fn get_var(&self) -> &Variable {
        &self.var
    }

    pub fn get_value(&self) -> Option<F> {
        self.value.clone()
    }
}

impl<F: BfField> From<ValueVariable<F>> for ScriptExpression<F> {
    fn from(var: ValueVariable<F>) -> Self {
        Self::ValueVariable {
            v: var,
            debug: Cell::new(false),
            var: StackVariable::null(),
        }
    }
}

impl<F: BfField> Add for ValueVariable<F> {
    type Output = ScriptExpression<F>;

    fn add(self, rhs: Self) -> Self::Output {
        ScriptExpression::<F>::from(self) + ScriptExpression::<F>::from(rhs)
    }
}

impl<F: BfField> Add<F> for ValueVariable<F> {
    type Output = ScriptExpression<F>;

    fn add(self, rhs: F) -> Self::Output {
        ScriptExpression::<F>::from(self) + ScriptExpression::<F>::from(rhs)
    }
}

impl<F: BfField> Add<ScriptExpression<F>> for ValueVariable<F> {
    type Output = ScriptExpression<F>;

    fn add(self, rhs: ScriptExpression<F>) -> Self::Output {
        ScriptExpression::from(self) + rhs
    }
}

impl<F: BfField> Add<ValueVariable<F>> for ScriptExpression<F> {
    type Output = Self;

    fn add(self, rhs: ValueVariable<F>) -> Self::Output {
        self + Self::from(rhs)
    }
}

impl<F: BfField> Sub for ValueVariable<F> {
    type Output = ScriptExpression<F>;

    fn sub(self, rhs: Self) -> Self::Output {
        ScriptExpression::<F>::from(self) - ScriptExpression::<F>::from(rhs)
    }
}

impl<F: BfField> Sub<F> for ValueVariable<F> {
    type Output = ScriptExpression<F>;

    fn sub(self, rhs: F) -> Self::Output {
        ScriptExpression::<F>::from(self) - ScriptExpression::<F>::from(rhs)
    }
}

impl<F: BfField> Sub<ScriptExpression<F>> for ValueVariable<F> {
    type Output = ScriptExpression<F>;

    fn sub(self, rhs: ScriptExpression<F>) -> Self::Output {
        ScriptExpression::<F>::from(self) - rhs
    }
}

impl<F: BfField> Sub<ValueVariable<F>> for ScriptExpression<F> {
    type Output = Self;

    fn sub(self, rhs: ValueVariable<F>) -> Self::Output {
        self - Self::from(rhs)
    }
}

impl<F: BfField> Mul for ValueVariable<F> {
    type Output = ScriptExpression<F>;

    fn mul(self, rhs: Self) -> Self::Output {
        ScriptExpression::<F>::from(self) * ScriptExpression::<F>::from(rhs)
    }
}

impl<F: BfField> Mul<F> for ValueVariable<F> {
    type Output = ScriptExpression<F>;

    fn mul(self, rhs: F) -> Self::Output {
        ScriptExpression::<F>::from(self) * ScriptExpression::<F>::from(rhs)
    }
}

impl<F: BfField> Mul<ScriptExpression<F>> for ValueVariable<F> {
    type Output = ScriptExpression<F>;

    fn mul(self, rhs: ScriptExpression<F>) -> Self::Output {
        ScriptExpression::<F>::from(self) * rhs
    }
}

impl<F: BfField> Mul<ValueVariable<F>> for ScriptExpression<F> {
    type Output = Self;

    fn mul(self, rhs: ValueVariable<F>) -> Self::Output {
        self * Self::from(rhs)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Variable {
    row_index: usize,
    column_index: usize,
    expect_var_size: Option<u32>,
}

impl Variable {
    pub fn new(row_index: usize, column_index: usize) -> Self {
        Variable {
            row_index,
            column_index,
            expect_var_size: None,
        }
    }

    pub fn new_base(row_index: usize, column_index: usize) -> Self {
        Variable {
            row_index,
            column_index,
            expect_var_size: Some(1),
        }
    }

    pub fn new_ext(row_index: usize, column_index: usize) -> Self {
        Variable {
            row_index,
            column_index,
            expect_var_size: Some(4),
        }
    }

    pub fn new_with_size(row_index: usize, column_index: usize, expect_var_size: u32) -> Self {
        Variable {
            row_index,
            column_index,
            expect_var_size: Some(expect_var_size),
        }
    }

    pub fn get_var_size(&self) -> Option<u32> {
        self.expect_var_size
    }
}

impl<F: BfField> From<Variable> for ScriptExpression<F> {
    fn from(var: Variable) -> Self {
        Self::InputVariable {
            sv: var,
            debug: Cell::new(false),
            var: StackVariable::null(),
        }
    }
}

impl<F: Field> From<SymbolicVariable<F>> for Variable {
    fn from(value: SymbolicVariable<F>) -> Self {
        match value.entry {
            Entry::Main { offset } => Variable {
                row_index: value.index,
                column_index: offset,
                expect_var_size: None,
            },
            Entry::Permutation { offset } => Variable {
                row_index: value.index,
                column_index: offset,
                expect_var_size: None,
            },
            Entry::Preprocessed { offset } => Variable {
                row_index: value.index,
                column_index: offset,
                expect_var_size: None,
            },
            _ => panic!("error type"),
        }
    }
}

impl<F: Field> From<&SymbolicVariable<F>> for Variable {
    fn from(value: &SymbolicVariable<F>) -> Self {
        match value.entry {
            Entry::Main { offset } => Variable {
                row_index: value.index,
                column_index: offset,
                expect_var_size: None,
            },
            Entry::Permutation { offset } => Variable {
                row_index: value.index,
                column_index: offset,
                expect_var_size: None,
            },
            Entry::Preprocessed { offset } => Variable {
                row_index: value.index,
                column_index: offset,
                expect_var_size: None,
            },
            _ => panic!("error type"),
        }
    }
}

impl<F: BfField> Add<F> for Variable {
    type Output = ScriptExpression<F>;

    fn add(self, rhs: F) -> Self::Output {
        ScriptExpression::<F>::from(self) + ScriptExpression::<F>::from(rhs)
    }
}

impl<F: BfField> Add<ScriptExpression<F>> for Variable {
    type Output = ScriptExpression<F>;

    fn add(self, rhs: ScriptExpression<F>) -> Self::Output {
        ScriptExpression::from(self) + rhs
    }
}

impl<F: BfField> Add<Variable> for ScriptExpression<F> {
    type Output = Self;

    fn add(self, rhs: Variable) -> Self::Output {
        self + Self::from(rhs)
    }
}

impl<F: BfField> Sub<F> for Variable {
    type Output = ScriptExpression<F>;

    fn sub(self, rhs: F) -> Self::Output {
        ScriptExpression::<F>::from(self) - ScriptExpression::<F>::from(rhs)
    }
}

impl<F: BfField> Sub<ScriptExpression<F>> for Variable {
    type Output = ScriptExpression<F>;

    fn sub(self, rhs: ScriptExpression<F>) -> Self::Output {
        ScriptExpression::<F>::from(self) - rhs
    }
}

impl<F: BfField> Sub<Variable> for ScriptExpression<F> {
    type Output = Self;

    fn sub(self, rhs: Variable) -> Self::Output {
        self - Self::from(rhs)
    }
}

impl<F: BfField> Mul<F> for Variable {
    type Output = ScriptExpression<F>;

    fn mul(self, rhs: F) -> Self::Output {
        ScriptExpression::<F>::from(self) * ScriptExpression::<F>::from(rhs)
    }
}

impl<F: BfField> Mul<ScriptExpression<F>> for Variable {
    type Output = ScriptExpression<F>;

    fn mul(self, rhs: ScriptExpression<F>) -> Self::Output {
        ScriptExpression::<F>::from(self) * rhs
    }
}

impl<F: BfField> Mul<Variable> for ScriptExpression<F> {
    type Output = Self;

    fn mul(self, rhs: Variable) -> Self::Output {
        self * Self::from(rhs)
    }
}
