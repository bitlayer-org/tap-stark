use core::fmt::Debug;
use core::ops::{Add, Mul, Sub};
use std::sync::{Arc, RwLock};

use primitives::field::BfField;

use super::Dsl;
use crate::{get_opid, InputOpcode, StandardOpcodeId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ValueVariable<F: BfField> {
    var: Variable,
    value: Option<F>,
}

impl<F: BfField> ValueVariable<F> {
    pub fn new(var: Variable, value: F) -> Self {
        assert_eq!(var.expect_var_size.unwrap(), F::U32_SIZE as u32);
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

impl<F: BfField> From<ValueVariable<F>> for Dsl<F> {
    fn from(var: ValueVariable<F>) -> Self {
        Dsl::new(Arc::new(RwLock::new(Box::new(InputOpcode::<0, 1>::new(
            get_opid(),
            var.into(),
            vec![],
            F::U32_SIZE as u32,
            StandardOpcodeId::InputVarCopy,
        )))))
    }
}

impl<F: BfField> Add for ValueVariable<F> {
    type Output = Dsl<F>;

    fn add(self, rhs: Self) -> Self::Output {
        Dsl::<F>::from(self) + Dsl::<F>::from(rhs)
    }
}

impl<F: BfField> Add<F> for ValueVariable<F> {
    type Output = Dsl<F>;

    fn add(self, rhs: F) -> Self::Output {
        Dsl::<F>::from(self) + Dsl::<F>::constant_f(rhs)
    }
}

impl<F: BfField> Add<Dsl<F>> for ValueVariable<F> {
    type Output = Dsl<F>;

    fn add(self, rhs: Dsl<F>) -> Self::Output {
        Dsl::from(self) + rhs
    }
}

impl<F: BfField> Add<ValueVariable<F>> for Dsl<F> {
    type Output = Self;

    fn add(self, rhs: ValueVariable<F>) -> Self::Output {
        self + Self::from(rhs)
    }
}

impl<F: BfField> Sub for ValueVariable<F> {
    type Output = Dsl<F>;

    fn sub(self, rhs: Self) -> Self::Output {
        Dsl::<F>::from(self) - Dsl::<F>::from(rhs)
    }
}

impl<F: BfField> Sub<F> for ValueVariable<F> {
    type Output = Dsl<F>;

    fn sub(self, rhs: F) -> Self::Output {
        Dsl::<F>::from(self) - Dsl::<F>::constant_f(rhs)
    }
}

impl<F: BfField> Sub<Dsl<F>> for ValueVariable<F> {
    type Output = Dsl<F>;

    fn sub(self, rhs: Dsl<F>) -> Self::Output {
        Dsl::<F>::from(self) - rhs
    }
}

impl<F: BfField> Sub<ValueVariable<F>> for Dsl<F> {
    type Output = Self;

    fn sub(self, rhs: ValueVariable<F>) -> Self::Output {
        self - Self::from(rhs)
    }
}

impl<F: BfField> Mul for ValueVariable<F> {
    type Output = Dsl<F>;

    fn mul(self, rhs: Self) -> Self::Output {
        Dsl::<F>::from(self) * Dsl::<F>::from(rhs)
    }
}

impl<F: BfField> Mul<F> for ValueVariable<F> {
    type Output = Dsl<F>;

    fn mul(self, rhs: F) -> Self::Output {
        Dsl::<F>::from(self) * Dsl::<F>::constant_f(rhs)
    }
}

impl<F: BfField> Mul<Dsl<F>> for ValueVariable<F> {
    type Output = Dsl<F>;

    fn mul(self, rhs: Dsl<F>) -> Self::Output {
        Dsl::<F>::from(self) * rhs
    }
}

impl<F: BfField> Mul<ValueVariable<F>> for Dsl<F> {
    type Output = Self;

    fn mul(self, rhs: ValueVariable<F>) -> Self::Output {
        self * Self::from(rhs)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
// Assume the trace matrix height is k, the row 0~k uses to record Matrix open
// the u32::Max row use to record public inputs
// the u32::Max-1 row uses to record other inputs
pub struct Variable {
    pub row_index: usize,
    pub column_index: usize,
    pub expect_var_size: Option<u32>,
}

#[derive(Debug, Clone)]
pub struct VarWithValue {
    pub var: Variable,
    pub value: Vec<u32>,
}

impl VarWithValue {
    pub fn new(value: Vec<u32>, row_index: usize, column_index: usize) -> Self {
        VarWithValue {
            var: Variable::new(row_index, column_index),
            value: value,
        }
    }
}

impl<F: BfField> From<ValueVariable<F>> for VarWithValue {
    fn from(value: ValueVariable<F>) -> Self {
        Self::new(
            value.value.unwrap().as_u32_vec(),
            value.var.row_index,
            value.var.column_index,
        )
    }
}

impl<F: BfField> From<ValueVariable<F>> for Variable {
    fn from(value: ValueVariable<F>) -> Self {
        let var = Self::new_with_size(
            value.var.row_index,
            value.var.column_index,
            F::U32_SIZE as u32,
        );
        var
    }
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

impl<F: BfField> From<Variable> for Dsl<F> {
    fn from(var: Variable) -> Self {
        if let Some(size) = var.expect_var_size {
            assert_eq!(size, F::U32_SIZE as u32);
        }
        Self::new(Arc::new(RwLock::new(Box::new(InputOpcode::<0, 1>::new(
            get_opid(),
            var,
            vec![],
            F::U32_SIZE as u32,
            StandardOpcodeId::InputVarCopy,
        )))))
    }
}

impl<F: BfField> Add<F> for Variable {
    type Output = Dsl<F>;

    fn add(self, rhs: F) -> Self::Output {
        Dsl::<F>::from(self) + Dsl::<F>::constant_f(rhs)
    }
}

impl<F: BfField> Add<Dsl<F>> for Variable {
    type Output = Dsl<F>;

    fn add(self, rhs: Dsl<F>) -> Self::Output {
        Dsl::from(self) + rhs
    }
}

impl<F: BfField> Add<Variable> for Dsl<F> {
    type Output = Self;

    fn add(self, rhs: Variable) -> Self::Output {
        self + Self::from(rhs)
    }
}

impl<F: BfField> Sub<F> for Variable {
    type Output = Dsl<F>;

    fn sub(self, rhs: F) -> Self::Output {
        Dsl::<F>::from(self) - Dsl::<F>::constant_f(rhs)
    }
}

impl<F: BfField> Sub<Dsl<F>> for Variable {
    type Output = Dsl<F>;

    fn sub(self, rhs: Dsl<F>) -> Self::Output {
        Dsl::<F>::from(self) - rhs
    }
}

impl<F: BfField> Sub<Variable> for Dsl<F> {
    type Output = Self;

    fn sub(self, rhs: Variable) -> Self::Output {
        self - Self::from(rhs)
    }
}

impl<F: BfField> Mul<F> for Variable {
    type Output = Dsl<F>;

    fn mul(self, rhs: F) -> Self::Output {
        Dsl::<F>::from(self) * Dsl::<F>::constant_f(rhs)
    }
}

impl<F: BfField> Mul<Dsl<F>> for Variable {
    type Output = Dsl<F>;

    fn mul(self, rhs: Dsl<F>) -> Self::Output {
        Dsl::<F>::from(self) * rhs
    }
}

impl<F: BfField> Mul<Variable> for Dsl<F> {
    type Output = Self;

    fn mul(self, rhs: Variable) -> Self::Output {
        self * Self::from(rhs)
    }
}
