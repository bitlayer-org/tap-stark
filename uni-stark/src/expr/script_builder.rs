use alloc::collections::BTreeMap;
use alloc::format;
use alloc::vec::Vec;

use bitcoin_script_stack::stack::{StackTracker, StackVariable};
use p3_air::{AirBuilder, AirBuilderWithPublicValues};
use p3_matrix::dense::RowMajorMatrix;
use primitives::field::BfField;
use scripts::treepp::*;

use super::{FieldScriptExpression, ValueVariable, Variable};
use crate::SymbolicExpression::{self, *};

pub struct ScriptConstraintBuilder<F: BfField> {
    pub main: RowMajorMatrix<ValueVariable<F>>,
    pub public_values: Vec<Variable>,
    pub is_first_row: F,
    pub is_last_row: F,
    pub is_transition: F,
    pub constraints: Vec<FieldScriptExpression<F>>,
    pub alpha: F,
}

impl<F: BfField> ScriptConstraintBuilder<F> {
    pub fn new(
        local: Vec<F>,
        next: Vec<F>,
        num_public_values: usize,
        is_first_row: F,
        is_last_row: F,
        is_transition: F,
        alpha: F,
    ) -> Self {
        let width = local.len();
        let main_variables: Vec<ValueVariable<F>> = [local, next]
            .into_iter()
            .enumerate()
            .flat_map(|(row_index, row_values)| {
                (0..width).map(move |column_index| {
                    ValueVariable::new(
                        Variable::new(row_index, column_index),
                        row_values[column_index],
                    )
                })
            })
            .collect();

        let public_values = (0..num_public_values)
            //  set the row_index of Variable as u32::MAX to mark public_values
            .map(move |index| Variable::new(u32::MAX as usize, index))
            .collect();

        Self {
            main: RowMajorMatrix::new(main_variables, width),
            public_values: public_values,
            is_first_row: is_first_row,
            is_last_row: is_last_row,
            is_transition: is_transition,
            constraints: Vec::new(),
            alpha: alpha,
        }
    }

    pub fn get_accmulator_expr(&self) -> FieldScriptExpression<F> {
        let mut acc = self.constraints[0].clone();
        for i in 1..self.constraints.len() {
            acc = acc * self.alpha + self.constraints[i].clone();
        }
        acc
    }

    pub fn set_variable_values<Base: BfField>(
        &self,
        public_values: &Vec<Base>,
        bmap: &mut BTreeMap<Variable, StackVariable>,
        stack: &mut StackTracker,
    ) {
        assert_eq!(self.public_values().len(), public_values.len());
        for i in 0..self.public_values().len() {
            let u32_vec = F::from_canonical_u32(public_values[i].as_u32_vec()[0]).as_u32_vec();
            assert_eq!(u32_vec.len(), 4);
            bmap.insert(
                self.public_values()[i],
                stack.var(
                    F::U32_SIZE as u32,
                    script! { {u32_vec[3]} {u32_vec[2]}  {u32_vec[1]} {u32_vec[0]} },
                    &format!("public_var index={}", i),
                ),
            );
        }

        for i in 0..self.main().values.len() {
            let u32_vec = self.main().values[i].get_value().unwrap().as_u32_vec();
            bmap.insert(
                self.main().values[i].get_var().clone(),
                stack.var(
                    F::U32_SIZE as u32,
                    script! { {u32_vec[3]} {u32_vec[2]}  {u32_vec[1]} {u32_vec[0]} },
                    &format!(
                        "main_trace row index={} column_value={}",
                        i / self.main().width,
                        i % self.main().width
                    ),
                ),
            );
        }
    }

    pub fn drop_variable_values(
        &self,
        bmap: &mut BTreeMap<Variable, StackVariable>,
        stack: &mut StackTracker,
    ) {
        for i in (0..self.main().values.len()).rev() {
            stack.drop(*bmap.get(self.main().values[i].get_var()).unwrap());
        }

        for i in (0..self.public_values().len()).rev() {
            stack.drop(*bmap.get(&self.public_values()[i]).unwrap());
        }
    }
}

impl<F: BfField> AirBuilder for ScriptConstraintBuilder<F> {
    type F = F;
    type Expr = FieldScriptExpression<F>;
    type Var = ValueVariable<F>;
    type M = RowMajorMatrix<Self::Var>;

    fn main(&self) -> Self::M {
        self.main.clone()
    }

    fn is_first_row(&self) -> Self::Expr {
        Self::Expr::from(self.is_first_row)
    }

    fn is_last_row(&self) -> Self::Expr {
        Self::Expr::from(self.is_last_row)
    }

    fn is_transition_window(&self, size: usize) -> Self::Expr {
        if size == 2 {
            Self::Expr::from(self.is_transition)
        } else {
            panic!("uni-stark only supports a window size of 2")
        }
    }

    fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) {
        let x = x.into();
        self.constraints.push(x);
    }
}

impl<F: BfField> AirBuilderWithPublicValues for ScriptConstraintBuilder<F> {
    type PublicVar = Variable;

    fn public_values(&self) -> &[Self::PublicVar] {
        &self.public_values
    }
}
