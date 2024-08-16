use alloc::collections::BTreeMap;
use alloc::format;
use alloc::vec::Vec;

use bitcoin_script_stack::stack::{StackTracker, StackVariable};
use p3_air::{AirBuilder, AirBuilderWithPublicValues};
use p3_matrix::dense::RowMajorMatrix;
use primitives::field::BfField;
use scripts::treepp::*;

use super::{Dsl, ValueVariable, Variable};
use crate::ValueCounter;

pub struct ScriptConstraintBuilder<F: BfField> {
    pub main: RowMajorMatrix<ValueVariable<F>>,
    pub public_values: Vec<Variable>,
    pub is_first_row: Dsl<F>,
    pub is_last_row: Dsl<F>,
    pub is_transition: Dsl<F>,
    pub constraints: Vec<Dsl<F>>,
    pub alpha: Dsl<F>,
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
        Self::new_with_expr(
            local,
            next,
            num_public_values,
            Dsl::constant_f(is_first_row),
            Dsl::constant_f(is_last_row),
            Dsl::constant_f(is_transition),
            Dsl::constant_f(alpha),
        )
    }

    pub fn new_with_expr(
        local: Vec<F>,
        next: Vec<F>,
        num_public_values: usize,
        is_first_row: Dsl<F>,
        is_last_row: Dsl<F>,
        is_transition: Dsl<F>,
        alpha: Dsl<F>,
    ) -> Self {
        let width = local.len();
        let main_variables: Vec<ValueVariable<F>> = [local, next]
            .into_iter()
            .enumerate()
            .flat_map(|(row_index, row_values)| {
                (0..width).map(move |column_index| {
                    ValueVariable::new(
                        Variable::new_with_size(row_index, column_index, F::U32_SIZE as u32),
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

    pub fn get_accmulator_expr(&self) -> Dsl<F> {
        let mut acc = self.constraints[0].clone();
        for i in 1..self.constraints.len() {
            acc = acc * self.alpha.clone() + self.constraints[i].clone();
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
                        "main_trace row_index={} column_index={}",
                        i / self.main().width,
                        i % self.main().width
                    ),
                ),
            );
        }
    }

    pub fn set_value_count(&self, vc: &mut ValueCounter) {
        // for i in 0..self.public_values().len() {
        //     let value = self.var
        //     vc.get_or_set(self.public_values()[i].as_u32());
        // }

        for i in 0..self.main().values.len() {
            let fvalue = self.main.values[i].get_value().unwrap().as_u32_vec();
            for j in 0..fvalue.len() {
                vc.get_or_set(fvalue[j]);
            }
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
    type Expr = Dsl<F>;
    type Var = ValueVariable<F>;
    type M = RowMajorMatrix<Self::Var>;

    fn main(&self) -> Self::M {
        self.main.clone()
    }

    fn is_first_row(&self) -> Self::Expr {
        self.is_first_row.clone()
    }

    fn is_last_row(&self) -> Self::Expr {
        self.is_last_row.clone()
    }

    fn is_transition_window(&self, size: usize) -> Self::Expr {
        if size == 2 {
            self.is_transition.clone()
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
