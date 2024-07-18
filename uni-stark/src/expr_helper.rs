use std::cell::Cell;
use std::sync::Arc;

use bitcoin_script_stack::stack::StackVariable;
use p3_field::{AbstractField, Field};
use primitives::field::BfField;
use script_expr::{FieldScriptExpression, ValueVariable, Variable};

use crate::symbolic_variable::SymbolicVariable;
use crate::{Entry, SymbolicExpression};

impl<F: BfField> From<&SymbolicExpression<F>> for FieldScriptExpression<F> {
    fn from(value: &SymbolicExpression<F>) -> Self {
        match value {
            SymbolicExpression::Variable(v) => FieldScriptExpression::InputVariable {
                sv: v.into(),
                debug: Cell::new(false),
                var: StackVariable::null(),
            },
            SymbolicExpression::IsFirstRow => FieldScriptExpression::one(),
            SymbolicExpression::IsLastRow => FieldScriptExpression::one(),
            SymbolicExpression::IsTransition => FieldScriptExpression::one(),
            SymbolicExpression::Constant(f) => FieldScriptExpression::Constant {
                f: f.clone(),
                debug: Cell::new(false),
                var: StackVariable::null(),
            },
            SymbolicExpression::Add { x, y, .. } => FieldScriptExpression::Add {
                x: Arc::new(Box::new(FieldScriptExpression::from(&*x.clone()))),
                y: Arc::new(Box::new(FieldScriptExpression::from(&*y.clone()))),
                debug: Cell::new(false),
                var: StackVariable::null(),
            },
            SymbolicExpression::Sub { x, y, .. } => FieldScriptExpression::Sub {
                x: Arc::new(Box::new(FieldScriptExpression::from(&*x.clone()))),
                y: Arc::new(Box::new(FieldScriptExpression::from(&*y.clone()))),
                debug: Cell::new(false),
                var: StackVariable::null(),
            },
            SymbolicExpression::Neg { x, .. } => FieldScriptExpression::Neg {
                x: Arc::new(Box::new(FieldScriptExpression::from(&*x.clone()))),
                debug: Cell::new(false),
                var: StackVariable::null(),
            },
            SymbolicExpression::Mul { x, y, .. } => FieldScriptExpression::Mul {
                x: Arc::new(Box::new(FieldScriptExpression::from(&*x.clone()))),
                y: Arc::new(Box::new(FieldScriptExpression::from(&*y.clone()))),
                debug: Cell::new(false),
                var: StackVariable::null(),
            },
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

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;

    use common::{BabyBear, BinomialExtensionField};
    use p3_air::AirBuilder;
    use p3_matrix::Matrix;
    use script_expr::{FieldScriptExpression, *};
    type EF = BinomialExtensionField<BabyBear, 4>;

    use crate::SymbolicAirBuilder;
    #[test]
    fn test_symbolic_expr_constraints() {
        let air_width: usize = 2;
        let mut builder = SymbolicAirBuilder::<BabyBear>::new(0, air_width, 0);
        let main_values = builder.main();
        let (local, next) = (main_values.row_slice(0), main_values.row_slice(1));
        let mut when_transition = builder.when_transition();
        // a' <- b
        when_transition.assert_eq(local[0], local[1]);

        // b' <- a + b
        when_transition.assert_eq(local[0] + local[1], next[1]);

        let cs = builder.constraints();
        let script_exp: Vec<FieldScriptExpression<BabyBear>> = cs
            .iter()
            .map(|cons| FieldScriptExpression::from(cons))
            .collect();
    }
}