use std::collections::{BTreeMap, HashMap};

use alloc::vec;
use alloc::vec::Vec;

use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, PairBuilder};
use p3_field::{ExtensionField, Field};
use p3_matrix::{dense::RowMajorMatrix, Matrix};
use p3_util::log2_ceil_usize;
use tracing::instrument;

use crate::{symbolic_expression::SymbolicExpression, SVKey};
use crate::symbolic_variable::SymbolicVariable;
use crate::Entry;
use primitives::air::{AirConstraintBuilder,AirTraceBuilder};

#[instrument(name = "infer log of constraint degree", skip_all)]
pub fn get_log_quotient_degree<F, A>(
    air: &A,
    preprocessed_width: usize,
    num_public_values: usize,
) -> usize
where
    F: Field,
    A: Air<SymbolicAirBuilder<F>>,
{
    // We pad to at least degree 2, since a quotient argument doesn't make sense with smaller degrees.
    let constraint_degree =
        get_max_constraint_degree(air, preprocessed_width, num_public_values).max(2);

    // The quotient's actual degree is approximately (max_constraint_degree - 1) n,
    // where subtracting 1 comes from division by the zerofier.
    // But we pad it to a power of two so that we can efficiently decompose the quotient.
    log2_ceil_usize(constraint_degree - 1)
}

#[instrument(name = "infer constraint degree", skip_all, level = "debug")]
pub fn get_max_constraint_degree<F, A>(
    air: &A,
    preprocessed_width: usize,
    num_public_values: usize,
) -> usize
where
    F: Field,
    A: Air<SymbolicAirBuilder<F>>,
{
    get_symbolic_constraints(air, preprocessed_width, num_public_values)
        .iter()
        .map(|c| c.degree_multiple())
        .max()
        .unwrap_or(0)
}

#[instrument(name = "evaluate constraints symbolically", skip_all, level = "debug")]
pub fn get_symbolic_constraints<F, A>(
    air: &A,
    preprocessed_width: usize,
    num_public_values: usize,
) -> Vec<SymbolicExpression<F>>
where
    F: Field,
    A: Air<SymbolicAirBuilder<F>>,
{
    let mut builder = SymbolicAirBuilder::new(preprocessed_width, air.width(), num_public_values);
    air.eval(&mut builder);
    builder.constraints()
}

/// An `AirBuilder` for evaluating constraints symbolically, and recording them for later use.
#[derive(Debug,Clone)]
pub struct SymbolicAirBuilder<F: Field> {
    preprocessed: RowMajorMatrix<SymbolicVariable<F>>,
    main: RowMajorMatrix<SymbolicVariable<F>>,
    public_values: Vec<SymbolicVariable<F>>,
    constraints: Vec<SymbolicExpression<F>>,
}

pub fn gen_symbolic_builder<F: Field, A: Air<SymbolicAirBuilder<F>>>( air: &A, preprocessed_width: usize,num_public_values: usize) -> SymbolicAirBuilder<F>
{
    let mut builder = SymbolicAirBuilder::new(preprocessed_width, air.width(), num_public_values);
    air.eval(&mut builder);
    builder
}

impl<F: Field> SymbolicAirBuilder<F> {
    pub(crate) fn new(preprocessed_width: usize, width: usize, num_public_values: usize) -> Self {
        let prep_values = [0, 1]
            .into_iter()
            .flat_map(|offset| {
                (0..preprocessed_width)
                    .map(move |index| SymbolicVariable::new(Entry::Preprocessed { offset }, index))
            })
            .collect();
        let main_values = [0, 1]
            .into_iter()
            .flat_map(|offset| {
                (0..width).map(move |index| SymbolicVariable::new(Entry::Main { offset }, index))
            })
            .collect();
        let public_values = (0..num_public_values)
            .map(move |index| SymbolicVariable::new(Entry::Public, index))
            .collect();
        Self {
            preprocessed: RowMajorMatrix::new(prep_values, preprocessed_width),
            main: RowMajorMatrix::new(main_values, width),
            public_values,
            constraints: vec![],
        }
    }

    pub(crate) fn constraints(&self) -> Vec<SymbolicExpression<F>> {
        self.constraints.clone()
    }
}

impl<F: Field> AirBuilder for SymbolicAirBuilder<F> {
    type F = F;
    type Expr = SymbolicExpression<F>;
    type Var = SymbolicVariable<F>;
    type M = RowMajorMatrix<Self::Var>;

    fn main(&self) -> Self::M {
        self.main.clone()
    }

    fn is_first_row(&self) -> Self::Expr {
        SymbolicExpression::IsFirstRow
    }

    fn is_last_row(&self) -> Self::Expr {
        SymbolicExpression::IsLastRow
    }

    fn is_transition_window(&self, size: usize) -> Self::Expr {
        if size == 2 {
            SymbolicExpression::IsTransition
        } else {
            panic!("uni-stark only supports a window size of 2")
        }
    }

    fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) {
        self.constraints.push(x.into());
    }
}

impl<F: Field> AirBuilderWithPublicValues for SymbolicAirBuilder<F> {
    type PublicVar = SymbolicVariable<F>;
    fn public_values(&self) -> &[Self::PublicVar] {
        &self.public_values
    }
}

impl<F: Field> PairBuilder for SymbolicAirBuilder<F> {
    fn preprocessed(&self) -> Self::M {
        self.preprocessed.clone()
    }
}

impl <F: Field> AirConstraintBuilder for SymbolicAirBuilder<F> {
    fn main_width(&self) -> usize {
        self.main.width()
    }

    fn preprocessed_width(&self) -> usize {
        self.preprocessed.width()
    }

    fn constraints(&self) -> &[Self::Expr] {
        &self.constraints
    }

    fn get_max_constraint_degree(&self) -> usize {
        self.constraints.iter().map(|c|c.degree_multiple()).max().unwrap_or(0)
    }
}

pub struct SymbolicAirTraceBuilder<'a,F: Field,PublicF: Into<F>,Challenge: ExtensionField<F>,ACB: AirConstraintBuilder> {
    constraint_builder: &'a ACB,
    main_trace: Option<RowMajorMatrix<F>>,
    preprocess_trace: Option<RowMajorMatrix<F>>,
    public_trace: Option<Vec<PublicF>>,
    selectors: Option<Vec<F>>,
    alpha: Option<Challenge>,
}


impl <'a,F: Field, PublicF: Into<F> + Copy ,Challenge: ExtensionField<F>> AirTraceBuilder<'a> for SymbolicAirTraceBuilder<'a,F,PublicF,Challenge,SymbolicAirBuilder<F>> {
    type F = F;
    type PublicF = PublicF;
    type Challenge = Challenge;
    type MV = RowMajorMatrix<F>;
    type ACB = SymbolicAirBuilder<F>;

    fn new(cb: &'a SymbolicAirBuilder<F>) -> Self {
        Self{
            constraint_builder: cb,
            main_trace: None,
            preprocess_trace: None,
            public_trace: None,
            selectors: None, 
            alpha: None,
        }
    }

    fn constraint_builder(&self) -> &Self::ACB {
        &self.constraint_builder    
    }

    fn main_trace(&self) -> RowMajorMatrix<F> {
        self.main_trace.as_ref().unwrap().clone()
    }

    fn set_main_trace(&mut self, main_trace: RowMajorMatrix<F>) {
        self.main_trace = Some(main_trace);
    }

    fn preprocess_trace(&self) -> RowMajorMatrix<F> {
        self.main_trace.as_ref().unwrap().clone()
    }

    fn set_preprocess_trace(&mut self, main_trace: RowMajorMatrix<F>) {
        self.main_trace = Some(main_trace);
    }

    fn public_trace(&self) -> &[Self::PublicF] {
        self.public_trace.as_ref().unwrap()
    }

    fn set_public_trace(&mut self, public_trace:Vec<PublicF>) {
        self.public_trace = Some(public_trace);
    }

    fn set_selectors(&mut self, selectors: Vec<F>){
        self.selectors = Some(selectors);
    }

    fn selectors(&self) -> &[Self::F]{
        self.selectors.as_ref().unwrap()
    }

    fn apply_constraint(&self, alpha: Self::Challenge) -> Self::Challenge {
        let var_getter = self.generate_var_getter();
        let selectors = self.selectors();
        let constraints = self.constraint_builder.constraints().clone();
        constraints.iter().enumerate().fold(Challenge::zero(), |acc, data|acc + alpha.exp_u64(data.0 as u64) * data.1.execute(&var_getter,selectors) )
    }

}

impl<'a,F: Field, PublicF: Into<F> + Copy ,Challenge: ExtensionField<F>> SymbolicAirTraceBuilder<'a,F, PublicF, Challenge,SymbolicAirBuilder<F>> {
    fn generate_var_getter(&self) -> BTreeMap<SVKey,F>{
        // assert_eq!(self.main().values.len(),self.main_trace().values.);
        let mut var_getter = BTreeMap::new();
        self.constraint_builder.main().values.iter().zip(self.main_trace().values.iter()).for_each(| data | {
            var_getter.insert(data.0.clone().into(), data.1.clone());
        });

        self.constraint_builder.public_values().iter().zip(self.public_trace().iter()).for_each(| data | {
            var_getter.insert(data.0.clone().into(), (*data.1).into());
        });

        if self.preprocess_trace.is_some(){
            self.constraint_builder.preprocessed().values.iter().zip(self.preprocess_trace().values.iter()).for_each(| data | {
                var_getter.insert(data.0.clone().into(), data.1.clone());
            });
        }

        var_getter
    }

}