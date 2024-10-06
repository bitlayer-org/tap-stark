use p3_air::{Air,AirBuilder,AirBuilderWithPublicValues};
use p3_field::{ExtensionField, Field};
use p3_matrix::Matrix;


pub trait AirConstraintBuilder:AirBuilderWithPublicValues{
    fn constraints(&self) -> &[Self::Expr];

    fn get_max_constraint_degree(&self) -> usize;
}

pub trait AirTraceBuilder<'a>{
    type F: Field;
    type Challenge: ExtensionField<Self::F>;
    type MV: Matrix<Self::F>;
    type ACB: AirConstraintBuilder;

    fn new(cb: &'a Self::ACB) -> Self; 

    fn constraint_builder(&self) -> &Self::ACB; 

    fn main_trace(&self) -> Self::MV;

    fn public_trace(&self) -> &[Self::F];

    fn selectors(&self) -> &[Self::F];

    fn set_selectors(&mut self, selectors: Vec<Self::F>);

    fn set_main_trace(&mut self, main_trace: Self::MV);

    fn set_public_trace(&mut self, public_trace:Vec<Self::F>);

    fn apply_constraint(&self, alpha: Self::Challenge) -> Self::Challenge;
}
