use alloc::vec::Vec;
use core::fmt::Debug;

use p3_field::Field;
use p3_matrix::Matrix;
use primitives::field::BfField;
use script_expr::Dsl;

#[derive(Debug)]
pub struct FriConfig<M> {
    pub log_blowup: usize,
    pub num_queries: usize,
    pub proof_of_work_bits: usize,
    pub mmcs: M,
}

impl<M> FriConfig<M> {
    pub fn blowup(&self) -> usize {
        1 << self.log_blowup
    }
}

/// Whereas `FriConfig` encompasses parameters the end user can set, `FriGenericConfig` is
/// set by the PCS calling FRI, and abstracts over implementation details of the PCS.
pub trait FriGenericConfig<F: Field> {
    type InputProof;
    type InputError: Debug;

    /// We can ask FRI to sample extra query bits (LSB) for our own purposes.
    /// They will be passed to our callbacks, but ignored (shifted off) by FRI.
    fn extra_query_index_bits(&self) -> usize;

    /// Fold a row, returning a single column.
    /// Right now the input row will always be 2 columns wide,
    /// but we may support higher folding arity in the future.
    fn fold_row(
        &self,
        index: usize,
        log_height: usize,
        beta: F,
        evals: impl Iterator<Item = F>,
    ) -> F;

    /// Same as applying fold_row to every row, possibly faster.
    fn fold_matrix<M: Matrix<F>>(&self, beta: F, m: M) -> Vec<F>;
}

pub trait FriGenericConfigWithExpr<F: BfField>: FriGenericConfig<F> {
    fn fold_row_with_expr(
        &self,
        folded_eval: Dsl<F>,
        sibling_eval: Dsl<F>,
        x: Dsl<F>, // x = x^2  ; neg_x = x * val::two_adic_generator(1);  // xs[index%2] = x, xs[index%2+1] = neg_x
        x_hint: F,
        point_index: usize,
        index_sibling: usize,
        beta: Dsl<F>,
    ) -> (Dsl<F>, Dsl<F>);
}
