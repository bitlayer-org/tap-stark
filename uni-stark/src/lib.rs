//! A minimal univariate STARK framework.

// #![no_std]

extern crate alloc;

mod config;
mod expr_helper;
mod folder;
mod proof;
mod prover;
mod script_verifier;
mod scripts;
mod symbolic_builder;
mod symbolic_expression;
mod symbolic_variable;
mod verifier;
mod zerofier_coset;

#[cfg(debug_assertions)]
mod check_constraints;

#[cfg(debug_assertions)]
pub use check_constraints::*;
pub use config::*;
pub use folder::*;
pub use proof::*;
pub use prover::*;
pub use script_verifier::*;
pub use scripts::*;
pub use symbolic_builder::*;
pub use symbolic_expression::*;
pub use symbolic_variable::*;
pub use verifier::*;
pub use zerofier_coset::*;
