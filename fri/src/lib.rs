//! An implementation of the FRI low-degree test (LDT).

extern crate alloc;

mod config;
pub mod error;
mod fold_even_odd;
mod proof;
pub mod prover;
pub mod script_verifier;
pub mod two_adic_pcs;
pub mod verifier;

pub use config::*;
pub use fold_even_odd::*;
pub use proof::*;
pub use script_verifier::*;
pub mod fri_scripts;
