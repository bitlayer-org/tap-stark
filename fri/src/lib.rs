//! An implementation of the FRI low-degree test (LDT).

#![cfg_attr(not(test), no_std)]

extern crate alloc;

mod config;
mod fold_even_odd;
pub mod mmcs;
mod proof;
pub mod prover;
// mod two_adic_pcs;
pub mod error;
pub mod fri_script;
pub mod script_verifier;
pub mod verifier;
pub use config::*;
pub use fold_even_odd::*;
pub use mmcs::*;
pub use proof::*;
pub use script_verifier::*;
// pub use two_adic_pcs::*;
