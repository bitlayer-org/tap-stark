pub mod bit_comm;
pub mod bit_comm_u32;
pub mod secret_generator;
pub mod winternitz;

pub use primitives::common::AsU32Vec;
use primitives::field::{BabyBear, BfField, BinomialExtensionField};
use winternitz::*;

type Witness = Vec<Vec<u8>>;
