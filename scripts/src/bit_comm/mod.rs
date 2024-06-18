pub mod bit_comm;
pub mod bit_comm_u32;
pub mod secret_generator;
pub mod winternitz;

pub use common::{AsU32Vec, BabyBear, BinomialExtensionField};
use winternitz::*;

type Witness = Vec<Vec<u8>>;
