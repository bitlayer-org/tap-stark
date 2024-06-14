pub mod bit_comm;
pub mod bit_comm_u32;
pub mod secret_generator;
mod winternitz;

use primitives::field::{BabyBear, BfField, BinomialExtensionField};
use winternitz::*;

pub trait AsU32Vec: Clone + Default {
    fn bc_as_u32_vec(&self) -> Vec<u32>;
}
type Witness = Vec<Vec<u8>>;

impl AsU32Vec for u32 {
    fn bc_as_u32_vec(&self) -> Vec<u32> {
        vec![self.clone()]
    }
}

impl AsU32Vec for BinomialExtensionField<BabyBear, 4> {
    fn bc_as_u32_vec(&self) -> Vec<u32> {
        self.as_u32_vec()
    }
}

impl AsU32Vec for BabyBear {
    fn bc_as_u32_vec(&self) -> Vec<u32> {
        self.as_u32_vec()
    }
}
