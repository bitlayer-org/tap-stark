use p3_baby_bear::BabyBear;
use p3_field::extension::BinomialExtensionField;

use super::field::*;

pub trait AsU32Vec {
    fn bc_as_u32_vec(&self) -> Vec<u32>;
}

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
