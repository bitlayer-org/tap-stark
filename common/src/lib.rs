pub use p3_baby_bear::BabyBear;
pub use p3_field::extension::BinomialExtensionField;
pub use p3_field::{AbstractExtensionField, AbstractField, PrimeField32, TwoAdicField};

pub trait AsU32Vec {
    fn bc_as_u32_vec(&self) -> Vec<u32>;
    // fn u32_clone(&self) -> Self;
}

impl AsU32Vec for u32 {
    fn bc_as_u32_vec(&self) -> Vec<u32> {
        vec![self.clone()]
    }
}

impl AsU32Vec for BinomialExtensionField<BabyBear, 4> {
    fn bc_as_u32_vec(&self) -> Vec<u32> {
        self.as_base_slice()
            .iter()
            .map(|babybear: &BabyBear| babybear.as_canonical_u32())
            .collect()
    }
}

impl AsU32Vec for BabyBear {
    fn bc_as_u32_vec(&self) -> Vec<u32> {
        vec![self.as_canonical_u32()]
    }
}
