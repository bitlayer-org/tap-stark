use p3_baby_bear::BabyBear;
use p3_field::extension::BinomialExtensionField;
use p3_field::{AbstractExtensionField, AbstractField, PrimeField32, TwoAdicField};

pub trait BfField: AbstractField + TwoAdicField + Clone + Copy {
    const BIS_SIZE: usize;
    const MOD: u32;
    const U32_SIZE: usize;

    fn from_u32(data: u32) -> Self {
        Self::from_canonical_u32(data)
    }
    fn group_genreator(group_bit_size: usize) -> Self {
        Self::two_adic_generator(group_bit_size)
    }

    fn sub_group(group_bit_size: usize) -> Vec<Self> {
        let generator = Self::group_genreator(group_bit_size);
        let group_size = 1 << group_bit_size;
        // let mut subgroups = Vec::with_capacity(2^group_bit_size);
        let mut subgroups = Vec::new();
        let mut acc = generator;
        subgroups.push(Self::one());
        for _ in 0..group_size - 1 {
            subgroups.push(acc);
            acc = acc * generator;
        }
        subgroups
    }

    fn field_mod() -> Self {
        Self::from_wrapped_u32(Self::MOD)
    }

    fn as_u32_vec(&self) -> Vec<u32>;
}

pub trait FieldAsSlice: BfField {
    fn as_slice(&self) -> &[u32];
}

impl BfField for BabyBear {
    const BIS_SIZE: usize = 32;
    const MOD: u32 = 0x78000001;
    const U32_SIZE: usize = 1;

    fn as_u32_vec(&self) -> Vec<u32> {
        vec![self.as_canonical_u32()]
    }
}

impl BfField for BinomialExtensionField<BabyBear, 4> {
    const BIS_SIZE: usize = 32;
    const MOD: u32 = 0x78000001;
    const U32_SIZE: usize = 4;

    fn as_u32_vec(&self) -> Vec<u32> {
        self.as_base_slice()
            .iter()
            .map(|babybear: &BabyBear| babybear.as_canonical_u32())
            .collect()
    }
}

mod tests {
    use p3_baby_bear::BabyBear;
    use p3_field::{AbstractField, PrimeField32};

    use super::BfField;

    #[test]
    fn test_subgroup() {
        let generator = BabyBear::group_genreator(2);
        assert_eq!(
            generator * generator * generator * generator,
            BabyBear::one()
        );

        let subgroups = BabyBear::sub_group(2);
        let subgroups_size: usize = 1 << 2;
        assert_eq!(subgroups.len(), subgroups_size);
        subgroups
            .iter()
            .for_each(|v| println!("{:}", v.as_canonical_u32()));

        assert_eq!(BabyBear::field_mod() - subgroups[0], subgroups[2]);
    }
}
