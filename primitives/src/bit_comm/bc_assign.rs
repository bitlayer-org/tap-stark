use std::collections::HashMap;

use itertools::Itertools;
use scripts::bit_comm_u32::BitCommitmentU32;

use super::BitCommitment;
use crate::field::BfField;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct BCAssignment {
    pub bcs: HashMap<u32, BitCommitmentU32>,
    secret_assign: SecretAssignment,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SecretAssignment;

impl SecretAssignment {
    pub fn new() -> Self {
        SecretAssignment
    }
    fn get_secret(&self) -> &str {
        // temporary secret
        "0000"
    }
}

impl BCAssignment {
    pub fn new() -> Self {
        Self {
            bcs: HashMap::new(),
            // ebcs: HashMap::new(),
            secret_assign: SecretAssignment::new(),
        }
    }

    fn get_secret(&self) -> &str {
        self.secret_assign.get_secret()
    }

    pub fn force_insert(&mut self, value: u32) -> BitCommitmentU32 {
        let bc = BitCommitmentU32::new(self.get_secret(), value);
        self.bcs.insert(value, bc);
        self.get(value).unwrap()
    }

    pub fn get(&self, value: u32) -> Option<BitCommitmentU32> {
        self.bcs.get(&value).map(|bc| bc.clone())
    }

    pub fn assign(&mut self, value: u32) -> BitCommitmentU32 {
        let secret = self.secret_assign.get_secret();
        self.bcs
            .entry(value)
            .or_insert_with(|| BitCommitmentU32::new(secret, value))
            .clone()
    }

    pub fn assign_field<F: BfField>(&mut self, value: F) -> BitCommitment<F> {
        let commitments = value
            .as_u32_vec()
            .iter()
            .map(|u32_value| self.assign(*u32_value))
            .collect_vec();
        BitCommitment { value, commitments }
    }
}

#[cfg(test)]
mod tests {
    use p3_baby_bear::BabyBear;
    use p3_field::AbstractField;
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaCha20Rng;

    use super::*;
    type F = BabyBear;
    type EF = p3_field::extension::BinomialExtensionField<BabyBear, 4>;

    #[test]
    fn test_assign_bitcommits() {
        use super::*;
        let key = 123;
        let bc_assign: &mut BCAssignment = &mut BCAssignment::new();
        let mut bc_temp: BitCommitmentU32 = BitCommitmentU32::new("1223", key);
        {
            bc_assign.force_insert(key);
            let bc: BitCommitmentU32 = bc_assign.get(key).unwrap();
            assert_eq!(bc.value, key);
            bc_temp = bc.clone();
        }

        {
            let bc1: BitCommitmentU32 = bc_assign.assign(key);
            assert_eq!(bc1, bc_temp);
        }
    }
}
