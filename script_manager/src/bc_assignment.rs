use std::collections::HashMap;

use scripts::bit_comm::bit_comm::BitCommitment;
use scripts::bit_comm::AsU32Vec;
use scripts::bit_comm_u32::BitCommitmentU32;
use scripts::secret_generator::SecretGen;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct BCAssignment<S: SecretGen> {
    // from u32 value -> u32 bitcommitment
    pub value_assigns: HashMap<u32, BitCommitmentU32>,
    // from index -> u32 bitcommitment
    pub varible_assigns: HashMap<String, Vec<BitCommitmentU32>>,
    pub indexer: u32,
    pub secret_gen: S,
}

impl<S: SecretGen> BCAssignment<S> {
    pub fn new() -> Self {
        Self {
            value_assigns: HashMap::new(),
            varible_assigns: HashMap::new(),
            indexer: 0,
            secret_gen: S::default(),
        }
    }

    pub fn assign<F: AsU32Vec>(&mut self, value: F) -> BitCommitment<F> {
        let x = BitCommitment::new::<S>(value);
        for i in x.clone().commitments {
            self.value_assigns.entry(i.value).or_insert_with(|| i);
        }
        x
    }

    // pre assign a commitment without value
    pub fn pre_assign_var<F: AsU32Vec>(&mut self) -> (BitCommitment<F>, String) {
        self.indexer += 1;
        let x = BitCommitment::new::<S>(F::default());
        self.varible_assigns
            .entry(self.indexer.to_string())
            .or_insert_with(|| x.commitments.clone());
        (x, self.indexer.to_string())
    }

    pub fn assign_var<F: AsU32Vec>(&mut self, name: &str, value: F) -> Option<BitCommitment<F>> {
        self.varible_assigns.remove(name).and_then(|commits| {
            let x: BitCommitment<F> = BitCommitment::new_with_commits(value, commits);
            for i in x.commitments.clone() {
                self.value_assigns.entry(i.value).or_insert_with(|| i);
            }
            Some(x)
        })
    }
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;
    use p3_baby_bear::BabyBear;
    use p3_field::{AbstractField, PackedValue};
    use primitives::field::BfField;
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaCha20Rng;
    use scripts::secret_generator::ThreadSecretGen;

    use super::*;
    type F = BabyBear;
    type EF = p3_field::extension::BinomialExtensionField<BabyBear, 4>;

    #[test]
    fn test_value_assign_bitcommits() {
        let mut bc_assign = BCAssignment::<ThreadSecretGen>::new();
        // let mut bc_temp: BitCommitmentU32 = BitCommitmentU32::new("1223", key);
        bc_assign.assign(10);
        bc_assign.assign(10);
        bc_assign.assign(10);
        bc_assign.assign(10);
        bc_assign.assign(10);

        assert_eq!(bc_assign.value_assigns.len(), 1);
        assert_eq!(bc_assign.value_assigns.get(&10).unwrap().value, 10);

        bc_assign.assign(12);
        bc_assign.assign(10);
        bc_assign.assign(14);
        bc_assign.assign(11);

        assert_eq!(bc_assign.value_assigns.len(), 4);
        assert_eq!(bc_assign.value_assigns.get(&10).unwrap().value, 10);
        assert_eq!(bc_assign.value_assigns.get(&11).unwrap().value, 11);
        assert_eq!(bc_assign.value_assigns.get(&12).unwrap().value, 12);
        assert_eq!(bc_assign.value_assigns.get(&14).unwrap().value, 14);

        bc_assign.assign(EF::default()); // 00, 00, 00, 00
        assert_eq!(bc_assign.value_assigns.len(), 5);
    }

    #[test]
    fn test_vars_assign_bitcommits() {
        let mut bc_assign = BCAssignment::<ThreadSecretGen>::new();
        let (old_bc, bc_id) = bc_assign.pre_assign_var::<F>();
        let new_bc = bc_assign
            .assign_var(&bc_id, F::from_canonical_u32(0x1234))
            .unwrap();
        assert_ne!(old_bc.value, new_bc.value);
        assert_eq!(old_bc.check_and_recover(), new_bc.check_and_recover());
    }
}
