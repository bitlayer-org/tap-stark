use std::usize;

use bitcoin::ScriptBuf as Script;
use bitcoin_script::{define_pushable, script};
use primitives::field::BfField;
use scripts::bit_comm::*;
define_pushable!();

#[derive(Debug, Clone)]
pub struct PointsLeaf<F: BfField> {
    leaf_index_1: usize,
    leaf_index_2: usize,
    points: Points<F>,
}

impl<F: BfField> PointsLeaf<F> {
    pub fn new(
        leaf_index_1: usize,
        leaf_index_2: usize,
        x: F,
        y: F,
        x2: F,
        y2: F,
    ) -> PointsLeaf<F> {
        let points = Points::<F>::new(x, y, x2, y2);
        Self {
            leaf_index_1,
            leaf_index_2,
            points,
        }
    }

    pub fn recover_points_euqal_to_commited_point(&self) -> Script {
        let scripts = script! {
            {self.points.p1.recover_point_euqal_to_commited_point()}
            {self.points.p2.recover_point_euqal_to_commited_point()}
            OP_1
        };
        scripts
    }

    pub fn signature(&self) -> Vec<Vec<u8>> {
        let mut p1_sigs = self.points.p1.signature();
        let mut p2_sigs = self.points.p2.signature();
        p2_sigs.append(p1_sigs.as_mut());
        p2_sigs
    }

    pub fn get_point_by_index(&self, index: usize) -> Option<&Point<F>> {
        if index == self.leaf_index_1 {
            Some(&self.points.p1)
        } else if self.leaf_index_2 == index {
            Some(&self.points.p2)
        } else {
            None
        }
    }
}

#[derive(Debug, Clone)]
pub struct Points<F: BfField> {
    p1: Point<F>,
    p2: Point<F>,
}

impl<F: BfField> Points<F> {
    pub fn new(x1: F, y1: F, x2: F, y2: F) -> Points<F> {
        let p1 = Point::<F>::new(x1, y1);
        let p2 = Point::<F>::new(x2, y2);
        Self { p1, p2 }
    }

    pub fn recover_points_euqal_to_commited_points(&self) -> Script {
        let scripts = script! {
            {self.p1.recover_point_euqal_to_commited_point()}
            {self.p2.recover_point_euqal_to_commited_point()}
        };
        scripts
    }

    pub fn signature(&self) -> Vec<Vec<u8>> {
        let mut p1_sigs = self.p1.signature();
        let mut p2_sigs = self.p2.signature();
        p2_sigs.append(p1_sigs.as_mut());
        p2_sigs
    }
}

#[derive(Debug, Clone)]
pub struct Point<F: BfField> {
    pub x: F,
    pub y: F,
    pub x_commit: BitCommitment<F>,
    pub y_commit: BitCommitment<F>,
}

impl<F: BfField> Point<F> {
    pub fn new_from_assign(x: F, y: F, bc_assign: &mut BCAssignment) -> Point<F> {
        let x_commit = bc_assign.assign_field(x);
        let y_commit = bc_assign.assign_field(y);
        Self {
            x,
            y,
            x_commit,
            y_commit,
        }
    }

    pub fn new(x: F, y: F) -> Point<F> {
        let x_commit = BitCommitment::<F>::new("b138982ce17ac813d505b5b40b665d404e9528e8", x);
        let y_commit = BitCommitment::<F>::new("b138982ce17ac813d505b5b40b665d404e9528e8", y);
        Self {
            x: x,
            y: y,
            x_commit: x_commit,
            y_commit: y_commit,
        }
    }

    pub fn recover_point_euqal_to_commited_point(&self) -> Script {
        let scripts = script! {
            { self.x_commit.recover_message_euqal_to_commit_message() }
            { self.y_commit.recover_message_euqal_to_commit_message() }
        };

        scripts
    }

    pub fn recover_point_x_at_altstack_y_at_stack(&self) -> Script {
        let scripts = script! {
            { self.x_commit.recover_message_at_altstack() }
            { self.y_commit.recover_message_at_stack() }
        };

        scripts
    }

    pub fn recover_point_at_altstack(&self) -> Script {
        let scripts = script! {
            { self.x_commit.recover_message_at_altstack() }
            { self.y_commit.recover_message_at_altstack() }
        };

        scripts
    }

    pub fn recover_point_at_stack(&self) -> Script {
        let scripts = script! {
            { self.x_commit.recover_message_at_stack() }
            { self.y_commit.recover_message_at_stack() }
        };

        scripts
    }

    pub fn signature(&self) -> Vec<Vec<u8>> {
        let mut x_sigs = self.x_commit.signature();
        let mut y_sigs = self.y_commit.signature();
        y_sigs.append(x_sigs.as_mut());
        y_sigs
    }
}

#[cfg(test)]
mod test {
    use p3_baby_bear::BabyBear;
    use p3_field::{AbstractExtensionField, AbstractField, PrimeField32};
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaCha20Rng;

    use super::*;
    use crate::execute_script_with_inputs;
    use crate::fri::field::BfField;

    type F = BabyBear;
    type EF = p3_field::extension::BinomialExtensionField<BabyBear, 4>;

    #[test]
    fn test_point_babybear() {
        use crate::BabyBear;
        let p = Point::<BabyBear>::new(BabyBear::from_u32(1), BabyBear::from_u32(2));

        let script = script! {
            {p.recover_point_euqal_to_commited_point()}
            OP_1
        };
        let inputs = p.signature();
        let res = execute_script_with_inputs(script, inputs);
        assert!(res.success);
    }

    #[test]
    fn test_point_Babybear4() {
        use super::*;
        let mut rng = ChaCha20Rng::seed_from_u64(0u64);
        let a = rng.gen::<EF>();
        let b = rng.gen::<EF>();

        let p = Point::new(a, b);

        let script = script! {
            {p.recover_point_euqal_to_commited_point()}
            OP_1
        };
        let inputs = p.signature();
        let res = execute_script_with_inputs(script, inputs);
        assert!(res.success);
    }

    #[test]
    fn test_points_Babybear() {
        use crate::BabyBear;
        let p = Points::<BabyBear>::new(
            BabyBear::from_u32(1),
            BabyBear::from_u32(2),
            BabyBear::from_u32(3),
            BabyBear::from_u32(4),
        );

        let script = script! {
            {p.recover_points_euqal_to_commited_points()}
            OP_1
        };
        let inputs = p.signature();
        let res = execute_script_with_inputs(script, inputs);
        assert!(res.success);
    }

    #[test]
    fn test_extension_points_Babybear4() {
        use super::*;
        let mut rng = ChaCha20Rng::seed_from_u64(0u64);
        let a = rng.gen::<EF>();
        let b = rng.gen::<EF>();
        let c = rng.gen::<EF>();
        let d = rng.gen::<EF>();

        let p = Points::new(a, b, c, d);

        let script = script! {
            {p.recover_points_euqal_to_commited_points()}
            OP_1
        };
        let inputs = p.signature();
        let res = execute_script_with_inputs(script, inputs);
        assert!(res.success);
    }
}
