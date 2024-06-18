use std::usize;

use bitcoin::ScriptBuf as Script;
use bitcoin_script::{define_pushable, script};
use script_manager::bc_assignment::DefaultBCAssignment;
use scripts::bit_comm::bit_comm::BitCommitment;
use scripts::secret_generator::ConstantSecretGen;

use crate::field::BfField;
define_pushable!();

#[derive(Debug, Clone)]
pub struct PointsLeaf<F: BfField> {
    leaf_index: usize,
    points: Points<F>,
}

impl<F: BfField> PointsLeaf<F> {
    pub fn new(
        leaf_index: usize,
        xs: &[F],
        ys: &[F],
    ) -> PointsLeaf<F> {
        let points = Points::<F>::new(xs, ys);
        Self {
            leaf_index,
            points,
        }
    }

    pub fn recover_points_euqal_to_commited_point(&self) -> Script {
        let scripts = script! {
            {self.points.recover_points_euqal_to_commited_points()}
            OP_1
        };
        scripts
    }

    pub fn witness(&self) -> Vec<Vec<u8>> {
        self.points.signature()
    }

    pub fn get_point_by_index(&self, index: usize) -> Option<&Point<F>> {
        if self.points.points.len() > index {
            Some(&self.points.points[index])
        } else {
            None
        }
    }
    pub fn print_point_evals(&self) -> Result<(), ()>{
        if self.points.points.is_empty() {
            println!("No points to evaluate");
        }
        for i in self.points.points.iter() {
            println!("point_eval: {:?}", i.y);
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct Points<F: BfField> {
    pub points: Vec<Point<F>>,
}

impl<F: BfField> Points<F> {
    pub fn new(xs: &[F], ys: &[F]) -> Points<F> {
        let mut points = vec![];
        for (x,y) in xs.iter().zip(ys.iter()){
            //we should use refer here?
            points.push(Point::<F>::new(*x, *y));
        }
        Self {points}
    }

    pub fn recover_points_euqal_to_commited_points(&self) -> Script {
        // let scripts = script! {
        //     {self.p1.recover_point_euqal_to_commited_point()}
        //     {self.p2.recover_point_euqal_to_commited_point()}
        // };
        let scripts = script! {
            for p in self.points.iter() {
                { p.recover_point_euqal_to_commited_point() }
            }     
        };
        scripts
    }

    pub fn signature(&self) -> Vec<Vec<u8>> {
        let mut sigs = vec![];
        for p in self.points.iter().rev() {
            sigs.extend(p.signature());
        }
        sigs
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
    pub fn new_from_assign(x: F, y: F, bc_assign: &mut DefaultBCAssignment) -> Point<F> {
        let x_commit = bc_assign.assign(x);
        let y_commit = bc_assign.assign(y);
        Self {
            x,
            y,
            x_commit,
            y_commit,
        }
    }

    pub fn new(x: F, y: F) -> Point<F> {
        let x_commit = BitCommitment::<F>::new::<ConstantSecretGen>(x);
        let y_commit = BitCommitment::<F>::new::<ConstantSecretGen>(y);
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
            { self.x_commit.check_and_recover_to_altstack() }
            { self.y_commit.check_and_recover() }
        };

        scripts
    }

    pub fn recover_point_at_altstack(&self) -> Script {
        let scripts = script! {
            { self.x_commit.check_and_recover_to_altstack() }
            { self.y_commit.check_and_recover() }
        };

        scripts
    }

    pub fn recover_point_at_stack(&self) -> Script {
        let scripts = script! {
            { self.x_commit.check_and_recover_to_altstack() }
            { self.y_commit.check_and_recover() }
        };

        scripts
    }

    pub fn signature(&self) -> Vec<Vec<u8>> {
        let mut x_sigs = self.x_commit.witness();
        let mut y_sigs = self.y_commit.witness();
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
    use scripts::execute_script_with_inputs;

    use super::*;
    use crate::field::BfField;

    type F = BabyBear;
    type EF = p3_field::extension::BinomialExtensionField<BabyBear, 4>;

    #[test]
    fn test_point_babybear() {
        use p3_baby_bear::BabyBear;
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
        use p3_baby_bear::BabyBear;
        let p = Points::<BabyBear>::new(
            &vec![BabyBear::from_u32(1),BabyBear::from_u32(3)],
            &vec![BabyBear::from_u32(2), BabyBear::from_u32(4)]
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
        let e = rng.gen::<EF>();
        let f = rng.gen::<EF>();

        let xs = vec![a,c,e];
        let ys = vec![b,d,f];
        let p = Points::new(&xs, &ys);

        let script = script! {
            {p.recover_points_euqal_to_commited_points()}
            OP_1
        };
        let inputs = p.signature();
        let res = execute_script_with_inputs(script, inputs);
        assert!(res.success);
    }
}
