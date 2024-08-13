use std::any::TypeId;

use common::BinomialExtensionField;
use p3_baby_bear::BabyBear;
use p3_challenger::{CanObserve, CanSample};
use p3_field::AbstractField;
use primitives::challenger::chan_field::U32;
use primitives::challenger::BitExtractor;
use primitives::field::BfField;
use scripts::blake3;

use crate::Dsl;

// BASE is the base field of F when F is a extension field
// And BASE is exactly same with F when F is a prime field
#[derive(Clone, Debug)]
pub struct BfChallengerExpr<F, const WIDTH: usize>
where
    F: BfField + BitExtractor,
{
    sponge_state: Vec<Dsl<F>>,
    input_buffer: Vec<Dsl<F>>,
    output_buffer: Vec<Dsl<F>>,

    pub grind_bits: Option<usize>,
    pub grind_output: F,
    pub sample_input: Vec<Vec<Dsl<F>>>,
    pub sample_output: Vec<Dsl<F>>,
}

impl<F, const WIDTH: usize> BfChallengerExpr<F, WIDTH>
where
    F: BfField + BitExtractor,
{
    pub fn new() -> Result<Self, String> {
        let mut u8_state = vec![];
        for _ in 0..32 {
            u8_state.push(Dsl::constant_u32(0));
        }
        u8_state.push(Dsl::sponge_state_init());
        Ok(Self {
            sponge_state: u8_state,
            input_buffer: vec![],
            output_buffer: vec![],

            grind_bits: None,
            grind_output: F::default(),
            sample_input: vec![],
            sample_output: vec![],
        })
    }

    pub fn record_sample(&mut self, input: &Vec<Dsl<F>>, output: &Dsl<F>) {
        self.sample_input.push(input.clone());
        self.sample_output.push(output.clone());
    }
}

impl<F, const WIDTH: usize> BfChallengerExpr<F, WIDTH>
where
    F: BfField + BitExtractor,
{
    fn duplexing(&mut self) {
        assert!(self.input_buffer.len() <= WIDTH / 2);

        for i in 0..self.input_buffer.len() {
            self.sponge_state[i] = self.input_buffer[i].clone();
        }
        self.input_buffer.clear();

        //reverse for permutation bytes order
        self.sponge_state.reverse();

        // Apply blake3 permutation.
        let blake3_res = Dsl::blake3(&self.sponge_state);

        self.sponge_state.clear();
        for _ in 0..32 {
            self.sponge_state.push(Dsl::constant_u32(0));
        }
        self.sponge_state.push(blake3_res.clone());

        self.output_buffer.push(blake3_res.to_sample());
    }
}

impl<F, const WIDTH: usize> CanObserve<U32> for BfChallengerExpr<F, WIDTH>
where
    F: BfField + BitExtractor,
{
    fn observe(&mut self, value: U32) {
        // Any buffered output is now invalid.
        self.output_buffer.clear();

        for elem in value {
            self.input_buffer.push(Dsl::constant_u32(elem as u32));
        }

        if self.input_buffer.len() == 32 {
            self.duplexing();
        }
    }
}

impl<F, const N: usize, const WIDTH: usize> CanObserve<[U32; N]> for BfChallengerExpr<F, WIDTH>
where
    F: BfField + BitExtractor,
{
    fn observe(&mut self, values: [U32; N]) {
        for value in values {
            self.observe(value);
        }
    }
}

// for TrivialPcs
impl<F, const WIDTH: usize> CanObserve<Vec<Vec<U32>>> for BfChallengerExpr<F, WIDTH>
where
    F: BfField + BitExtractor,
{
    fn observe(&mut self, valuess: Vec<Vec<U32>>) {
        for values in valuess {
            for value in values {
                self.observe(value);
            }
        }
    }
}

impl<F, const WIDTH: usize> CanSample<Dsl<F>> for BfChallengerExpr<F, WIDTH>
where
    F: BfField + BitExtractor,
{
    fn sample(&mut self) -> Dsl<F> {
        // if BASE is the same with F
        let mut sample_input = vec![];
        let res;
        if TypeId::of::<F>() == TypeId::of::<BabyBear>() {
            // If we have buffered inputs, we must perform a duplexing so that the challenge will
            // reflect them. Or if we've run out of outputs, we must perform a duplexing to get more.
            if !self.input_buffer.is_empty() || self.output_buffer.is_empty() {
                self.duplexing();
            }

            let value = self
                .output_buffer
                .pop()
                .expect("Output buffer should be non-empty");

            sample_input.push(value.clone());

            let output = value.sample_base();

            res = output;
        }
        // else, F would be a extension field of Babybear
        else if TypeId::of::<F>() == TypeId::of::<BinomialExtensionField<BabyBear, 4>>() {
            // If we have buffered inputs, we must perform a duplexing so that the challenge will
            // reflect them. Or if we've run out of outputs, we must perform a duplexing to get more.
            if !self.input_buffer.is_empty() || self.output_buffer.is_empty() {
                self.duplexing();
            }
            let value = self
                .output_buffer
                .pop()
                .expect("Output buffer should be non-empty");

            sample_input.push(value.clone());

            let output = value.sample_ext();

            res = output;
        } else {
            panic!("the type of base or f is invalid")
        } // no other implementation yet

        res
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use bitcoin_script_stack::stack::StackTracker;
    use common::BinomialExtensionField;
    use p3_baby_bear::BabyBear;
    use p3_challenger::{CanObserve, CanSample};
    use primitives::challenger::chan_field::U32;
    use primitives::challenger::{BfChallenger, Blake3Permutation};

    use crate::challenger_expr::BfChallengerExpr;

    #[test]
    fn test_challenger_expr() {
        {
            let mut stack = StackTracker::new();
            let mut var_getter = BTreeMap::new();
            let mut optimize = BTreeMap::new();

            let mut challenger = BfChallengerExpr::<BabyBear, 64>::new().unwrap();

            let value = [1 as u8; 4];
            challenger.observe(value.clone());

            let t = challenger.sample();

            // t.simulate_express(&mut optimize);
            // t.express_to_script(&mut stack, &mut var_getter, &mut optimize, true);

            challenger.observe(value.clone());

            let t1 = challenger.sample();

            t1.simulate_express(&mut optimize);
            t1.express_to_script(&mut stack, &mut var_getter, &mut optimize, true);

            stack.number(1103171332 as u32);
            stack.debug();
            stack.op_equal();

            stack.debug();
            let res = stack.run();
            assert!(res.success);
        }

        {
            let mut stack = StackTracker::new();
            let mut var_getter = BTreeMap::new();
            let mut optimize = BTreeMap::new();

            let mut challenger =
                BfChallengerExpr::<BinomialExtensionField<BabyBear, 4>, 64>::new().unwrap();

            let value = [1 as u8, 2 as u8, 3 as u8, 4 as u8];
            challenger.observe(value.clone());

            let _t = challenger.sample();

            challenger.observe(value.clone());

            let t1 = challenger.sample();

            //t1.express_to_script(&mut stack, &bmap);

            let permutation = Blake3Permutation {};
            let mut challenger = BfChallenger::<
                BinomialExtensionField<BabyBear, 4>,
                U32,
                Blake3Permutation,
                16,
            >::new(permutation)
            .unwrap();
            let value = [1 as u8, 2 as u8, 3 as u8, 4 as u8];

            challenger.observe(value.clone());
            let _t_value = challenger.sample();

            challenger.observe(value);
            let t1_value = challenger.sample();

            let equal = t1.equal_for_f(t1_value);

            equal.simulate_express(&mut optimize);
            equal.express_to_script(&mut stack, &mut var_getter, &mut optimize, true);

            stack.debug();

            let res = stack.run();
            assert!(res.success);
        }
    }
}
