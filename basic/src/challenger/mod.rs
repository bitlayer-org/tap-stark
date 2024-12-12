use std::any::{Any, TypeId};

use chan_field::{ChallengeField, PermutationField, U32};
use p3_baby_bear::BabyBear;
use p3_challenger::{CanObserve, CanSample, CanSampleBits};
use p3_field::extension::BinomialExtensionField;
use p3_field::{AbstractExtensionField, AbstractField, Field, PrimeField32};
use p3_maybe_rayon::prelude::*;
use p3_symmetric::{CryptographicPermutation, Hash, Permutation};
use tracing;
use tracing::instrument;

pub mod chan_field;
/// A challenger that operates natively on PF but produces challenges of F: Field + BitExtractor,.

// BF_Fri uses Blake3 as Permutation Function
// The type of the taptree root is [u8;32], which is the input of the permutation function,
// and we expect to sample the babybear or babybear-extension point to challenge
// The input buffer is Vec<PF>
// The output buffer is Vec<PF> and we can mod F::P to get Vec<F>

#[derive(Clone)]
pub struct Blake3Permutation {}

// For bf challenger, U32 is the PF and 16 is the WIDTH.
type StateLength = [U32; 16];

impl Permutation<StateLength> for Blake3Permutation {
    fn permute(&self, mut input: StateLength) -> StateLength {
        self.permute_mut(&mut input);
        input
    }

    fn permute_mut(&self, input: &mut StateLength) {
        let mut hasher = blake3::Hasher::new();
        for chunk in *input {
            hasher.update(&chunk);
        }
        let hashed: [u8; 32] = hasher.finalize().into();

        for idx in 0..16 {
            if idx < 8 {
                input[idx] = U32::from_u64(0);
            } else {
                input[idx] = U32::from_u8_array(&hashed[(idx - 8) * 4..(idx - 8) * 4 + 4]);
            }
        }
    }
}

impl CryptographicPermutation<StateLength> for Blake3Permutation {}

pub trait BfGrindingChallenger:
    CanObserve<Self::Witness> + CanSampleBits<usize> + Sync + Clone
{
    type Witness: PermutationField<4>;

    fn grind(&mut self, bits: usize) -> Self::Witness;

    #[must_use]
    fn check_witness(&mut self, bits: usize, witness: Self::Witness) -> bool;
}

// BASE is the base field of F when F is a extension field
// And BASE is exactly same with F when F is a prime field
#[derive(Clone, Debug)]
pub struct BfChallenger<F, PF, P, const WIDTH: usize>
where
    F: Field + BitExtractor,
    PF: PermutationField<4>,
    P: CryptographicPermutation<[PF; WIDTH]>,
{
    sponge_state: [PF; WIDTH],
    input_buffer: Vec<PF>,
    output_buffer: Vec<PF>,
    permutation: P,

    pub permutation_input_records: Vec<Vec<PF>>,
    pub permutation_output_records: Vec<Vec<PF>>,
    pub grind_bits: Option<usize>,
    pub grind_output: F,
    pub sample_input: Vec<Vec<PF>>,
    pub sample_output: Vec<F>,
}

impl<F, PF, P, const WIDTH: usize> BfGrindingChallenger for BfChallenger<F, PF, P, WIDTH>
where
    F: Field + BitExtractor,
    PF: PermutationField<4>,
    P: CryptographicPermutation<[PF; WIDTH]>,
{
    type Witness = PF;

    #[instrument(name = "grind for proof-of-work witness", skip_all)]
    fn grind(&mut self, bits: usize) -> Self::Witness {
        let witness = (0..PF::mod_p())
            .into_par_iter()
            .map(|i| PF::from_u64(i as u64))
            .find_any(|witness| self.clone().check_witness(bits, *witness))
            .expect("failed to find witness");
        assert!(self.check_witness(bits, witness));
        self.grind_bits = Some(bits);
        self.grind_output = *self.sample_output.last().unwrap();
        witness
    }

    #[must_use]
    fn check_witness(&mut self, bits: usize, witness: Self::Witness) -> bool {
        self.observe(witness);
        for _ in 0..7 {
            self.observe(PF::from_u64(0));
        }
        self.sample_bits(bits) == 0
    }
}

impl<F, PF, P, const WIDTH: usize> BfChallenger<F, PF, P, WIDTH>
where
    F: Field + BitExtractor,
    PF: PermutationField<4>,
    P: CryptographicPermutation<[PF; WIDTH]>,
{
    pub fn new(permutation: P) -> Result<Self, String> {
        Ok(Self {
            sponge_state: [PF::default(); WIDTH],
            input_buffer: vec![],
            output_buffer: vec![],
            permutation,

            permutation_input_records: vec![],
            permutation_output_records: vec![],
            grind_bits: None,
            grind_output: F::default(),
            sample_input: vec![],
            sample_output: vec![],
        })
    }

    pub fn record_sample(&mut self, input: &Vec<PF>, output: &F) {
        self.sample_input.push(input.clone());
        self.sample_output.push(*output);
    }
}

impl<F, PF, P, const WIDTH: usize> BfChallenger<F, PF, P, WIDTH>
where
    F: Field + BitExtractor,
    PF: PermutationField<4>,
    P: CryptographicPermutation<[PF; WIDTH]>,
{
    fn duplexing(&mut self) {
        assert!(self.input_buffer.len() <= WIDTH);

        for i in 0..self.input_buffer.len() {
            self.sponge_state[i] = self.input_buffer[i];
        }
        self.input_buffer.clear();

        // Record this permutation to build fiat shamir subtree for future
        self.permutation_input_records
            .push(self.sponge_state.into());

        // Apply the permutation.
        self.permutation.permute_mut(&mut self.sponge_state);

        self.permutation_output_records
            .push(self.sponge_state[WIDTH / 2..WIDTH].into());

        self.output_buffer.clear();
        for i in WIDTH / 2..WIDTH {
            self.output_buffer.push(self.sponge_state[i]);
        }
        tracing::debug! {"state change: {:?}", u32::from_le_bytes(self.sponge_state[8].as_u8_array())};
    }
}

impl<F, PF, P, const WIDTH: usize> CanObserve<PF> for BfChallenger<F, PF, P, WIDTH>
where
    F: Field + BitExtractor,
    PF: PermutationField<4>,
    P: CryptographicPermutation<[PF; WIDTH]>,
{
    fn observe(&mut self, value: PF) {
        tracing::debug! {"observe: {:?}", u32::from_le_bytes(value.as_u8_array())};

        // Any buffered output is now invalid.
        self.output_buffer.clear();

        self.input_buffer.push(value);

        if self.input_buffer.len() == WIDTH / 2 {
            self.duplexing();
        }
    }
}

impl<F, PF, const N: usize, P, const WIDTH: usize> CanObserve<[PF; N]>
    for BfChallenger<F, PF, P, WIDTH>
where
    F: Field + BitExtractor,
    PF: PermutationField<4>,
    P: CryptographicPermutation<[PF; WIDTH]>,
{
    fn observe(&mut self, values: [PF; N]) {
        for value in values {
            self.observe(value);
        }
    }
}

impl<F, PF, const N: usize, P, const WIDTH: usize> CanObserve<Vec<[PF; N]>>
    for BfChallenger<F, PF, P, WIDTH>
where
    F: Field + BitExtractor,
    PF: PermutationField<4>,
    P: CryptographicPermutation<[PF; WIDTH]>,
{
    fn observe(&mut self, values: Vec<[PF; N]>) {
        for value in values {
            self.observe(value);
        }
    }
}

impl<F, PF, const N: usize, P, const WIDTH: usize> CanObserve<Hash<PF, PF, N>>
    for BfChallenger<F, PF, P, WIDTH>
where
    F: Field + BitExtractor,
    PF: PermutationField<4>,
    P: CryptographicPermutation<[PF; WIDTH]>,
{
    fn observe(&mut self, values: Hash<PF, PF, N>) {
        for pf_val in values {
            self.observe(pf_val);
        }
    }
}

// for TrivialPcs
impl<F, PF, P, const WIDTH: usize> CanObserve<Vec<Vec<PF>>> for BfChallenger<F, PF, P, WIDTH>
where
    F: Field + BitExtractor,
    PF: PermutationField<4>,
    P: CryptographicPermutation<[PF; WIDTH]>,
{
    fn observe(&mut self, valuess: Vec<Vec<PF>>) {
        for values in valuess {
            for value in values {
                self.observe(value);
            }
        }
    }
}

impl<F, PF, P, const WIDTH: usize> CanSample<F> for BfChallenger<F, PF, P, WIDTH>
where
    F: Field + BitExtractor,
    PF: PermutationField<4>,
    P: CryptographicPermutation<[PF; WIDTH]>,
{
    fn sample(&mut self) -> F {
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
            // commit records
            let output = BabyBear::from_pf(&value);
            sample_input.push(value);
            res = *(&output as &dyn Any).downcast_ref::<F>().unwrap();
        }
        // else, F would be a extension field of Babybear
        else if TypeId::of::<F>() == TypeId::of::<BinomialExtensionField<BabyBear, 4>>() {
            let mut base_slice = [BabyBear::from_wrapped_u32(0); 4];

            for idx in 0..4 {
                // If we have buffered inputs, we must perform a duplexing so that the challenge will
                // reflect them. Or if we've run out of outputs, we must perform a duplexing to get more.
                if !self.input_buffer.is_empty() || self.output_buffer.is_empty() {
                    self.duplexing();
                }
                let value = self
                    .output_buffer
                    .pop()
                    .expect("Output buffer should be non-empty");

                let base_v = BabyBear::from_pf(&value);
                base_slice[idx] = base_v;

                sample_input.push(value);
            }

            // commit records
            let output = BinomialExtensionField::<BabyBear, 4>::from_base_slice(&base_slice);
            res = *(&output as &dyn Any).downcast_ref::<F>().unwrap();
        } else {
            panic!("the type of base or f is invalid")
        } // no other implementation yet
        self.record_sample(&sample_input, &res);

        //TODO:adapt our challenger expr implementation
        //self.output_buffer.clear();
        res
    }
}

pub trait BitExtractor {
    fn as_usize(&self) -> usize;
}

impl BitExtractor for BabyBear {
    fn as_usize(&self) -> usize {
        self.as_canonical_u32() as usize
    }
}

impl BitExtractor for BinomialExtensionField<BabyBear, 4> {
    fn as_usize(&self) -> usize {
        let s: BabyBear = *<Self as AbstractExtensionField<BabyBear>>::as_base_slice(self)
            .first()
            .unwrap();
        s.as_canonical_u32() as usize
    }
}

impl<F, PF, P, const WIDTH: usize> CanSampleBits<usize> for BfChallenger<F, PF, P, WIDTH>
where
    F: Field + BitExtractor,
    PF: PermutationField<4>,
    P: CryptographicPermutation<[PF; WIDTH]>,
{
    fn sample_bits(&mut self, bits: usize) -> usize {
        debug_assert!(bits < (usize::BITS as usize));
        // debug_assert!((1 << bits) < BASE::ORDER_U64);
        let rand_f = self.sample();
        // make it possible to check a point is valid in pow grinding
        let rand_usize = rand_f.as_usize();
        rand_usize >> (32 - bits)
    }
}
