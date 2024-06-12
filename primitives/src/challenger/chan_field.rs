use core::{alloc, array};

use ::alloc::vec;
use p3_baby_bear::BabyBear;
use p3_field::PrimeField32;
pub trait ChallengeField<const U8_NUM: usize>: PrimeField32 + Clone + Default + Copy + Ord {
    fn u8_num() -> usize {
        U8_NUM
    }

    fn from_pf<const PF_U8_NUM: usize, PF: PermutationField<PF_U8_NUM>>(pf: &PF) -> Self {
        assert_eq!(PF_U8_NUM, U8_NUM);
        let u8_arr: [u8; 4] = array::from_fn(|i| pf.as_u8_array()[i]);
        let value = u32::from_le_bytes(u8_arr);
        let actual_value = value % Self::ORDER_U32;
        Self::from_canonical_u32(actual_value)
    }
}

impl ChallengeField<4> for BabyBear {}

// the PremutationField only support U8_NUM<=8
// Use LittleEndian
pub trait PermutationField<const U8_NUM: usize>:
    Clone + Default + Copy + Ord + Sized + Send + Sync
{
    fn u8_num() -> usize {
        U8_NUM
    }

    fn as_u8_array(&self) -> [u8; U8_NUM];

    fn from_u8_array(array: &[u8]) -> Self;

    fn mod_p() -> u128 {
        assert!(U8_NUM <= 8);
        let mut by = vec![1u8];
        for _ in 0..U8_NUM {
            by.push(0);
        }
        1 << U8_NUM * 3
    }

    fn from_u64(value: u64) -> Self {
        Self::from_u8_array(&value.to_le_bytes()[0..U8_NUM])
    }
}

pub type U8 = [u8; 1];
impl PermutationField<1> for U8 {
    fn as_u8_array(&self) -> [u8; 1] {
        *self
    }

    fn from_u8_array(array: &[u8]) -> Self {
        assert!(array.len() == 1);
        let arr: [u8; 1] = [array[0]];
        arr
    }
}
pub type U32 = [u8; 4];
impl PermutationField<4> for U32 {
    fn as_u8_array(&self) -> U32 {
        *self
    }

    fn from_u8_array(array: &[u8]) -> Self {
        assert!(array.len() <= 4);
        let arr: [u8; 4] = array::from_fn(|i| array[i]);
        arr
    }
}

pub type U256 = [u8; 32];
impl PermutationField<32> for U256 {
    fn as_u8_array(&self) -> [u8; 32] {
        *self
    }

    fn from_u8_array(array: &[u8]) -> Self {
        assert!(array.len() <= 32);
        let arr: [u8; 32] = array::from_fn(|i| array[i]);
        arr
    }
}

pub fn u256_to_u32(data: U256) -> [U32; 8] {
    let mut result: [[u8; 4]; 8] = [[0; 4]; 8];

    for i in 0..8 {
        let slice = &data[i * 4..(i + 1) * 4];
        result[i].copy_from_slice(slice);
    }
    result
}

pub fn u32_to_u256(data: [U32; 8]) -> U256 {
    let mut result: [u8; 32] = [0; 32];

    for (i, small_array) in data.iter().enumerate() {
        let start_index = i * 4;
        result[start_index..start_index + 4].copy_from_slice(small_array);
    }
    result
}
