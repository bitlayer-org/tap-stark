use bitcoin::opcodes::{OP_DUP, OP_SWAP};
use bitcoin::ScriptBuf as Script;
use bitcoin_script::{define_pushable, script};
use p3_field::{AbstractField, TwoAdicField};
use p3_util::{log2_ceil_u64, log2_ceil_usize, log2_strict_usize, reverse_bits_len};

use crate::u31::{babybear, U31Config};
use crate::{u31_double, u31_mul};

pub struct BabyBearU31;
impl U31Config for BabyBearU31 {
    const MOD: u32 = 15 * (1 << 27) + 1;
}
