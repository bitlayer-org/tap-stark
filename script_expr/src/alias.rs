use std::collections::BTreeMap;
use std::iter::{Product, Sum};
use std::marker::PhantomData;
use std::ops::{Add, AddAssign, Deref, DerefMut, Mul, MulAssign, Neg, Sub, SubAssign};
// #[macro_use]
// extern crate lazy_static;
use std::sync::Mutex;
use std::sync::{Arc, RwLock, RwLockReadGuard, RwLockWriteGuard};
use std::usize;

use bitcoin_script_stack::stack::{StackTracker, StackVariable};
use common::{AbstractField, BabyBear};
use lazy_static::lazy_static;
use primitives::field::BfField;

use crate::{
    CustomOpcode, Expression, IdCount, InputManager, ManagerAssign, ScriptExprError,
    StandardOpcode, StandardOpcodeId, Variable, DYNAMIC_INPUT_OR_OUTPUT,
};
lazy_static! {
    static ref OPID: Mutex<u32> = Mutex::new(0);
}

pub(crate) fn get_opid() -> u32 {
    let mut id = OPID.lock().unwrap();
    *id += 1;
    *id
}

pub type ExprPtr = Arc<RwLock<Box<dyn Expression>>>;
pub type ExprRead<'a> = RwLockReadGuard<'a, Box<dyn Expression>>;
pub type ExprWrite<'a> = RwLockWriteGuard<'a, Box<dyn Expression>>;

#[derive(Debug)]
pub struct Dsl<F: BfField>(ExprPtr, PhantomData<F>);
impl<F: BfField> Deref for Dsl<F> {
    type Target = ExprPtr;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<F: BfField> DerefMut for Dsl<F> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<F: BfField> Clone for Dsl<F> {
    fn clone(&self) -> Self {
        Self(self.0.clone(), PhantomData::<F>)
    }
}

impl<F: BfField> Dsl<F> {
    pub(crate) fn get_var_size(&self) -> u32 {
        self.read().unwrap().var_size()
    }

    pub(crate) fn get_id(&self) -> u32 {
        self.read().unwrap().get_id()
    }

    pub(crate) fn new(expr: ExprPtr) -> Dsl<F> {
        Dsl(expr, PhantomData::<F>)
    }

    pub(crate) fn new_equal(lhs: Self, rhs: Self) -> Dsl<F> {
        Self(
            Arc::new(RwLock::new(Box::new(StandardOpcode::<2, 1>::new(
                get_opid(),
                vec![lhs.into(), rhs.into()],
                1, // the var size must be 1 for equal op_code
                StandardOpcodeId::Equal,
            )))),
            PhantomData::<F>,
        )
    }

    pub(crate) fn new_expconst(lhs: Self, power: u32) -> Dsl<F> {
        let var_size = lhs.read().unwrap().var_size();
        Self(
            Arc::new(RwLock::new(Box::new(CustomOpcode::<1, 1, F>::new(
                get_opid(),
                vec![vec![power]],
                vec![lhs.into()],
                var_size, // the var size must be 1 for equal op_code
                StandardOpcodeId::ExpConst,
            )))),
            PhantomData::<F>,
        )
    }

    pub fn index_to_rou(index: u32, sub_group_bits: u32) -> Self {
        assert_eq!(F::U32_SIZE, 1);
        Self(
            Arc::new(RwLock::new(Box::new(CustomOpcode::<1, 1, F>::new(
                get_opid(),
                vec![vec![sub_group_bits]],
                vec![Self::constant_u32(index).into()],
                F::U32_SIZE as u32, // the var size must be 1 for equal op_code
                StandardOpcodeId::IndexToRou,
            )))),
            PhantomData::<F>,
        )
    }

    pub fn index_to_rou_ext<Base: BfField>(index: u32, sub_group_bits: u32) -> Self {
        assert_eq!(Base::U32_SIZE, 1);
        assert_eq!(F::U32_SIZE, 4);
        Self(
            Arc::new(RwLock::new(Box::new(CustomOpcode::<1, 1, F>::new(
                get_opid(),
                vec![vec![sub_group_bits]],
                vec![Dsl::<Base>::constant_u32(index).into()],
                F::U32_SIZE as u32, // the var size must be 1 for equal op_code
                StandardOpcodeId::IndexToRou,
            )))),
            PhantomData::<F>,
        )
    }

    pub fn index_to_rou_dsl(self, sub_group_bits: u32) -> Self {
        assert_eq!(F::U32_SIZE, 1);
        Self(
            Arc::new(RwLock::new(Box::new(CustomOpcode::<1, 1, F>::new(
                get_opid(),
                vec![vec![sub_group_bits]],
                vec![self.into()],
                F::U32_SIZE as u32, // the var size must be 1 for equal op_code
                StandardOpcodeId::IndexToRou,
            )))),
            PhantomData::<F>,
        )
    }

    pub fn reverse_bits_len<Base: BfField>(index:u32, bit_len: u32)  -> Self {
        Self(
            Arc::new(RwLock::new(Box::new(CustomOpcode::<1, 1, F>::new(
                get_opid(),
                vec![vec![index], vec![bit_len]],
                vec![Dsl::<Base>::constant_u32(index).into()],
                1, // the var size must be 1 for equal op_code
                StandardOpcodeId::ReverseBitslen,
            )))),
            PhantomData::<F>,
        )
    }


    pub(crate) fn new_equal_verify(lhs: Self, rhs: Self) -> Dsl<F> {
        Self(
            Arc::new(RwLock::new(Box::new(StandardOpcode::<2, 0>::new(
                get_opid(),
                vec![lhs.into(), rhs.into()],
                0,
                StandardOpcodeId::EqualVerify,
            )))),
            PhantomData::<F>,
        )
    }

    pub fn square(self) -> Self {
        let var_size = self.read().unwrap().var_size();
        Self(
            Arc::new(RwLock::new(Box::new(StandardOpcode::<1, 1>::new(
                get_opid(),
                vec![self.into()],
                var_size,
                StandardOpcodeId::Square,
            )))),
            PhantomData,
        )
    }

    pub fn double(self) -> Self {
        let var_size = self.read().unwrap().var_size();
        Self(
            Arc::new(RwLock::new(Box::new(StandardOpcode::<1, 1>::new(
                get_opid(),
                vec![self.into()],
                var_size,
                StandardOpcodeId::Double,
            )))),
            PhantomData,
        )
    }

    pub fn exp_constant(self, power: u32) -> Self {
        Self::new_expconst(self, power)
    }

    pub fn num_to_field(self) -> Self {
        Self(
            Arc::new(RwLock::new(Box::new(StandardOpcode::<1, 1>::new(
                get_opid(),
                vec![self.into()],
                F::U32_SIZE as u32,
                StandardOpcodeId::NumToField,
            )))),
            PhantomData::<F>,
        )
    }

    pub fn lookup(self, index: u32, len: usize) -> Self {
        let index = Self::constant_u32(index);
        Self(
            Arc::new(RwLock::new(Box::new(CustomOpcode::<2, 1, F>::new(
                get_opid(),
                vec![vec![len as u32]],
                vec![self.into(), index.into()],
                F::U32_SIZE as u32,
                StandardOpcodeId::Lookup,
            )))),
            PhantomData::<F>,
        )
    }

    pub fn from_table(table: &[F]) -> Self {
        let vs = table.iter().map(|f| f.as_u32_vec()).collect::<Vec<_>>();
        Self(
            Arc::new(RwLock::new(Box::new(CustomOpcode::<
                0,
                DYNAMIC_INPUT_OR_OUTPUT,
                F,
            >::new(
                get_opid(),
                vs,
                vec![],
                F::U32_SIZE as u32,
                StandardOpcodeId::Table,
            )))),
            PhantomData::<F>,
        )
    }

    pub fn sponge_state_init() -> Self {
        let vs = (0..32).map(|x| vec![0]).collect::<Vec<_>>();
        Self(
            Arc::new(RwLock::new(Box::new(CustomOpcode::<
                0,
                DYNAMIC_INPUT_OR_OUTPUT,
                F,
            >::new(
                get_opid(),
                vs,
                vec![],
                1,
                StandardOpcodeId::Table,
            )))),
            PhantomData::<F>,
        )
    }

    pub fn add_ext<EF: BfField>(self, rhs: Dsl<EF>) -> Dsl<EF> {
        assert_eq!(F::U32_SIZE, 1);
        assert_eq!(EF::U32_SIZE, 4);
        Dsl::<EF>(
            Arc::new(RwLock::new(Box::new(StandardOpcode::<2, 1>::new(
                get_opid(),
                vec![self.into(), rhs.into()],
                EF::U32_SIZE as u32,
                StandardOpcodeId::Add,
            )))),
            PhantomData,
        )
    }

    pub fn add_base<Base: BfField>(self, rhs: Dsl<Base>) -> Self {
        assert_eq!(F::U32_SIZE, 4);
        assert_eq!(Base::U32_SIZE, 1);
        Self(
            Arc::new(RwLock::new(Box::new(StandardOpcode::<2, 1>::new(
                get_opid(),
                vec![self.into(), rhs.into()],
                F::U32_SIZE as u32,
                StandardOpcodeId::Add,
            )))),
            PhantomData,
        )
    }

    pub fn mul_ext<EF: BfField>(self, rhs: Dsl<EF>) -> Dsl<EF> {
        assert_eq!(F::U32_SIZE, 1);
        assert_eq!(EF::U32_SIZE, 4);
        Dsl::<EF>(
            Arc::new(RwLock::new(Box::new(StandardOpcode::<2, 1>::new(
                get_opid(),
                vec![self.into(), rhs.into()],
                EF::U32_SIZE as u32,
                StandardOpcodeId::Mul,
            )))),
            PhantomData,
        )
    }

    pub fn mul_base<Base: BfField>(self, rhs: Dsl<Base>) -> Self {
        assert_eq!(F::U32_SIZE, 4);
        assert_eq!(Base::U32_SIZE, 1);
        Self(
            Arc::new(RwLock::new(Box::new(StandardOpcode::<2, 1>::new(
                get_opid(),
                vec![self.into(), rhs.into()],
                F::U32_SIZE as u32,
                StandardOpcodeId::Mul,
            )))),
            PhantomData,
        )
    }

    pub fn sub_ext<EF: BfField>(self, rhs: Dsl<EF>) -> Dsl<EF> {
        assert_eq!(F::U32_SIZE, 1);
        assert_eq!(EF::U32_SIZE, 4);
        Dsl::<EF>(
            Arc::new(RwLock::new(Box::new(StandardOpcode::<2, 1>::new(
                get_opid(),
                vec![self.into(), rhs.into()],
                EF::U32_SIZE as u32,
                StandardOpcodeId::Sub,
            )))),
            PhantomData,
        )
    }

    pub fn sub_base<Base: BfField>(self, rhs: Dsl<Base>) -> Self {
        assert_eq!(F::U32_SIZE, 4);
        assert_eq!(Base::U32_SIZE, 1);
        Self(
            Arc::new(RwLock::new(Box::new(StandardOpcode::<2, 1>::new(
                get_opid(),
                vec![self.into(), rhs.into()],
                F::U32_SIZE as u32,
                StandardOpcodeId::Sub,
            )))),
            PhantomData,
        )
    }

    pub fn equal(self, other: Self) -> Self {
        Self::new_equal(self, other)
    }

    pub fn equal_for_f(self, other: F) -> Self {
        Self::new_equal(self, Self::constant(other.as_u32_vec()))
    }

    pub fn equal_verify(self, other: Self) -> Self {
        Self::new_equal_verify(self, other)
    }

    pub fn equal_verify_for_f(self, other: F) -> Self {
        Self::new_equal_verify(self, Self::constant(other.as_u32_vec()))
    }

    pub fn constant(values: Vec<u32>) -> Self {
        Self(
            Arc::new(RwLock::new(Box::new(CustomOpcode::<0, 1, F>::new(
                get_opid(),
                vec![values.clone()],
                vec![],
                values.len() as u32,
                StandardOpcodeId::Constant,
            )))),
            PhantomData::<F>,
        )
    }

    pub fn constant_f(value: F) -> Self {
        Self::constant(value.as_u32_vec())
    }

    pub fn constant_u32(value: u32) -> Self {
        Self::constant(vec![value])
    }

    pub fn blake3(state: &[Self]) -> Self {
        let state = state.iter().map(|x| x.clone().into()).collect::<Vec<_>>();
        Self(
            Arc::new(RwLock::new(Box::new(StandardOpcode::<33, 32>::new(
                get_opid(),
                state,
                F::U32_SIZE as u32,
                StandardOpcodeId::Blake3Perm,
            )))),
            PhantomData,
        )
    }

    pub fn to_sample(self) -> Self {
        Self(
            Arc::new(RwLock::new(Box::new(StandardOpcode::<1, 8>::new(
                get_opid(),
                vec![self.into()],
                F::U32_SIZE as u32,
                StandardOpcodeId::ToSample,
            )))),
            PhantomData,
        )
    }

    pub fn sample_base(self) -> Self {
        Self(
            Arc::new(RwLock::new(Box::new(StandardOpcode::<1, 1>::new(
                get_opid(),
                vec![self.into()],
                1,
                StandardOpcodeId::SampleBase,
            )))),
            PhantomData,
        )
    }

    pub fn sample_ext(self) -> Self {
        Self(
            Arc::new(RwLock::new(Box::new(StandardOpcode::<1, 1>::new(
                get_opid(),
                vec![self.into()],
                4,
                StandardOpcodeId::SampleExt,
            )))),
            PhantomData,
        )
    }
}

impl<F: BfField> Dsl<F> {
    pub fn read(&self) -> Result<ExprRead, ScriptExprError> {
        self.0.read().map_err(|_| ScriptExprError::ReadLockError)
    }

    pub fn write(&self) -> Result<ExprWrite, ScriptExprError> {
        self.0.write().map_err(|_| ScriptExprError::WriteLockError)
    }

    pub fn opcode(&self) -> StandardOpcodeId {
        self.read().unwrap().opcode()
    }

    pub fn debug(self) -> Self {
        self.read().unwrap().set_debug();
        self
    }

    pub fn set_debug(&self) {
        self.read().unwrap().set_debug();
    }

    pub fn simulate_express(&self, id_mapper: &mut BTreeMap<u32, IdCount>) {
        self.read().unwrap().simulate_express(id_mapper)
    }

    pub fn express_to_script(
        &self,
        stack: &mut StackTracker,
        bmap: &BTreeMap<Variable, StackVariable>,
        id_mapper: &mut BTreeMap<u32, IdCount>,
        optimize: bool,
    ) -> Vec<StackVariable> {
        self.read()
            .unwrap()
            .express_to_script(stack, bmap, id_mapper, optimize)
    }

    pub fn express(
        &self,
        stack: &mut StackTracker,
        var_getter: &BTreeMap<Variable, StackVariable>,
    ) -> (Vec<StackVariable>, BTreeMap<u32, IdCount>) {
        let mut id_mapper = BTreeMap::new();
        self.read().unwrap().simulate_express(&mut id_mapper);
        (
            self.express_to_script(stack, &var_getter, &mut id_mapper, true),
            id_mapper,
        )
    }

    pub fn express1(
        &self,
        stack: &mut StackTracker,
        var_getter: &BTreeMap<Variable, StackVariable>,
        optimize: bool,
    ) -> (Vec<StackVariable>, BTreeMap<u32, IdCount>) {
        let mut id_mapper = BTreeMap::new();
        self.read().unwrap().simulate_express(&mut id_mapper);
        (
            self.express_to_script(stack, &var_getter, &mut id_mapper, optimize),
            id_mapper,
        )
    }

    pub fn express_with_optimize(
        &self,
    ) -> (
        StackTracker,
        BTreeMap<Variable, StackVariable>,
        BTreeMap<u32, IdCount>,
    ) {
        let mut stack = StackTracker::new();
        let var_getter = BTreeMap::new();
        let mut id_mapper = BTreeMap::new();
        self.read().unwrap().simulate_express(&mut id_mapper);
        self.express_to_script(&mut stack, &var_getter, &mut id_mapper, true);
        (stack, var_getter, id_mapper)
    }

    pub fn express_without_optimize(
        &self,
    ) -> (
        StackTracker,
        BTreeMap<Variable, StackVariable>,
        BTreeMap<u32, IdCount>,
    ) {
        let mut stack = StackTracker::new();
        let var_getter = BTreeMap::new();
        let mut id_mapper = BTreeMap::new();
        self.read().unwrap().simulate_express(&mut id_mapper);
        self.express_to_script(&mut stack, &var_getter, &mut id_mapper, false);
        (stack, var_getter, id_mapper)
    }
}

impl<F: BfField> From<F> for Dsl<F> {
    fn from(expr: F) -> Self {
        Self::constant_f(expr)
    }
}

impl<F: BfField> From<Dsl<F>> for ExprPtr {
    fn from(expr: Dsl<F>) -> Self {
        expr.0
    }
}

impl<F: BfField> Default for Dsl<F> {
    fn default() -> Self {
        Self::constant_f(F::zero())
    }
}

impl<F: BfField> AbstractField for Dsl<F> {
    type F = F;

    fn zero() -> Self {
        Self::constant_f(F::zero())
    }
    fn one() -> Self {
        Self::constant_f(F::one())
    }
    fn two() -> Self {
        Self::constant_f(F::two())
    }
    fn neg_one() -> Self {
        Self::constant_f(F::neg_one())
    }

    #[inline]
    fn from_f(f: Self::F) -> Self {
        Self::constant_f(f)
    }

    fn from_bool(b: bool) -> Self {
        Self::constant_f(F::from_bool(b))
    }

    fn from_canonical_u8(n: u8) -> Self {
        Self::constant_f(F::from_canonical_u8(n))
    }

    fn from_canonical_u16(n: u16) -> Self {
        Self::constant_f(F::from_canonical_u16(n))
    }

    fn from_canonical_u32(n: u32) -> Self {
        Self::constant_f(F::from_canonical_u32(n))
    }

    fn from_canonical_u64(n: u64) -> Self {
        Self::constant_f(F::from_canonical_u64(n))
    }

    fn from_canonical_usize(n: usize) -> Self {
        Self::constant_f(F::from_canonical_usize(n))
    }

    fn from_wrapped_u32(n: u32) -> Self {
        Self::constant_f(F::from_wrapped_u32(n))
    }

    fn from_wrapped_u64(n: u64) -> Self {
        Self::constant_f(F::from_wrapped_u64(n))
    }

    fn generator() -> Self {
        Self::constant_f(F::generator())
    }
}

impl<F: BfField> Add for Dsl<F> {
    type Output = Dsl<F>;
    fn add(self, other: Dsl<F>) -> Self::Output {
        let var_size = self
            .read()
            .unwrap()
            .var_size()
            .max(other.read().unwrap().var_size());

        Self(
            Arc::new(RwLock::new(Box::new(StandardOpcode::<2, 1>::new(
                get_opid(),
                vec![self.into(), other.into()],
                var_size,
                StandardOpcodeId::Add,
            )))),
            PhantomData::<F>,
        )
    }
}

impl<F: BfField> Add<&Self> for Dsl<F> {
    type Output = Dsl<F>;
    fn add(self, other: &Dsl<F>) -> Self::Output {
        let var_size = self
            .read()
            .unwrap()
            .var_size()
            .max(other.read().unwrap().var_size());

        Self(
            Arc::new(RwLock::new(Box::new(StandardOpcode::<2, 1>::new(
                get_opid(),
                vec![self.into(), other.clone().into()],
                var_size,
                StandardOpcodeId::Add,
            )))),
            PhantomData::<F>,
        )
    }
}

impl<F: BfField> Add<F> for Dsl<F> {
    type Output = Dsl<F>;
    fn add(self, other: F) -> Self::Output {
        self + Self::constant_f(other)
    }
}

impl<F: BfField> AddAssign for Dsl<F> {
    fn add_assign(&mut self, rhs: Self) {
        let c: Dsl<F> = self.clone();
        *self = c + rhs;
    }
}

impl<F: BfField> AddAssign<F> for Dsl<F> {
    fn add_assign(&mut self, rhs: F) {
        *self += Self::constant_f(rhs);
    }
}

impl<F: BfField> Sum for Dsl<F> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|x, y| x + y).unwrap_or(Self::zero())
    }
}

impl<F: BfField> Sub for Dsl<F> {
    type Output = Dsl<F>;
    fn sub(self, other: Dsl<F>) -> Self::Output {
        let var_size = self
            .read()
            .unwrap()
            .var_size()
            .max(other.read().unwrap().var_size());

        Self(
            Arc::new(RwLock::new(Box::new(StandardOpcode::<2, 1>::new(
                get_opid(),
                vec![self.into(), other.into()],
                var_size,
                StandardOpcodeId::Sub,
            )))),
            PhantomData::<F>,
        )
    }
}

impl<F: BfField> Sub<F> for Dsl<F> {
    type Output = Dsl<F>;
    fn sub(self, other: F) -> Self::Output {
        self - Self::constant(other.as_u32_vec())
    }
}

impl<F: BfField> SubAssign for Dsl<F> {
    fn sub_assign(&mut self, rhs: Self) {
        let c: Dsl<F> = self.clone();
        *self = c - rhs;
    }
}

impl<F: BfField> SubAssign<ExprPtr> for Dsl<F> {
    fn sub_assign(&mut self, rhs: ExprPtr) {
        *self -= Self::new(rhs);
    }
}

impl<F: BfField> Mul for Dsl<F> {
    type Output = Dsl<F>;
    fn mul(self, other: Dsl<F>) -> Self::Output {
        let var_size = self
            .read()
            .unwrap()
            .var_size()
            .max(other.read().unwrap().var_size());

        Self(
            Arc::new(RwLock::new(Box::new(StandardOpcode::<2, 1>::new(
                get_opid(),
                vec![self.into(), other.into()],
                var_size,
                StandardOpcodeId::Mul,
            )))),
            PhantomData::<F>,
        )
    }
}

impl<F: BfField> Mul<F> for Dsl<F> {
    type Output = Dsl<F>;
    fn mul(self, other: F) -> Self::Output {
        self * Self::constant(other.as_u32_vec())
    }
}

impl<F: BfField> MulAssign for Dsl<F> {
    fn mul_assign(&mut self, rhs: Self) {
        let c: Dsl<F> = self.clone();
        *self = c * rhs;
    }
}

impl<F: BfField> MulAssign<F> for Dsl<F> {
    fn mul_assign(&mut self, rhs: F) {
        *self *= Self::constant(rhs.as_u32_vec());
    }
}

impl<F: BfField> Neg for Dsl<F> {
    type Output = Dsl<F>;
    fn neg(self) -> Self::Output {
        let var_size = self.read().unwrap().var_size();

        Self(
            Arc::new(RwLock::new(Box::new(StandardOpcode::<1, 1>::new(
                get_opid(),
                vec![self.into()],
                var_size,
                StandardOpcodeId::Neg,
            )))),
            PhantomData,
        )
    }
}

impl<F: BfField> Product for Dsl<F> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|x, y| x * y).unwrap_or(Self::one())
    }
}

impl<F: BfField> Product<ExprPtr> for Dsl<F> {
    fn product<I: Iterator<Item = ExprPtr>>(iter: I) -> Self {
        iter.map(|x| Self::new(x)).product()
    }
}

#[cfg(test)]
mod tests {
    use alloc::boxed::Box;
    use alloc::collections::BTreeMap;
    use alloc::sync::Arc;
    use alloc::vec::Vec;
    use p3_util::reverse_bits_len;
    use core::cell::{self, Cell};

    use bitcoin_script_stack::stack::{self, StackTracker, StackVariable};
    use common::{AbstractField, BabyBear, BinomialExtensionField};
    use p3_air::AirBuilder;
    use p3_field::TwoAdicField;
    use p3_matrix::Matrix;
    use primitives::field::BfField;
    use scripts::treepp::*;
    use scripts::u31_lib::{u31_equalverify, u31ext_equalverify, BabyBear4};

    use super::{Dsl, Expression, Variable, *};
    use crate::InputManager;
    type F = BabyBear;
    type EF = BinomialExtensionField<BabyBear, 4>;

    #[test]
    fn test_expr_double() {
        {
            let bmap = BTreeMap::new();
            let mut stack = StackTracker::new();
            let a_value = BabyBear::two();
            let b_value = a_value.clone() + a_value;

            let a = Dsl::constant_f(a_value);
            let b = a.double();
            let equal = b.equal_verify_for_f(b_value);
            equal.express(&mut stack, &bmap);
            stack.op_true();
            let res = stack.run();
            assert!(res.success);
        }

        {
            let bmap = BTreeMap::new();
            let mut stack = StackTracker::new();
            let a_value = EF::two();
            let b_value = a_value.clone() + a_value;
            let a = Dsl::constant_f(a_value);
            let b = a.double();
            let equal = b.equal_verify_for_f(b_value);
            equal.express(&mut stack, &bmap);
            stack.op_true();
            let res = stack.run();
            assert!(res.success);
        }
    }

    #[test]
    fn test_expr_square() {
        {
            let bmap = BTreeMap::new();
            let mut stack = StackTracker::new();
            let a_value = BabyBear::two();
            let b_value = a_value.exp_u64(2);

            let a = Dsl::constant_f(a_value);
            let b = a.square();
            let equal = b.equal_verify_for_f(b_value);
            equal.express(&mut stack, &bmap);
            stack.op_true();
            let res = stack.run();
            assert!(res.success);
        }

        {
            let bmap = BTreeMap::new();
            let mut stack = StackTracker::new();
            let a_value = EF::two();
            let b_value = a_value.exp_u64(2);
            let a = Dsl::constant_f(a_value);
            let b = a.square();
            let equal = b.equal_verify_for_f(b_value);
            equal.express(&mut stack, &bmap);
            stack.op_true();
            let res = stack.run();
            assert!(res.success);
        }
    }

    #[test]
    fn test_expr_expconst() {
        {
            let bmap = BTreeMap::new();
            let mut stack = StackTracker::new();
            let a_value = BabyBear::two();
            let b_value = a_value.exp_u64(2);
            let a = Dsl::constant_f(a_value);
            let b = a.exp_constant(2);
            let equal = b.equal_verify_for_f(b_value);
            equal.express(&mut stack, &bmap);
            stack.op_true();
            let res = stack.run();
            assert!(res.success);
        }

        {
            let bmap = BTreeMap::new();
            let mut stack = StackTracker::new();
            let a_value = EF::two();
            let b_value = a_value.exp_u64(2);
            let a = Dsl::constant_f(a_value);
            let b = a.exp_constant(2);
            let equal = b.equal_verify_for_f(b_value);
            equal.express(&mut stack, &bmap);
            stack.op_true();
            let res = stack.run();
            assert!(res.success);
        }
    }

    #[test]
    fn test_index_to_rou() {
        {
            let bmap = BTreeMap::new();
            let mut stack = StackTracker::new();
            let sub_group_bits = 10u32;
            let generator = BabyBear::two_adic_generator(sub_group_bits as usize);
            let index = 7u32;
            let res = generator.exp_u64(index as u64);

            let b = Dsl::<BabyBear>::index_to_rou(index, sub_group_bits);
            // b.set_debug();
            let res_expr = Dsl::constant_f(res);
            let equal = b.equal_verify(res_expr);
            equal.express(&mut stack, &bmap);
            stack.op_true();
            let res = stack.run();
            assert!(res.success);
        }

        {
            let bmap = BTreeMap::new();
            let mut stack = StackTracker::new();
            let sub_group_bits = 10u32;
            let generator = EF::two_adic_generator(sub_group_bits as usize);
            let index = 7u32;
            let res = generator.exp_u64(index as u64);

            let b = Dsl::<EF>::index_to_rou_ext::<F>(index, sub_group_bits);
            let res_dsl = Dsl::constant_f(res);
            assert_eq!(b.get_var_size(), res_dsl.get_var_size());
            // assert_eq!(b.get)
            let equal = b.equal_verify(res_dsl);
            equal.express(&mut stack, &bmap);
            stack.op_true();
            let res = stack.run();
            assert!(res.success);
        }
    }

    #[test]
    fn test_num_to_field() {
        let num = 182712u32;

        {
            let bmap = BTreeMap::new();
            let mut stack = StackTracker::new();
            let a = Dsl::constant_u32(num);
            let b = a.num_to_field();
            let res = BabyBear::from_canonical_u32(num);
            let equal = b.equal_verify_for_f(res);
            equal.express(&mut stack, &bmap);
            stack.op_true();
            let res = stack.run();
            assert!(res.success);
        }
    }

    #[test]
    fn test_script_expression_add() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = Dsl::constant_f(BabyBear::one());
        let b = Dsl::constant_f(BabyBear::two());
        let c = a + b;
        c.set_debug();

        let d = Dsl::constant_f(BabyBear::two());
        let e = Dsl::constant_f(BabyBear::two());
        let f = d + e;

        let g = c + f; // 4 + 3 = 7
        let script = g.express(&mut stack, &bmap);
        stack.number(BabyBear::from_canonical_u32(7u32).as_u32_vec()[0]);
        stack.op_equal();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_script_expression_u31add_u31ext() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = Dsl::constant_f(BabyBear::one());
        let b = Dsl::constant_f(EF::two());
        let c = a.add_ext(b);

        let d = Dsl::constant_f(BabyBear::two());
        let e = Dsl::constant_f(EF::two());
        let f = e.add_base(d);

        let g = c + f; // 4 + 3 = 7
        let h = g.equal_verify_for_f(EF::from_canonical_u32(7u32));
        let script = h.express(&mut stack, &bmap);
        stack.op_true();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_script_expression_u31sub_u31ext() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = Dsl::constant_f(BabyBear::one());
        let b = Dsl::constant_f(EF::two());
        let c = a.sub_ext(b);

        let d = Dsl::constant_f(BabyBear::two());
        let e = Dsl::constant_f(EF::from_canonical_u32(4));
        let f = e.sub_base(d);
        let g = c + f; // 4 + 3 = 7
        let script = g.express(&mut stack, &bmap);
        stack.bignumber(EF::from_canonical_u32(1u32).as_u32_vec());
        stack.custom(
            u31ext_equalverify::<BabyBear4>(),
            2,
            false,
            0,
            "u31ext_equalverify",
        );
        stack.op_true();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_script_expression_u31mul_u31ext() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = Dsl::constant_f(BabyBear::one());
        let b = Dsl::constant_f(EF::two());
        b.set_debug();
        // let c = a.mul_ext(b);
        let c = b.mul_base(a);
        c.set_debug();
        let d = Dsl::constant_f(BabyBear::two());
        let e = Dsl::constant_f(EF::from_canonical_u32(4));
        let f = e.mul_base(d);
        f.set_debug();
        let g = c * f;
        let equal = g.equal_for_f(EF::from_canonical_u32(16));
        equal.express(&mut stack, &bmap);
        let res = stack.run();
        println!("{:?}", res.error);
        println!("{:?}", res.error_msg);
        assert!(res.success);
    }

    #[test]
    fn test_ext_constant() {
        let mut stack = StackTracker::new();
        let bmap = BTreeMap::new();
        let a = Dsl::constant_f(EF::one());
        a.express(&mut stack, &bmap);
        let res = EF::one();

        stack.bignumber(res.as_u32_vec());
        stack.custom(
            u31ext_equalverify::<BabyBear4>(),
            2,
            false,
            0,
            "u31ext_equalverify",
        );

        stack.op_true();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_script_expr_with_input() {
        let mut input_manager = InputManager::new();
        let var1_wrap =
            input_manager.assign_input::<BabyBear>(BabyBear::from_canonical_u32(1u32).as_u32_vec());
        let var2_wrap =
            input_manager.assign_input::<BabyBear>(BabyBear::from_canonical_u32(2u32).as_u32_vec());
        let var3_wrap =
            input_manager.assign_input::<BabyBear>(BabyBear::from_canonical_u32(3u32).as_u32_vec());
        let var4_wrap =
            input_manager.assign_input::<BabyBear>(BabyBear::from_canonical_u32(4u32).as_u32_vec());
        let (mut stack, input_getter) = input_manager.simulate_input();

        let res1 = var1_wrap + var2_wrap;
        let res2 = var3_wrap + var4_wrap;

        let res = res1 + res2;
        res.express(&mut stack, &input_getter);

        stack.number(BabyBear::from_canonical_u32(10u32).as_u32_vec()[0]);
        stack.op_equalverify();

        stack.debug();
        stack.op_true();
        let res = stack.run();
        assert!(res.success);

        {
            let mut input_manager = InputManager::new();
            let var1_wrap = input_manager.assign_input(EF::from_canonical_u32(1u32).as_u32_vec());
            let var2_wrap = input_manager.assign_input(EF::from_canonical_u32(2u32).as_u32_vec());
            let var3_wrap = input_manager.assign_input(EF::from_canonical_u32(3u32).as_u32_vec());
            let var4_wrap = input_manager.assign_input(EF::from_canonical_u32(4u32).as_u32_vec());
            let (mut stack, input_getter) = input_manager.simulate_input();

            let res1 = var1_wrap + var2_wrap;
            let res2 = var3_wrap + var4_wrap;

            let res = res1 + res2;
            let equal = res.equal_for_f(EF::from_canonical_u32(10));
            equal.debug().express(&mut stack, &input_getter);
            let res = stack.run();
            assert!(res.success);
        }
    }

    #[test]
    fn test_script_expression_extadd() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = Dsl::constant_f(EF::one());
        let b = Dsl::constant_f(EF::two());
        let c = a + b;

        let script = c.express(&mut stack, &bmap);
        stack.debug();
        let res = EF::one() + EF::two();

        stack.bignumber(res.as_u32_vec());
        stack.debug();
        stack.custom(
            u31ext_equalverify::<BabyBear4>(),
            2,
            false,
            0,
            "u31ext_equalverify",
        );
        stack.op_true();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_script_expression_sub() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = Dsl::constant_f(BabyBear::one());
        let b = Dsl::constant_f(BabyBear::two());
        let c = b - a; // 1

        let d = Dsl::constant_f(BabyBear::two());
        let e = Dsl::constant_f(BabyBear::from_canonical_u32(8));
        let f = e - d; // 6

        let g = f - c; // 5
        let script = g.express(&mut stack, &bmap);
        stack.number(BabyBear::from_canonical_u32(5u32).as_u32_vec()[0]);
        stack.op_equal();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_script_expression_extsub() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = Dsl::constant_f(EF::one());
        let b = Dsl::constant_f(EF::two());
        let c = b - a; // 1

        let d = Dsl::constant_f(EF::two());
        let e = Dsl::constant_f(EF::from_canonical_u32(8));
        let f = e - d; // 6
        let g = f - c; // 5
        let script = g.express(&mut stack, &bmap);
        stack.bignumber(EF::from_canonical_u32(5u32).as_u32_vec());
        stack.custom(
            u31ext_equalverify::<BabyBear4>(),
            2,
            false,
            0,
            "u31ext_equalverify",
        );
        stack.op_true();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_script_expression_mul() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = Dsl::constant_f(BabyBear::one());
        let b = Dsl::constant_f(BabyBear::two());
        let c = b * a; // 2

        let d = Dsl::constant_f(BabyBear::two());
        let e = Dsl::constant_f(BabyBear::from_canonical_u32(8));
        let f = e * d * BabyBear::one(); // 16
        stack.show_stack();
        let g = f * c; // 32
        let script = g.express(&mut stack, &bmap);
        stack.number(BabyBear::from_canonical_u32(32u32).as_u32_vec()[0]);
        stack.op_equal();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_script_expression_extmul() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = Dsl::constant_f(EF::one());
        let b = Dsl::constant_f(EF::two());
        let c = b * a; // 2

        let d = Dsl::constant_f(EF::two());
        let e = Dsl::constant_f(EF::from_canonical_u32(8));
        let f = e * d; // 16
        let g = f * c; // 32
        g.express(&mut stack, &bmap);

        stack.show_stack();

        stack.bignumber(EF::from_canonical_u32(32u32).as_u32_vec());
        stack.custom(
            u31ext_equalverify::<BabyBear4>(),
            2,
            false,
            0,
            "u31ext_equalverify",
        );
        stack.op_true();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_script_expression_neg() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = Dsl::constant_f(BabyBear::one());
        let b = -a * BabyBear::two();
        let script = b.express(&mut stack, &bmap);
        stack.number(BabyBear::from_canonical_u32(BabyBear::MOD - 2).as_u32_vec()[0]);
        stack.op_equal();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_script_expression_extneg() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = Dsl::constant_f(EF::one());
        let b = -a * EF::two();
        let equal = b.equal_for_f(EF::from_canonical_u32(EF::MOD - 2));
        let script = equal.express(&mut stack, &bmap);
        // let res = stack.run();
        // assert!(res.success);
    }
    #[test]
    fn test_ext_equal() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = Dsl::constant_f(EF::two());
        let exp = a.equal_for_f(EF::two());
        let script = exp.express(&mut stack, &bmap);
        let res = stack.run();
        assert!(res.success);

        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = Dsl::constant_f(BabyBear::two());
        let exp = a.equal_for_f(BabyBear::two());
        let script = exp.express(&mut stack, &bmap);
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_lookup() {
        let vec = vec![
            BabyBear::from_canonical_u32(1 as u32),
            BabyBear::from_canonical_u32(2 as u32),
            BabyBear::from_canonical_u32(3 as u32),
            BabyBear::from_canonical_u32(4 as u32),
            BabyBear::from_canonical_u32(5 as u32),
        ];
        let mut stack = StackTracker::new();
        let bmap = BTreeMap::new();

        let table = Dsl::from_table(&vec);

        let index = 4;

        let m = table.lookup(index, vec.len());

        let script = m.express(&mut stack, &bmap);

        stack.number(5 as u32);

        stack.custom(u31_equalverify(), 2, false, 0, "u31_equalverify");
        stack.op_true();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_reverse_bits_len(){
        let index = 652893;
        let bit_len = 26;
        let mut stack = StackTracker::new();
        let bmap = BTreeMap::new();

        let rev_index = Dsl::<BabyBear>::reverse_bits_len::<BabyBear>(index, bit_len.clone());


        let script = rev_index.express(&mut stack, &bmap);

        let expected = reverse_bits_len(index as usize, bit_len as usize);

        stack.number(expected as u32);

        stack.custom(u31_equalverify(), 2, false, 0, "u31_equalverify");
        stack.op_true();
        let res = stack.run();
        assert!(res.success);
        
    }
}

#[cfg(test)]
mod tests2 {
    use alloc::boxed::Box;
    use alloc::collections::BTreeMap;
    use alloc::sync::Arc;
    use alloc::vec::Vec;
    use core::cell::{self, Cell};
    use std::borrow::Borrow;

    use bitcoin_script_stack::stack::{self, StackTracker, StackVariable};
    use common::{AbstractField, BabyBear, BinomialExtensionField};
    use p3_air::AirBuilder;
    use p3_field::TwoAdicField;
    use p3_matrix::Matrix;
    use primitives::field::BfField;
    use scripts::treepp::*;
    use scripts::u31_lib::{u31ext_equalverify, BabyBear4};

    use super::{Dsl, Expression, Variable, *};
    use crate::opcode::Opcode;
    type EF = BinomialExtensionField<BabyBear, 4>;

    #[test]
    fn test_mul_express_optimize() {
        let a_value = BabyBear::two();
        let b_value = BabyBear::one();
        let c_value = BabyBear::from_canonical_u32(13232);
        let d_value = a_value + b_value;
        let e_value = d_value * c_value;

        let f_value = e_value * d_value;
        let g_value = f_value * e_value;
        let h_value = g_value * e_value;

        let a = Dsl::constant_f(a_value);
        let b = Dsl::constant_f(b_value);

        let c = Dsl::constant_f(c_value);
        let d = a + b;
        let e = d.clone() * c;
        let f = e.clone() * d;
        let g = e.clone() * f;
        let h = g * e.clone();

        let equal = h.equal_for_f(h_value);
        {
            let res = equal.express_without_optimize();
            println!("no optimize script len {:?}", res.0.get_script().len());
            let res = res.0.run();
            assert!(res.success);
        }
        {
            let res = equal.express_with_optimize();
            println!("optimize script len {:?}", res.0.get_script().len());
            let res = res.0.run();
            assert!(res.success);
        }
    }

    /**
     *  a b  
     *   c    d
     *     e
     */

    #[test]
    fn test_add_express_optimize() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = Dsl::constant_f(BabyBear::one());
        // let b = Dsl::constant_f(BabyBear::one());
        let b = a.clone();
        // let c = b.clone();

        let c = a + b;
        let d = c.clone();
        // let res = res1 + c;
        let e = c + d;
        let e_copy = e.clone();

        let e1 = e_copy.clone();

        let e_clone = e.clone();

        let g = e1 + e.clone() + e_clone + e.clone();

        let equal_check = g.equal_for_f(BabyBear::from_canonical_u32(16));
        let vars = equal_check.express(&mut stack, &bmap);
        stack.debug();
        let success = stack.run().success;
        assert!(success);
    }

    #[test]
    fn test_dsl_clone() {
        // let bmap = BTreeMap::new();
        // let mut stack = StackTracker::new();
        let a = Dsl::constant_f(BabyBear::one());
        let b = a.clone() + a.clone();
        let c = b.clone() + b.clone();
        let equal_check = c.equal_for_f(BabyBear::from_canonical_u32(4));
        let res = equal_check.express_with_optimize();
        let success = res.0.run().success;
        println!("optimize script len: {:?}", res.0.get_script().len());
        assert!(success);

        let res = equal_check.express_without_optimize();
        let success = res.0.run().success;
        println!("script len: {:?}", res.0.get_script().len());
        assert!(success);
    }

    #[test]
    fn test_index_to_rou_bug() {
        // todo: the test below happens bug, to fix
        // {
        //     let bmap = BTreeMap::new();
        //     let mut stack = StackTracker::new();
        //     let sub_group_bits = 10u32;
        //     let generator = BabyBear::two_adic_generator(sub_group_bits as usize);
        //     let index = 7u32;
        //     let res = generator.exp_u64(index as u64);

        //     let b = Dsl::<BabyBear>::index_to_rou(index, sub_group_bits);
        //     b.set_debug();
        //     let b_2 = b.clone() * b;
        //     //  let b_2 = b.square();
        //     let res_expr = Dsl::constant_f(res * res);
        //     let equal = b_2.equal_verify(res_expr);
        //     equal.express1(&mut stack, &bmap,false);
        //     stack.op_true();
        //     let res = stack.run();
        //     assert!(res.success);
        //     println!("script_len: {:?}", stack.get_script_len());
        // }

        {
            let bmap = BTreeMap::new();
            let mut stack = StackTracker::new();
            let sub_group_bits = 10u32;
            let generator = BabyBear::two_adic_generator(sub_group_bits as usize);
            let index = 7u32;
            let res = generator.exp_u64(index as u64);

            let b = Dsl::<BabyBear>::index_to_rou(index, sub_group_bits);
            let b_2 = b.clone() * b;
            let res_expr = Dsl::constant_f(res * res);
            let equal = b_2.equal_verify(res_expr);
            equal.express(&mut stack, &bmap);
            stack.op_true();

            let res = stack.run();
            assert!(res.success);
            println!("script_len: {:?}", stack.get_script_len());
        }
    }
}
