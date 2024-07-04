use alloc::collections::BTreeMap;
use alloc::rc::Rc;
use alloc::vec::Vec;
use alloc::{format, vec};
use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use bitcoin::hashes::cmp;
use bitcoin_script_stack::stack::{StackTracker, StackVariable};
use common::{AbstractField, AsU32Vec};
use p3_field::Field;
use primitives::field::BfField;
use script_primitives::*;
use scripts::treepp::*;
use scripts::u31_lib::{
    u31_add, u31_double, u31_mul, u31_neg, u31_sub, u31_sub_u31ext, u31_to_u31ext, u31ext_add,
    u31ext_add_u31, u31ext_double, u31ext_equalverify, u31ext_mul, u31ext_mul_u31,
    u31ext_mul_u31_by_constant, u31ext_neg, u31ext_sub, u31ext_sub_u31, BabyBear4, BabyBearU31,
};

use crate::symbolic_variable::SymbolicVariable;
use crate::Entry;
use crate::SymbolicExpression::{self, *};

pub mod script_primitives {
    use bitcoin_script_stack::stack::{StackTracker, StackVariable};
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Variable {
    row_index: usize,
    column_index: usize,
}

impl<F: Field> From<SymbolicVariable<F>> for Variable {
    fn from(value: SymbolicVariable<F>) -> Self {
        match value.entry {
            Entry::Main { offset } => Variable {
                row_index: value.index,
                column_index: offset,
            },
            Entry::Permutation { offset } => Variable {
                row_index: value.index,
                column_index: offset,
            },
            Entry::Preprocessed { offset } => Variable {
                row_index: value.index,
                column_index: offset,
            },
            _ => panic!("error type"),
        }
    }
}

impl<F: Field> From<&SymbolicVariable<F>> for Variable {
    fn from(value: &SymbolicVariable<F>) -> Self {
        match value.entry {
            Entry::Main { offset } => Variable {
                row_index: value.index,
                column_index: offset,
            },
            Entry::Permutation { offset } => Variable {
                row_index: value.index,
                column_index: offset,
            },
            Entry::Preprocessed { offset } => Variable {
                row_index: value.index,
                column_index: offset,
            },
            _ => panic!("error type"),
        }
    }
}

#[derive(Clone, Debug)]
pub enum ScriptExpression<F: BfField> {
    InputVariable {
        sv: Variable,
    },
    IsFirstRow,
    IsLastRow,
    IsTransition,
    Constant(F),
    Add {
        x: Rc<Self>,
        y: Rc<Self>,
        script: Script,
        var: StackVariable,
    },
    Sub {
        x: Rc<Self>,
        y: Rc<Self>,
        script: Script,
        var: StackVariable,
    },
    Neg {
        x: Rc<Self>,
        script: Script,
        var: StackVariable,
    },
    Mul {
        x: Rc<Self>,
        y: Rc<Self>,
        script: Script,
        var: StackVariable,
    },
}

impl<F: BfField> From<&SymbolicExpression<F>> for ScriptExpression<F> {
    fn from(value: &SymbolicExpression<F>) -> Self {
        match value {
            SymbolicExpression::Variable(v) => ScriptExpression::InputVariable {
                sv: v.into(),
                // value: F::default(),
                // var: StackVariable::null(),
            },
            SymbolicExpression::IsFirstRow => ScriptExpression::IsFirstRow,
            SymbolicExpression::IsLastRow => ScriptExpression::IsLastRow,
            SymbolicExpression::IsTransition => ScriptExpression::IsTransition,
            SymbolicExpression::Constant(f) => ScriptExpression::Constant(f.clone()),
            SymbolicExpression::Add { x, y, .. } => ScriptExpression::Add {
                x: Rc::new(ScriptExpression::from(&*x.clone())),
                y: Rc::new(ScriptExpression::from(&*y.clone())),
                script: Script::default(),
                var: StackVariable::null(),
            },
            SymbolicExpression::Sub { x, y, .. } => ScriptExpression::Sub {
                x: Rc::new(ScriptExpression::from(&*x.clone())),
                y: Rc::new(ScriptExpression::from(&*y.clone())),
                script: Script::default(),
                var: StackVariable::null(),
            },
            SymbolicExpression::Neg { x, .. } => ScriptExpression::Neg {
                x: Rc::new(ScriptExpression::from(&*x.clone())),
                script: Script::default(),
                var: StackVariable::null(),
            },
            SymbolicExpression::Mul { x, y, .. } => ScriptExpression::Mul {
                x: Rc::new(ScriptExpression::from(&*x.clone())),
                y: Rc::new(ScriptExpression::from(&*y.clone())),
                script: Script::default(),
                var: StackVariable::null(),
            },
        }
    }
}

impl<F: BfField> ScriptExpression<F> {
    fn express_to_script(
        &self,
        stack: &mut StackTracker,
        input_variables: &BTreeMap<&Variable, StackVariable>,
    ) -> Script {
        // let mut variable_sequence: Vec<&Variable> = Vec::new();
        // let mut var_map = BTreeMap::<&Variable,StackVariable>::new();
        match self {
            ScriptExpression::InputVariable { sv } => {
                let var = input_variables.get(sv).unwrap();
                stack.copy_var(var.clone());
                stack.debug();
            }
            ScriptExpression::IsFirstRow => {
                stack.op_true();
            }
            ScriptExpression::IsLastRow => {
                stack.op_true();
            }
            ScriptExpression::IsTransition => {
                stack.op_true();
            }
            ScriptExpression::Constant(f) => {
                let v = f.as_u32_vec();
                stack.bignumber(v);
            }
            ScriptExpression::Add {
                x,
                y,
                script,
                mut var,
            } => {
                x.express_to_script(stack, input_variables);
                y.express_to_script(stack, input_variables);
                let vars = stack
                    .custom1(
                        script! {
                            if F::U32_SIZE == 1{
                                {u31_add::<BabyBearU31>()}
                            }else{
                                {u31ext_add::<BabyBear4>()}
                            }
                        },
                        2,
                        1,
                        0,
                        F::U32_SIZE as u32,
                        "ScriptExpression_ADD",
                    )
                    .unwrap();
                var = vars[0];
                assert_eq!(var.size(), F::U32_SIZE as u32);
            }
            ScriptExpression::Sub {
                x,
                y,
                script,
                mut var,
            } => {
                x.express_to_script(stack, input_variables);
                y.express_to_script(stack, input_variables);
                let vars = stack
                    .custom1(
                        script! {
                            if F::U32_SIZE == 1{
                                {u31_sub::<BabyBearU31>()}
                            }else{
                                {u31ext_sub::<BabyBear4>()}
                            }
                        },
                        2,
                        1,
                        0,
                        F::U32_SIZE as u32,
                        "ScriptExpression_SUB",
                    )
                    .unwrap();
                var = vars[0];
                assert_eq!(var.size(), F::U32_SIZE as u32);
            }

            ScriptExpression::Neg { x, script, mut var } => {
                x.express_to_script(stack, input_variables);
                let vars = stack
                    .custom1(
                        script! {
                            if F::U32_SIZE == 1{
                                {u31_neg::<BabyBearU31>()}
                            }else{
                                {u31ext_neg::<BabyBear4>()}
                            }
                        },
                        1,
                        1,
                        0,
                        F::U32_SIZE as u32,
                        "ScriptExpression_NEG",
                    )
                    .unwrap();
                var = vars[0];
                assert_eq!(var.size(), F::U32_SIZE as u32);
            }
            ScriptExpression::Mul {
                x,
                y,
                script,
                mut var,
            } => {
                x.express_to_script(stack, input_variables);
                y.express_to_script(stack, input_variables);
                let vars = stack
                    .custom1(
                        script! {
                            if F::U32_SIZE == 1{
                                {u31_mul::<BabyBearU31>()}
                            }else{
                                {u31ext_mul::<BabyBear4>()}
                            }
                        },
                        2,
                        1,
                        0,
                        F::U32_SIZE as u32,
                        "ScriptExpression_MUL",
                    )
                    .unwrap();
                var = vars[0];
                assert_eq!(var.size(), F::U32_SIZE as u32);
            }
        };

        stack.get_script()
    }
}

impl<F: BfField> Default for ScriptExpression<F> {
    fn default() -> Self {
        Self::Constant(F::zero())
    }
}

impl<F: BfField> From<F> for ScriptExpression<F> {
    fn from(value: F) -> Self {
        Self::Constant(value)
    }
}

impl<F: BfField> AbstractField for ScriptExpression<F> {
    type F = F;

    fn zero() -> Self {
        Self::Constant(F::zero())
    }
    fn one() -> Self {
        Self::Constant(F::one())
    }
    fn two() -> Self {
        Self::Constant(F::two())
    }
    fn neg_one() -> Self {
        Self::Constant(F::neg_one())
    }

    #[inline]
    fn from_f(f: Self::F) -> Self {
        f.into()
    }

    fn from_bool(b: bool) -> Self {
        Self::Constant(F::from_bool(b))
    }

    fn from_canonical_u8(n: u8) -> Self {
        Self::Constant(F::from_canonical_u8(n))
    }

    fn from_canonical_u16(n: u16) -> Self {
        Self::Constant(F::from_canonical_u16(n))
    }

    fn from_canonical_u32(n: u32) -> Self {
        Self::Constant(F::from_canonical_u32(n))
    }

    fn from_canonical_u64(n: u64) -> Self {
        Self::Constant(F::from_canonical_u64(n))
    }

    fn from_canonical_usize(n: usize) -> Self {
        Self::Constant(F::from_canonical_usize(n))
    }

    fn from_wrapped_u32(n: u32) -> Self {
        Self::Constant(F::from_wrapped_u32(n))
    }

    fn from_wrapped_u64(n: u64) -> Self {
        Self::Constant(F::from_wrapped_u64(n))
    }

    fn generator() -> Self {
        Self::Constant(F::generator())
    }
}

impl<F: BfField> Add for ScriptExpression<F> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Self::Add {
            x: Rc::new(self),
            y: Rc::new(rhs),
            script: Script::default(),
            var: StackVariable::null(),
        }
    }
}

impl<F: BfField> Add<F> for ScriptExpression<F> {
    type Output = Self;

    fn add(self, rhs: F) -> Self {
        self + Self::from(rhs)
    }
}

impl<F: BfField> AddAssign for ScriptExpression<F> {
    fn add_assign(&mut self, rhs: Self) {
        *self = self.clone() + rhs;
    }
}

impl<F: BfField> AddAssign<F> for ScriptExpression<F> {
    fn add_assign(&mut self, rhs: F) {
        *self += Self::from(rhs);
    }
}

impl<F: BfField> Sum for ScriptExpression<F> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|x, y| x + y).unwrap_or(Self::zero())
    }
}

impl<F: BfField> Sum<F> for ScriptExpression<F> {
    fn sum<I: Iterator<Item = F>>(iter: I) -> Self {
        iter.map(|x| Self::from(x)).sum()
    }
}

impl<F: BfField> Sub for ScriptExpression<F> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        Self::Sub {
            x: Rc::new(self),
            y: Rc::new(rhs),
            script: Script::default(),
            var: StackVariable::null(),
        }
    }
}

impl<F: BfField> Sub<F> for ScriptExpression<F> {
    type Output = Self;

    fn sub(self, rhs: F) -> Self {
        self - Self::from(rhs)
    }
}

impl<F: BfField> SubAssign for ScriptExpression<F> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = self.clone() - rhs;
    }
}

impl<F: BfField> SubAssign<F> for ScriptExpression<F> {
    fn sub_assign(&mut self, rhs: F) {
        *self -= Self::from(rhs);
    }
}

impl<F: BfField> Neg for ScriptExpression<F> {
    type Output = Self;

    fn neg(self) -> Self {
        Self::Neg {
            x: Rc::new(self),
            script: Script::default(),
            var: StackVariable::null(),
        }
    }
}

impl<F: BfField> Mul for ScriptExpression<F> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        #[allow(clippy::suspicious_arithmetic_impl)]
        Self::Mul {
            x: Rc::new(self),
            y: Rc::new(rhs),
            script: Script::default(),
            var: StackVariable::null(),
        }
    }
}

impl<F: BfField> Mul<F> for ScriptExpression<F> {
    type Output = Self;

    fn mul(self, rhs: F) -> Self {
        self * Self::from(rhs)
    }
}

impl<F: BfField> MulAssign for ScriptExpression<F> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.clone() * rhs;
    }
}

impl<F: BfField> MulAssign<F> for ScriptExpression<F> {
    fn mul_assign(&mut self, rhs: F) {
        *self *= Self::from(rhs);
    }
}

impl<F: BfField> Product for ScriptExpression<F> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|x, y| x * y).unwrap_or(Self::one())
    }
}

impl<F: BfField> Product<F> for ScriptExpression<F> {
    fn product<I: Iterator<Item = F>>(iter: I) -> Self {
        iter.map(|x| Self::from(x)).product()
    }
}

#[cfg(test)]
mod tests {
    use alloc::collections::BTreeMap;
    use alloc::vec::Vec;

    use bitcoin_script_stack::stack::{self, StackTracker};
    use common::{AbstractField, BabyBear, BinomialExtensionField};
    use p3_air::AirBuilder;
    use p3_matrix::Matrix;
    use primitives::field::BfField;
    use scripts::treepp::*;
    use scripts::u31_lib::{u31ext_equalverify, BabyBear4, BabyBearU31};

    use super::{ScriptExpression, Variable};
    use crate::{prove, verify, StarkConfig, SymbolicAirBuilder, SymbolicExpression};
    type EF = BinomialExtensionField<BabyBear, 4>;

    #[test]
    fn test_symbolic_expr_constraints() {
        let air_width: usize = 2;
        let mut builder = SymbolicAirBuilder::<BabyBear>::new(0, air_width, 0);
        let main_values = builder.main();
        let (local, next) = (main_values.row_slice(0), main_values.row_slice(1));
        let mut when_transition = builder.when_transition();
        // a' <- b
        when_transition.assert_eq(local[0], local[1]);

        // b' <- a + b
        when_transition.assert_eq(local[0] + local[1], next[1]);

        let cs = builder.constraints();
        let script_exp: Vec<ScriptExpression<BabyBear>> =
            cs.iter().map(|cons| ScriptExpression::from(cons)).collect();
    }

    #[test]
    fn test_script_expression_add() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = ScriptExpression::from(BabyBear::one());
        let b = ScriptExpression::from(BabyBear::two());
        let c = a + b;

        let d = ScriptExpression::from(BabyBear::two());
        let e = ScriptExpression::from(BabyBear::two());
        let f = d + e;

        let g = c + f; // 4 + 3 = 7
        let script = g.express_to_script(&mut stack, &bmap);
        stack.number(BabyBear::from_canonical_u32(7u32).as_u32_vec()[0]);
        stack.op_equal();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_ext_constant() {
        let mut stack = StackTracker::new();
        let bmap = BTreeMap::new();
        let a = ScriptExpression::from(EF::one());
        a.express_to_script(&mut stack, &bmap);
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
        let var1 = Variable {
            row_index: 0,
            column_index: 0,
        };
        let var2 = Variable {
            row_index: 0,
            column_index: 1,
        };
        let var3 = Variable {
            row_index: 1,
            column_index: 0,
        };
        let var4 = Variable {
            row_index: 1,
            column_index: 1,
        };

        let mut stack = StackTracker::new();
        let mut bmap = BTreeMap::new();
        bmap.insert(
            &var1,
            stack.var(
                1,
                script! { {BabyBear::from_canonical_u32(1u32).as_u32_vec()[0]}},
                "input 1",
            ),
        );
        bmap.insert(
            &var2,
            stack.var(
                1,
                script! { {BabyBear::from_canonical_u32(2u32).as_u32_vec()[0]}},
                "input 2",
            ),
        );
        bmap.insert(
            &var3,
            stack.var(
                1,
                script! {{BabyBear::from_canonical_u32(3u32).as_u32_vec()[0]}},
                "input 3",
            ),
        );
        bmap.insert(
            &var4,
            stack.var(
                1,
                script! {{BabyBear::from_canonical_u32(4u32).as_u32_vec()[0]}},
                "input 4",
            ),
        );

        let var1_wrap = ScriptExpression::InputVariable { sv: var1 };
        let var2_wrap = ScriptExpression::<BabyBear>::InputVariable { sv: var2 };
        let var3_wrap = ScriptExpression::InputVariable { sv: var3 };
        let var4_wrap = ScriptExpression::<BabyBear>::InputVariable { sv: var4 };
        let res1 = var1_wrap + var2_wrap;
        let res2 = var3_wrap + var4_wrap;

        let res = res1 + res2;
        res.express_to_script(&mut stack, &bmap);

        stack.number(BabyBear::from_canonical_u32(10u32).as_u32_vec()[0]);
        stack.op_equalverify();

        stack.drop(*bmap.get(&var4).unwrap());
        stack.drop(*bmap.get(&var3).unwrap());
        stack.drop(*bmap.get(&var2).unwrap());
        stack.drop(*bmap.get(&var1).unwrap());
        stack.op_true();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_script_expression_extadd() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = ScriptExpression::from(EF::one());
        let b = ScriptExpression::from(EF::two());
        let c = a + b;

        let script = c.express_to_script(&mut stack, &bmap);
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
        let a = ScriptExpression::from(BabyBear::one());
        let b = ScriptExpression::from(BabyBear::two());
        let c = b - a; // 1

        let d = ScriptExpression::from(BabyBear::two());
        let e = ScriptExpression::from(BabyBear::from_canonical_u32(8));
        let f = e - d; // 6

        let g = f - c; // 5
        let script = g.express_to_script(&mut stack, &bmap);
        stack.number(BabyBear::from_canonical_u32(5u32).as_u32_vec()[0]);
        stack.op_equal();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_script_expression_extsub() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = ScriptExpression::from(EF::one());
        let b = ScriptExpression::from(EF::two());
        let c = b - a; // 1

        let d = ScriptExpression::from(EF::two());
        let e = ScriptExpression::from(EF::from_canonical_u32(8));
        let f = e - d; // 6

        let g = f - c; // 5
        let script = g.express_to_script(&mut stack, &bmap);
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
        let a = ScriptExpression::from(BabyBear::one());
        let b = ScriptExpression::from(BabyBear::two());
        let c = b * a; // 2

        let d = ScriptExpression::from(BabyBear::two());
        let e = ScriptExpression::from(BabyBear::from_canonical_u32(8));
        let f = e * d * BabyBear::one(); // 16
        stack.show_stack();
        let g = f * c; // 32
        let script = g.express_to_script(&mut stack, &bmap);
        stack.number(BabyBear::from_canonical_u32(32u32).as_u32_vec()[0]);
        stack.op_equal();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_script_expression_extmul() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = ScriptExpression::from(EF::one());
        let b = ScriptExpression::from(EF::two());
        let c = b * a; // 2

        let d = ScriptExpression::from(EF::two());
        let e = ScriptExpression::from(EF::from_canonical_u32(8));
        let f = e * d; // 16
        let g = f * c; // 32
        let script = g.express_to_script(&mut stack, &bmap);

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
        let a = ScriptExpression::from(BabyBear::one());
        let b = -a * BabyBear::two();
        let script = b.express_to_script(&mut stack, &bmap);
        stack.number(BabyBear::from_canonical_u32(BabyBear::MOD - 2).as_u32_vec()[0]);
        stack.op_equal();
        let res = stack.run();
        assert!(res.success);
    }

    #[test]
    fn test_script_expression_extneg() {
        let bmap = BTreeMap::new();
        let mut stack = StackTracker::new();
        let a = ScriptExpression::from(EF::one());
        let b = -a * EF::two();
        let script = b.express_to_script(&mut stack, &bmap);
        stack.bignumber(EF::from_canonical_u32(EF::MOD - 2).as_u32_vec());
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
}
