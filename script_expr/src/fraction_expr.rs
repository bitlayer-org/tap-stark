use std::ops::Add;
use std::sync::Arc;

use basic::field::BfField;

use super::FieldScriptExpression;
use crate::Expression;

pub struct Fraction<F: BfField> {
    numerator: FieldScriptExpression<F>,
    denominator: FieldScriptExpression<F>,
}

impl<F: BfField> Fraction<F> {
    pub(crate) fn new(
        numerator: FieldScriptExpression<F>,
        denominator: FieldScriptExpression<F>,
    ) -> Self {
        Self {
            numerator,
            denominator,
        }
    }

    fn get_numerator(&self) -> FieldScriptExpression<F> {
        self.numerator.clone()
    }

    fn get_demonitor(&self) -> FieldScriptExpression<F> {
        self.denominator.clone()
    }

    fn mul_expr(self, other: FieldScriptExpression<F>) -> Fraction<F> {
        Fraction::new(self.numerator * other, self.denominator)
    }

    fn mul_fraction(self, other: Self) -> Fraction<F> {
        Fraction::new(
            self.numerator * other.numerator,
            self.denominator * other.denominator,
        )
    }

    fn add_expr(self, other: FieldScriptExpression<F>) -> Fraction<F> {
        Fraction::new(
            self.numerator + other * self.denominator.clone(),
            self.denominator,
        )
    }

    fn add_fraction(self, other: Self) -> Fraction<F> {
        Fraction::new(
            self.numerator * other.denominator.clone() + other.numerator * self.denominator.clone(),
            self.denominator * other.denominator,
        )
    }

    fn sub_expr(self, other: FieldScriptExpression<F>) -> Fraction<F> {
        Fraction::new(
            self.numerator - other * self.denominator.clone(),
            self.denominator,
        )
    }

    fn sub_fraction(self, other: Self) -> Fraction<F> {
        Fraction::new(
            self.numerator * other.denominator.clone() - other.numerator * self.denominator.clone(),
            self.denominator * other.denominator,
        )
    }
}
