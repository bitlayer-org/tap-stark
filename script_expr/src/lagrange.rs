use common::TwoAdicField;
use p3_field::ExtensionField;
use primitives::field::BfField;

use super::Dsl;

pub struct LagrangeSelectorsExpr<F: BfField> {
    pub is_first_row: Dsl<F>,
    pub is_last_row: Dsl<F>,
    pub is_transition: Dsl<F>,
    pub z_h: Dsl<F>,
}

pub fn selectors_at_point_expr<Ext: ExtensionField<Val> + BfField, Val: TwoAdicField + BfField>(
    shift: Val,
    point: Ext,
    log_n: usize,
) -> LagrangeSelectorsExpr<Ext> {
    let unshifted_point = point * shift.inverse();
    let mut unshifted_point_expr = Dsl::<Ext>::default();
    if shift == Val::one() {
        unshifted_point_expr = Dsl::<Ext>::constant_f(unshifted_point);
    } else {
        unshifted_point_expr = Dsl::constant_f(point).mul_base(Dsl::constant_f(shift.inverse()));
    }
    let z_h = unshifted_point.exp_power_of_2(log_n) - Ext::one(); // (x-w^0)...(x-w^n-1)
    let z_h_expr = unshifted_point_expr.clone().exp_constant(2 ^ log_n as u32);
    LagrangeSelectorsExpr {
        is_first_row: Dsl::constant_f(z_h / (unshifted_point - Ext::one())), // hint
        is_last_row: Dsl::constant_f(
            z_h / (unshifted_point - Val::two_adic_generator(log_n).inverse()),
        ), // hint
        is_transition: unshifted_point_expr
            .sub_base(Dsl::constant_f(Val::two_adic_generator(log_n).inverse())),
        z_h: z_h_expr, //
    }
}
