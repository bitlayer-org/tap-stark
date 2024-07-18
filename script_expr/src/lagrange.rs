use common::TwoAdicField;
use p3_field::ExtensionField;
use primitives::field::BfField;

use super::FieldScriptExpression;

pub struct LagrangeSelectorsExpr<F: BfField> {
    pub is_first_row: FieldScriptExpression<F>,
    pub is_last_row: FieldScriptExpression<F>,
    pub is_transition: FieldScriptExpression<F>,
    pub z_h: FieldScriptExpression<F>,
}

pub fn selectors_at_point_expr<
    Ext: ExtensionField<Val> + BfField,
    Val: TwoAdicField + BfField,
>(
    shift: Val,
    point: Ext,
    log_n: usize,
) -> LagrangeSelectorsExpr<Ext> {
    let unshifted_point = point * shift.inverse();
    let mut unshifted_point_expr = FieldScriptExpression::<Ext>::default();
    if shift == Val::one() {
        unshifted_point_expr = FieldScriptExpression::<Ext>::from(unshifted_point);
    } else {
        unshifted_point_expr = FieldScriptExpression::from(point)
            .mul_base(FieldScriptExpression::from(shift.inverse()));
    }
    let z_h = unshifted_point.exp_power_of_2(log_n) - Ext::one(); // (x-w^0)...(x-w^n-1)
    let z_h_expr = unshifted_point_expr.exp_constant(2 ^ log_n as u32);
    LagrangeSelectorsExpr {
        is_first_row: (z_h / (unshifted_point - Ext::one())).into(), // hint
        is_last_row: (z_h / (unshifted_point - Val::two_adic_generator(log_n).inverse())).into(), // hint
        is_transition: unshifted_point_expr
            .sub_base(Val::two_adic_generator(log_n).inverse().into()),
        z_h: z_h_expr, //
    }
}
