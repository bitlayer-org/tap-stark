use core::marker::PhantomData;

use p3_challenger::{CanObserve, CanSample, FieldChallenger};
use p3_commit::PolynomialSpace;
use p3_field::{ExtensionField, Field};
use primitives::bf_pcs;
use primitives::bf_pcs::{Pcs, PcsExpr};
use primitives::challenger::BfGrindingChallenger;
use primitives::field::BfField;
use script_expr::{Dsl, ManagerAssign};

pub type PcsError<SC> = <<SC as StarkGenericConfig>::Pcs as Pcs<
    <SC as StarkGenericConfig>::Challenge,
    <SC as StarkGenericConfig>::Challenger,
>>::Error;

pub type Domain<SC> = <<SC as StarkGenericConfig>::Pcs as Pcs<
    <SC as StarkGenericConfig>::Challenge,
    <SC as StarkGenericConfig>::Challenger,
>>::Domain;

//TODO: Val: p3_field::Field, we need Val: BfField?
pub type Val<SC> = <<<SC as StarkGenericConfig>::Pcs as Pcs<
    <SC as StarkGenericConfig>::Challenge,
    <SC as StarkGenericConfig>::Challenger,
>>::Domain as PolynomialSpace>::Val;

pub type PackedVal<SC> = <Val<SC> as Field>::Packing;

pub type PackedChallenge<SC> =
    <<SC as StarkGenericConfig>::Challenge as ExtensionField<Val<SC>>>::ExtensionPacking;

pub trait StarkGenericConfig {
    /// The PCS used to commit to trace polynomials.
    type Pcs: PcsExpr<Self::Challenge, Self::Challenger, ManagerAssign>;

    /// The field from which most random challenges are drawn.
    type Challenge: ExtensionField<Val<Self>> + BfField;

    /// The challenger (Fiat-Shamir) implementation used.
    // type Challenger: FieldChallenger<Val<Self>>
    //     + CanObserve<<Self::Pcs as Pcs<Self::Challenge, Self::Challenger>>::Commitment>
    //     + CanSample<Self::Challenge>;

    // TODO: we need a field challenger too?
    type Challenger: BfGrindingChallenger
        + CanObserve<<Self::Pcs as Pcs<Self::Challenge, Self::Challenger>>::Commitment>
        + CanSample<Self::Challenge>;
    // + CanObserve<<<Self::Pcs as Pcs<Self::Challenge, Self::Challenger>>::Domain as PolynomialSpace>::Val>

    fn pcs(&self) -> &Self::Pcs;
}

#[derive(Debug)]
pub struct StarkConfig<Pcs, Challenge, Challenger> {
    pcs: Pcs,
    _phantom: PhantomData<(Challenge, Challenger)>,
}

impl<Pcs, Challenge, Challenger> StarkConfig<Pcs, Challenge, Challenger> {
    pub const fn new(pcs: Pcs) -> Self {
        Self {
            pcs,
            _phantom: PhantomData,
        }
    }
}

impl<Pcs, Challenge, Challenger> StarkGenericConfig for StarkConfig<Pcs, Challenge, Challenger>
where
    Challenge: ExtensionField<<Pcs::Domain as PolynomialSpace>::Val> + BfField,
    Pcs: PcsExpr<Challenge, Challenger, ManagerAssign>,
    Challenger: BfGrindingChallenger
        + CanObserve<<Pcs as bf_pcs::Pcs<Challenge, Challenger>>::Commitment>
        + CanSample<Challenge>,
{
    type Pcs = Pcs;
    type Challenge = Challenge;
    type Challenger = Challenger;

    fn pcs(&self) -> &Self::Pcs {
        &self.pcs
    }
}
