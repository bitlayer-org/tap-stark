use core::marker::PhantomData;

use basic::bf_pcs;
use basic::bf_pcs::{Pcs, PcsExpr};
use basic::challenger::BfGrindingChallenger;
use basic::field::BfField;
use p3_challenger::{CanObserve, CanSample};
use p3_commit::PolynomialSpace;
use p3_field::{ExtensionField, Field};
use script_expr::{BfCheckGrindingChallenger, Dsl, ManagerAssign};

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
    type Pcs: PcsExpr<
        Self::Challenge,
        Self::Challenger,
        Self::ChallengerDsl,
        ManagerAssign,
        DslRep = Dsl<Self::Challenge>,
    >;

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

    type ChallengerDsl: CanObserve<<Self::Pcs as Pcs<Self::Challenge, Self::Challenger>>::Commitment>
        + CanSample<Dsl<Self::Challenge>>
        + BfCheckGrindingChallenger<Self::Challenge>;
    // + CanObserve<<<Self::Pcs as Pcs<Self::Challenge, Self::Challenger>>::Domain as PolynomialSpace>::Val>

    fn pcs(&self) -> &Self::Pcs;
}

#[derive(Debug)]
pub struct StarkConfig<Pcs, Challenge, Challenger, ChallengerDsl> {
    pcs: Pcs,
    _phantom: PhantomData<(Challenge, Challenger, ChallengerDsl)>,
}

impl<Pcs, Challenge, Challenger, ChallengerDsl>
    StarkConfig<Pcs, Challenge, Challenger, ChallengerDsl>
{
    pub const fn new(pcs: Pcs) -> Self {
        Self {
            pcs,
            _phantom: PhantomData,
        }
    }
}

impl<Pcs, Challenge, Challenger, ChallengerDsl> StarkGenericConfig
    for StarkConfig<Pcs, Challenge, Challenger, ChallengerDsl>
where
    Challenge: ExtensionField<<Pcs::Domain as PolynomialSpace>::Val> + BfField,
    Pcs: PcsExpr<Challenge, Challenger, ChallengerDsl, ManagerAssign, DslRep = Dsl<Challenge>>,
    Challenger: BfGrindingChallenger
        + CanObserve<<Pcs as bf_pcs::Pcs<Challenge, Challenger>>::Commitment>
        + CanSample<Challenge>,
    ChallengerDsl: CanObserve<<Pcs as bf_pcs::Pcs<Challenge, Challenger>>::Commitment>
        + CanSample<Dsl<Challenge>>
        + BfCheckGrindingChallenger<Challenge>,
{
    type Pcs = Pcs;
    type Challenge = Challenge;
    type Challenger = Challenger;
    type ChallengerDsl = ChallengerDsl;

    fn pcs(&self) -> &Self::Pcs {
        &self.pcs
    }
}
