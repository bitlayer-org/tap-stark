use bitcoin::taproot::TaprootBuilderError;
use primitives::mmcs::error::BfError;
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum SVError {
    VerifyCalNegXScriptError,
    VerifyIndexToROUScriptError,
    VerifyReductionScriptError,
    VerifyFoldingScriptError,
    VerifySquareFScriptError,
    VerifyCommitedPointError,
    VerifyReverseIndexScriptError,
    InvalidWitness,
}

impl<M> From<BfError> for FriError<M> {
    fn from(error: BfError) -> Self {
        FriError::<M>::BFError(error)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum FriError<CommitMmcsErr> {
    InvalidProofShape,
    CommitPhaseMmcsError(CommitMmcsErr),
    ScriptVerifierError(SVError),
    BFError(BfError),
    FinalPolyMismatch,
    InvalidPowWitness,
}
