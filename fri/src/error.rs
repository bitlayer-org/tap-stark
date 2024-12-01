use basic::mmcs::error::BfError;
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

impl<M, I> From<BfError> for FriError<M, I> {
    fn from(error: BfError) -> Self {
        FriError::<M, I>::BFError(error)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum FriError<CommitMmcsErr, InputErr> {
    InputError(InputErr),
    InvalidProofShape,
    CommitPhaseMmcsError(CommitMmcsErr),
    ScriptVerifierError(SVError),
    BFError(BfError),
    FinalPolyMismatch,
    InvalidPowWitness,
}
