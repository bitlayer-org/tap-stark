use bitcoin::taproot::TaprootBuilderError;
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum BfError {
    TaprootBuilderError(TaprootBuilderError),
    TaprootError,
    TapLeafError,
    TapTreeError,
    EvaluationLeafError,
    ExecuteScriptError,
    InvalidMerkleProof,
    IndexWithEmptyLeaf(u32, u32),
}

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

impl From<TaprootBuilderError> for BfError {
    fn from(error: TaprootBuilderError) -> Self {
        BfError::TaprootBuilderError(error)
    }
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
