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
    InvalidOpenedValue,
    IndexWithEmptyLeaf(u32, u32),
}

impl From<TaprootBuilderError> for BfError {
    fn from(error: TaprootBuilderError) -> Self {
        BfError::TaprootBuilderError(error)
    }
}
