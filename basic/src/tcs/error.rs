use bitcoin::taproot::TaprootBuilderError;
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TCSError {
    TaprootBuilderError(TaprootBuilderError),
}

impl From<TaprootBuilderError> for TCSError {
    fn from(error: TaprootBuilderError) -> Self {
        TCSError::TaprootBuilderError(error)
    }
}
