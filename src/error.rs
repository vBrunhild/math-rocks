use crate::parser::ParserError as ParserError;


#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("Invalid roll: {0}")]
    InvalidRoll(String),

    #[error("Zero value not allowed")]
    ZeroValue,

    #[error("Failed to convert to NonZero: {0}")]
    InvalidNonZero(String),

    #[error("Parser error - {0}")]
    ParserError(#[from] ParserError)
}
