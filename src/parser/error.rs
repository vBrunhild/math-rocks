use crate::Error as RollError;


#[derive(thiserror::Error, Debug)]
pub enum ParserError {
    #[error("Invalid token: {0}")]
    Token(char),

    #[error("Invalid number: {0}")]
    Number(#[from] std::num::ParseIntError),

    #[error("Zero value is not accepted")]
    ZeroValue,

    #[error("Invalid identifier: {0}")]
    Identifier(String),

    #[error("Division by zero")]
    ZeroDiv,

    #[error("Invalid roll expression: {0}")]
    RollExpr(String),

    #[error("Roll error - {0}")]
    RollError(#[from] Box<RollError>),

    #[error("Input string is empty")]
    Empty
}

pub type Result<T> = std::result::Result<T, ParserError>;
