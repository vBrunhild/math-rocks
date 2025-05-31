use crate::Error as RollError;


#[derive(Debug, Clone, PartialEq, thiserror::Error)]
pub enum ParserError {
    #[error("At position {0} - {1}")]
    AtPosition(usize, Box<ParserError>),

    #[error("Invalid token: {0}")]
    Token(char),

    #[error("Invalid number: {0}")]
    Number(#[from] std::num::ParseIntError),

    #[error("Zero value is not accepted")]
    ZeroValue,

    #[error("Invalid identifier: {0}")]
    Identifier(String),

    #[error("Invalid roll expression: {0}")]
    RollExpr(String),

    #[error("Roll error - {0}")]
    RollError(#[from] Box<RollError>),

    #[error("Input string is empty")]
    Empty,

    #[error("Parenthesis was not closed")]
    UnclosedParenthesis,

    #[error("Unexpected dice expression, expected literal number, got {0}")]
    UnexpectedDiceExpression(String),

    #[error("Unexpected prefix: {0}")]
    UnexpectedPrefix(String),

    #[error("Unexpected infix: {0}")]
    UnexpectedInfix(String),
}

impl ParserError {
    pub fn err(&self) -> &Self {
        match self {
            ParserError::AtPosition(_, err) => err.as_ref(),
            other => other
        }
    }

    pub fn pos(&self) -> Option<&usize> {
        match self {
            ParserError::AtPosition(position, _) => Some(position),
            _ => None
        }
    }

    pub fn at_pos(self, position: usize) -> Self {
        match self {
            ParserError::AtPosition(_, _) => self,
            other => ParserError::AtPosition(position, Box::new(other))
        }
    }
}

pub type Result<T> = std::result::Result<T, ParserError>;
