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

#[cfg(test)]
mod test {
    use super::ParserError;
    use proptest::prelude::*;

    fn err_strategy() -> impl Strategy<Value = ParserError> {
        let base_errors = prop_oneof![
            Just(ParserError::Token('a')),
            Just(ParserError::ZeroValue),
            Just(ParserError::Identifier("id".into())),
            Just(ParserError::RollExpr("expr".into())),
            Just(ParserError::Empty),
            Just(ParserError::UnclosedParenthesis),
            Just(ParserError::UnexpectedDiceExpression("dice".into())),
            Just(ParserError::UnexpectedPrefix("prefix".into())),
            Just(ParserError::UnexpectedInfix("infix".into())),
        ];
        
        base_errors.prop_recursive(1, 16, 1, |inner| {
                prop_oneof![
                    inner.clone(),
                    (0usize..=100, inner).prop_map(|(position, err)| err.at_pos(position))
                ]
            }
        )
    }

    proptest! {
        #[test]
        fn test_parser_error_methods(err in err_strategy(), pos in 0usize..=100) {
            match &err {
                ParserError::AtPosition(_, boxed_err) => {
                    prop_assert!(std::ptr::eq(err.err(), boxed_err.as_ref()));
                    prop_assert!(err.pos().is_some());
                },
                other => {
                    prop_assert!(std::ptr::eq(err.err(), other));
                    prop_assert!(other.pos().is_none());
                }
            };

            let err_at_pos = err.clone().at_pos(pos);

            match err {
                ParserError::AtPosition(_, _) => prop_assert_eq!(err, err_at_pos),
                _ => prop_assert!(matches!(
                    err_at_pos,
                    ParserError::AtPosition(err_pos, _) if err_pos == pos
                ))
            };
        }
    }
}
