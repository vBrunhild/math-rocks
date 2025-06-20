use crate::Error as RollError;
use std::num::ParseIntError;


/// Represents the various errors that can occur while parsing a dice notation string.
///
/// Errors can range from lexical issues (invalid tokens) to syntactic problems
/// (unexpected expressions, unclosed parentheses) and semantic issues within
/// the parser's understanding of dice expressions.
#[derive(Debug, Clone, PartialEq, thiserror::Error)]
pub enum ParserError {
    /// Wraps another `ParserError` with positional information, indicating
    /// where in the input string the original error occurred.
    ///
    /// The `usize` is the 0-indexed position (character offset) in the input string.
    /// The `Box<ParserError>` contains the underlying error.
    #[error("At position {0} - {1}")]
    AtPosition(usize, Box<ParserError>),

    /// An invalid character was encountered that does not form part of a recognized token.
    /// The `char` is the unexpected character.
    #[error("Invalid token: {0}")]
    Token(char),

    /// Failed to parse a sequence of digits into a number.
    ///
    /// This typically occurs if a number literal is malformed
    /// (e.g., too large, contains non-digit characters where not expected).
    #[error("Invalid number: {0}")]
    Number(#[from] ParseIntError),

    /// A zero value was encountered in a context where it's not permitted by the parser
    /// or underlying roll logic during parsing.
    /// 
    /// Values like "000001" should be parsed to 1u16, but values like "0" or "000000"
    /// will return this error. 
    #[error("Zero value is not accepted")]
    ZeroValue,

    /// An unrecognized or malformed identifier was found.
    #[error("Invalid identifier: {0}")]
    Identifier(String),

    /// Encapsulates an error originating from the core dice rolling logic (`RollError`)
    /// that was encountered during a parsing step that might involve partial evaluation
    /// or validation of roll parameters.
    #[error("Roll error - {0}")]
    RollError(#[from] RollError),

    /// The input string provided to the parser was empty.
    #[error("Input string is empty")]
    Empty,

    /// A left parenthesis `(` was encountered without a matching right parenthesis `)`.
    #[error("Parenthesis was not closed")]
    UnclosedParenthesis,

    /// A dice 'd' notation was found, but the expression preceding it (for the count)
    /// or following it (for the size) was not a literal number as expected.
    #[error("Unexpected dice expression, expected literal number, got {0}")]
    UnexpectedDiceExpression(String),

    /// An unexpected token was found at the beginning of an expression or sub-expression
    /// where a prefix operator (like unary minus) or a primary expression (like a number
    /// or opening parenthesis) was expected.
    #[error("Unexpected prefix: {0}")]
    UnexpectedPrefix(String),

    /// An unexpected token was found where an infix operator (like `+`, `-`, `*`, `/`, `d`)
    /// was expected, or the token found is not a valid infix operator in the current context.
    #[error("Unexpected infix: {0}")]
    UnexpectedInfix(String),
}

impl ParserError {
    /// Retrieves a reference to the underlying `ParserError` if this error is
    /// an `AtPosition` variant; otherwise, returns a reference to itself.
    ///
    /// This is useful for accessing the "actual" error type when it might be
    /// wrapped with positional information.
    ///
    /// # Examples
    /// ```
    /// use math_rocks::ParserError;
    ///
    /// let base_err = ParserError::Empty;
    /// let wrapped_err = ParserError::AtPosition(5, Box::new(base_err.clone()));
    ///
    /// assert_eq!(wrapped_err.err(), &base_err); // Gets the inner Empty error
    /// assert_eq!(base_err.err(), &base_err);    // Returns itself
    /// ```
    pub fn err(&self) -> &Self {
        match self {
            ParserError::AtPosition(_, err) => err.as_ref(),
            other => other
        }
    }

    /// Returns the position of the error if this is an `AtPosition` variant.
    ///
    /// # Examples
    /// ```
    /// use math_rocks::ParserError;
    ///
    /// let base_err = ParserError::UnclosedParenthesis;
    /// let wrapped_err = ParserError::AtPosition(10, Box::new(base_err.clone()));
    ///
    /// assert_eq!(wrapped_err.pos(), Some(&10));
    /// assert_eq!(base_err.pos(), None);
    /// ```
    pub fn pos(&self) -> Option<&usize> {
        match self {
            ParserError::AtPosition(position, _) => Some(position),
            _ => None
        }
    }

    /// Wraps the current error with positional information, creating an `AtPosition` variant.
    ///
    /// If the current error is already an `AtPosition` variant, this method returns
    /// it unchanged (i.e., it does not double-wrap positions). Otherwise, it creates
    /// a new `AtPosition` error boxing the current error.
    ///
    /// # Arguments
    /// * `position`: The 0-indexed character offset in the input string where the error occurred.
    ///
    /// # Examples
    /// ```
    /// use math_rocks::ParserError;
    ///
    /// let initial_err = ParserError::Token('!');
    /// let positioned_err = initial_err.clone().at_pos(7);
    ///
    /// match positioned_err {
    ///     ParserError::AtPosition(pos, ref err_box) => {
    ///         assert_eq!(pos, 7);
    ///         assert_eq!(**err_box, initial_err);
    ///     }
    ///     _ => panic!("Expected AtPosition variant"),
    /// }
    ///
    /// // Calling at_pos on an already positioned error does not change it
    /// let re_positioned_err = positioned_err.clone().at_pos(12);
    /// assert_eq!(re_positioned_err, positioned_err);
    /// ```
    pub fn at_pos(self, position: usize) -> Self {
        match self {
            ParserError::AtPosition(_, _) => self,
            other => ParserError::AtPosition(position, Box::new(other))
        }
    }
}

/// A type alias for `Result`s that use [`ParserError`] as the error type.
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
