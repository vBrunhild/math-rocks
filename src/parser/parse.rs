use crate::{Mode, Roll};
use crate::parser::error::*;
use crate::parser::{Lexer, Token, Expr};


#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Precedence {
    Lowest = 1,
    Sum = 2,
    Product = 3,
    Prefix = 4,
    Dice = 5,
}

impl Precedence {
    fn of_token(token: &Token) -> Self {
        match token {
            Token::Plus | Token::Minus => Precedence::Sum,
            Token::Multiply | Token::Divide => Precedence::Product,
            Token::Dice => Precedence::Dice,
            _ => Precedence::Lowest
        }
    }
}


/// A Pratt parser for dice notation strings.
///
/// The parser takes a string input, tokenizes it
/// and then constructs an abstract syntax tree ([`Expr`]) representing
/// the parsed expression. It handles operator precedence and associativity.
#[derive(Debug)]
pub struct Parser {
    lexer: Lexer,
    current: Token,
    peek: Token
}

impl Parser {
    /// Creates a new `Parser` instance for the given input string..
    ///
    /// # Arguments
    /// * `input`: The dice notation string to parse.
    ///
    /// # Errors
    /// Errors returned are always wrapped with a [`ParserError::AtPosition`]
    /// The wrapped error can be any other error of [`ParserError`]
    ///
    /// # Examples
    /// ```
    /// use math_rocks::{Parser, ParserError};
    ///
    /// let parser_result = Parser::new("1d6 + 3");
    /// assert!(parser_result.is_ok());
    /// dbg!(parser_result.unwrap()); // generated Expr
    ///
    /// let empty_parser_result = Parser::new("  ").unwrap_err();
    /// assert!(matches!(empty_parser_result.err(), ParserError::Empty));
    /// ```
    pub fn new(input: &str) -> Result<Self, ParserError> {
        let mut lexer = Lexer::new(input);
        let current = lexer.next_token()?;

        if current == Token::Eof {
            return Err(ParserError::Empty);
        }

        let peek = lexer.next_token()?;
        Ok(Self { lexer, current, peek })
    }

    /// Parses the entire input string into an [`Expr`] (Abstract Syntax Tree).
    ///
    /// This is the main entry point for parsing after creating a `Parser` instance.
    /// It starts parsing tokens with the lowest precedence.
    ///
    /// # Errors
    /// Returns a `ParserError` if any syntax errors are encountered during parsing.
    /// The error will be wrapped with positional information using [`ParserError::at_pos()`]
    /// indicating where the error occurred in the input string.
    /// 
    /// Get a reference to the wrapped error with [`ParserError::err()`].
    /// Get the position at which the error was found with [`ParserError::pos()`].
    ///
    /// # Examples
    /// ```
    /// use math_rocks::{Parser, ParserError};
    ///
    /// let mut parser = Parser::new("1 + 2").unwrap();
    /// let expr = parser.parse().unwrap();
    /// assert_eq!(format!("{expr}"), "(1 + 2)");
    ///
    /// let mut invalid_parser = Parser::new("1 +").unwrap();
    /// let err = invalid_parser.parse().unwrap_err();
    /// assert!(matches!(err.err(), ParserError::UnexpectedPrefix(_)))
    /// ```
    pub fn parse(&mut self) -> Result<Expr, ParserError> {
        self.parse_tokens(Precedence::Lowest)
            .map_err(|err| err.at_pos(self.lexer.position))
    }

    fn next_token(&mut self) -> Result<(), ParserError> {
        self.current = self.peek;
        self.peek = self.lexer.next_token()?;

        Ok(())
    }

    fn parse_tokens(&mut self, precedence: Precedence) -> Result<Expr, ParserError> {
        let mut expr = self.parse_prefix()?;

        while self.peek != Token::Eof && precedence < self.peek_precedence() {
            self.next_token()?;
            expr = self.parse_infix(expr)?;
        }

        Ok(expr)
    }

    fn parse_prefix(&mut self) -> Result<Expr, ParserError> {
        match self.current {
            Token::Number(v) => Ok(v.into()),

            Token::Minus => {
                self.next_token()?;
                let operand = self.parse_tokens(Precedence::Prefix)?;
                Ok(Expr::neg(operand))
            },

            Token::Plus => {
                self.next_token()?;
                let operand = self.parse_tokens(Precedence::Prefix)?;
                Ok(Expr::pos(operand))
            },

            Token::LeftParenthesis => {
                self.next_token()?;
                let expr = self.parse_tokens(Precedence::Lowest)?;

                if self.peek != Token::RightParenthesis {
                    return Err(ParserError::UnclosedParenthesis);
                }

                self.next_token()?;
                Ok(expr)
            },

            other => {
                let token = format!("{other:?}");
                match (other, self.peek) {
                    (Token::Dice, _) | (_, Token::Dice) => Err(ParserError::UnexpectedDiceExpression(token)),
                    _ => Err(ParserError::UnexpectedPrefix(token))
                }
            }
        }
    }

    fn parse_infix(&mut self, expr: Expr) -> Result<Expr, ParserError> {
        match self.current {
            Token::Dice => self.parse_dice(expr),
            Token::Plus | Token::Minus | Token::Multiply | Token::Divide => self.parse_binary_op(expr),
            other => Err(ParserError::UnexpectedInfix(format!("{other:?}")))
        }
    }

    fn parse_binary_op(&mut self, left: Expr) -> Result<Expr, ParserError> {
        let op = self.current;
        self.next_token()?;

        let right = self.parse_tokens(Precedence::of_token(&op))?;

        match op {
            Token::Plus => Ok(Expr::add(left, right)),
            Token::Minus => Ok(Expr::sub(left, right)),
            Token::Multiply => Ok(Expr::mul(left, right)),
            Token::Divide => Ok(Expr::div(left, right)),
            other => unreachable!("{other:?}")
        }
    }

    fn parse_dice(&mut self, count_expr: Expr) -> Result<Expr, ParserError> {
        let count = match count_expr {
            Expr::Literal(n) => n,
            other => return Err(ParserError::UnexpectedDiceExpression(format!("{other:?}")))
        };

        let size = match self.peek {
            Token::Number(size) => size,
            other => return Err(ParserError::UnexpectedDiceExpression(format!("{other:?}")))
        };

        self.next_token()?;

        let mode = self.parse_dice_mode()?;

        Ok(
            Roll::builder(size)
                .count(count)
                .mode(mode)
                .build()?
                .into()
        )
    }

    fn parse_dice_mode(&mut self) -> Result<Mode, ParserError> {
        match self.peek {
            Token::KeepHighest | Token::KeepLowest | Token::DropHighest | Token::DropLowest => {
                self.next_token()?;
                let mode_token = self.current;

                let n = match self.peek {
                    Token::Number(n) => {
                        self.next_token()?;
                        n
                    },
                    _ => 1
                };

                match mode_token {
                    Token::KeepHighest => Ok(Mode::kh(n)),
                    Token::KeepLowest => Ok(Mode::kl(n)),
                    Token::DropHighest => Ok(Mode::dh(n)),
                    Token::DropLowest => Ok(Mode::dl(n)),
                    other => unreachable!("{other:?}")
                }
            },
            _ => Ok(Mode::None)
        }
    }

    fn peek_precedence(&self) -> Precedence {
        Precedence::of_token(&self.peek)
    }
}


/// Parses a dice notation string directly into an [`Expr`] (Abstract Syntax Tree).
/// This is a convenience function that creates a [`Parser`] and calls its `parse` method.
///
/// # Arguments
/// * `input`: The dice notation string to parse.
///
/// # Returns
/// `Ok(Expr)` if parsing is successful.
/// `Err(ParserError)` if any parsing errors occur, including positional information.
///
/// # Errors
/// Returns a `ParserError` if any syntax errors are encountered during parsing.
/// The error will be wrapped with positional information using [`ParserError::at_pos()`]
/// indicating where the error occurred in the input string.
/// 
/// Get a reference to the wrapped error with [`ParserError::err()`].
/// Get the position at which the error was found with [`ParserError::pos()`].
/// 
/// # Examples
/// ```
/// use math_rocks::parse_to_expr;
///
/// let expr_result = parse_to_expr("2d20kh + 5");
/// assert!(expr_result.is_ok());
/// dbg!(expr_result);
/// ```
pub fn parse_to_expr(input: &str) -> Result<Expr, ParserError> {
    let mut parser = Parser::new(input)?;
    parser.parse()
}


/// Parses a dice notation string and immediately evaluates it.
///
/// This function first parses the input into an [`Expr`] using [`parse_to_expr`],
/// and then calls [`Expr::evaluate()`] on the resulting AST.
///
/// # Arguments
/// * `input`: The dice notation string to parse and evaluate.
///
/// # Returns
/// `Ok(EvaluationResult)` if parsing and evaluation are successful.
/// `Err(ParserError)` if any parsing errors occur.
///
/// # Errors
/// Returns a `ParserError` if any syntax errors are encountered during parsing.
/// The error will be wrapped with positional information using [`ParserError::at_pos()`]
/// indicating where the error occurred in the input string.
/// 
/// Get a reference to the wrapped error with [`ParserError::err()`].
/// Get the position at which the error was found with [`ParserError::pos()`].
/// 
/// # Examples
/// ```
/// use math_rocks::parse;
///
/// let eval_result = parse("2d6 + 3");
///
/// if let Ok(result) = eval_result {
///     println!("Value: {}, Rolls: {:?}", result.value, result.rolls);
///     assert!(result.value >= 5 && result.value <= 15);
///     assert_eq!(result.rolls.len(), 1);
/// }
/// ```
pub fn parse(input: &str) -> Result<crate::EvaluationResult, ParserError> {
    Ok(parse_to_expr(input)?.evaluate())
}


#[cfg(test)]
mod test {
    use proptest::prelude::*;
    use super::*;
    use crate::parser::str_test_strategies::*;
    use crate::roll_test_strategies::roll_strategy;

    fn token_strategy() -> impl Strategy<Value = Token> {
        prop_oneof![
            (1u16..=100).prop_map(Token::Number),
            Just(Token::Dice),
            Just(Token::Plus),
            Just(Token::Minus),
            Just(Token::Multiply),
            Just(Token::Divide),
            Just(Token::LeftParenthesis),
            Just(Token::RightParenthesis),
            Just(Token::KeepHighest),
            Just(Token::KeepLowest),
            Just(Token::DropHighest),
            Just(Token::DropLowest),
            Just(Token::Eof),
        ]
    }

    proptest! {
        #[test]
        fn test_precedence_of_token(token in token_strategy()) {
            let precedence = Precedence::of_token(&token);

            match token {
                Token::Plus | Token::Minus => prop_assert_eq!(precedence, Precedence::Sum),
                Token::Multiply | Token::Divide => prop_assert_eq!(precedence, Precedence::Product),
                Token::Dice => prop_assert_eq!(precedence, Precedence::Dice),
                _ => prop_assert_eq!(precedence, Precedence::Lowest),
            }
        }

        #[test]
        fn test_precedence_consistency(
            a in -100i32..=100,
            b in -100i32..=100,
            c in -100i32..=100
        ) {
            if a == 0 || b == 0 || c == 0 { return Ok(()) };

            let expected1 = a + b * c;
            let expected2 = a * b + c;

            let expr1 = format!("{a} + {b} * {c}");
            let expr2 = format!("{a} * {b} + {c}");

            let result1 = parse(&expr1);
            let result2 = parse(&expr2);

            prop_assert!(result1.is_ok());
            prop_assert!(result2.is_ok());

            if let (Ok(r1), Ok(r2)) = (result1, result2) {
                if a != 0 && b != 0 && c != 0 {
                    prop_assert_eq!(r1.value, expected1);
                    prop_assert_eq!(r2.value, expected2);
                }
            }
        }

        #[test]
        fn test_peek_precedence(
            n1 in 1u16..=100,
            n2 in 1u16..=100,
            op in prop::sample::select(&[
                (Token::Plus, "+"),
                (Token::Minus, "-"),
                (Token::Multiply, "*"),
                (Token::Divide, "/")
            ])
        ) {
            let (token, token_str) = op;
            let input = format!("{n1} {token_str} {n2}");
            if let Ok(parser) = Parser::new(&input) {
                let precedence = parser.peek_precedence();
                prop_assert_eq!(precedence, Precedence::of_token(&token));
            }
        }

        #[test]
        fn test_parse_prefix(current in token_strategy(), peek in token_strategy()) {
            let mut parser = Parser { lexer: Lexer::new(""), current, peek };
            let result = parser.parse_prefix();

            match (current, peek) {
                (Token::Number(_), _) =>
                    prop_assert!(matches!(result, Ok(Expr::Literal(_))), "result = {result:?}"),

                (Token::Plus | Token::Minus, Token::Number(_)) =>
                    prop_assert!(matches!(result, Ok(Expr::UnaryOperator { .. })), "result = {result:?}"),

                (_, Token::Dice) | (Token::Dice, _) =>
                    prop_assert!(matches!(result, Err(ParserError::UnexpectedDiceExpression(_))), "result = {result:?}"),

                (Token::LeftParenthesis, Token::Number(_)) =>
                    prop_assert!(matches!(result, Err(ParserError::UnclosedParenthesis)), "result = {result:?}"),

                _ => prop_assert!(matches!(result, Err(ParserError::UnexpectedPrefix(_))), "result = {result:?}")
            }
        }

        #[test]
        fn test_parse_infix(
            left in (1u16..=100).prop_map(Expr::Literal),
            current in token_strategy(),
            peek in token_strategy()
        ) {
            let mut parser = Parser { lexer: Lexer::new("777"), current, peek };
            let result = parser.parse_infix(left);

            match (current, peek) {
                (Token::Dice, Token::Number(_)) =>
                    prop_assert!(result.is_ok(), "result = {result:?}"),
                                
                (Token::Dice, _) | (_, Token::Dice) =>
                    prop_assert!(result.is_err(), "result = {result:?}"),

                (Token::Plus | Token::Minus | Token::Multiply | Token::Divide, Token::Number(_)) =>
                    prop_assert!(matches!(result, Ok(Expr::BinaryOperator { .. })), "result = {result:?}"),

                (Token::Plus | Token::Minus | Token::Multiply | Token::Divide, Token::Plus | Token::Minus) =>
                    prop_assert!(matches!(result, Ok(Expr::BinaryOperator { .. })), "result = {result:?}"),                

                (Token::Plus | Token::Minus | Token::Multiply | Token::Divide, Token::LeftParenthesis) =>
                    prop_assert!(matches!(result, Err(ParserError::UnclosedParenthesis)), "result = {result:?}"),

                (Token::Plus | Token::Minus | Token::Multiply | Token::Divide, _) =>
                    prop_assert!(matches!(result, Err(ParserError::UnexpectedPrefix(_))), "result = {result:?}"),

                _ => prop_assert!(matches!(result, Err(ParserError::UnexpectedInfix(_))), "result = {result:?}")
            }
        }

        #[test]
        fn test_literal_expression(value in -1000i32..=1000) {
            if value == 0 { return Ok(()) };
            let mut parser = Parser::new(&value.to_string()).unwrap();
            let expr = parser.parse().unwrap();
            let evaluation = expr.evaluate();
            prop_assert_eq!(value, evaluation.value)
        }

        #[test]
        fn test_complex_dice_expression(expr_str in dice_expression_strategy()) {
            let mut parser = Parser::new(&expr_str).unwrap();

            let expr = match parser.parse() {
                Ok(ex) => ex,
                Err(err) => panic!("{err}")
            };

            let _result = expr.evaluate();
        }

        #[test]
        fn test_parse_dice(
            value in 1u16..=100,
            other_expr in roll_strategy(),
            token in token_strategy()
        ) {
            let mut parser = Parser { lexer: Lexer::new(""), current: token, peek: token };

            let result_ok = parser.parse_dice(value.into());
            match token {
                Token::Number(_) => prop_assert!(result_ok.is_ok()),
                _ => prop_assert!(matches!(result_ok.unwrap_err(), ParserError::UnexpectedDiceExpression(_)))
            }

            let result_err = parser.parse_dice(other_expr.into());
            prop_assert!(matches!(result_err.unwrap_err(), ParserError::UnexpectedDiceExpression(_)));
        }

        #[test]
        fn test_parse_to_expr_function(valid_expr in dice_expression_strategy()) {
            let result = parse_to_expr(&valid_expr);
            prop_assert!(result.is_ok());
        }

        #[test]
        fn test_parse_function(valid_expr in dice_expression_strategy()) {
            let result = parse(&valid_expr);
            prop_assert!(result.is_ok());
        }

        #[test]
        fn test_dice_without_mode(count in 1u16..=100, size in 1u16..=100) {
            let expr = format!("{count}d{size}");
            let result = parse(&expr);
            assert!(result.is_ok());
        }

        #[test]
        fn test_dice_with_default_mode_value(
            count in 1u16..=100,
            size in 1u16..=100,
            mode in prop::sample::select(&["kh", "kl", "dh", "dl"])
        ) {
            let expr = format!("{count}d{size}{mode}");
            let result = parse(&expr);

            if count == 1 {
                assert!(result.is_err())
            } else {
                assert!(result.is_ok());
            }
        }

        #[test]
        fn test_edge_case_white_space(input in "[ \\t\\n]+") {
            let result = Parser::new(&input);
            assert!(matches!(result, Err(ParserError::Empty)))
        }
    }

    #[test]
    fn test_edge_case_empty() {
        let result = Parser::new("");
        assert!(matches!(result, Err(ParserError::Empty)))
    }
}
