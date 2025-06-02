#![warn(missing_docs)]
#![warn(clippy::missing_errors_doc)]


#[cfg(test)]
mod roll_test_strategies;

mod error;
mod roll;
mod parser;

pub use error::Error;
pub use roll::{Roll, RollBuilder, RollValue, RollResult, Mode};
pub use parser::{
    ParserError, Parser,
    Expr, UnaryOperator, BinaryOperator,
    EvaluationResult, RollEvaluation,
    parse, parse_to_expr
};
