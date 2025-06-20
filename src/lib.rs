#![warn(missing_docs)]
#![warn(clippy::missing_errors_doc)]

//! # Math Rocks
//!
//! Math Rocks is a Rust crate designed for parsing and evaluating dice expressions.
//! It provides a robust and flexible way to handle common dice notation used in
//! tabletop role-playing games and other contexts where random number generation
//! based on dice rolls is required.
//!
//! 
//! ## Features
//!
//! *   **Dice Notation Parsing:** Parses strings representing dice rolls, including:
//!     *   Basic dice rolls (e.g., `1d6`, `3d20`).
//!     *   Dice with modifiers like "keep highest" (`khN`), "keep lowest" (`klN`),
//!         "drop highest" (`dhN`), and "drop lowest" (`dlN`). For example, `4d10kh2`
//!         means "roll four 10-sided dice and keep the two highest results."
//!     *   Arithmetic operations: addition (`+`), subtraction (`-`), multiplication (`*`),
//!         and division (`/`) between dice rolls and literal numbers.
//!     *   Parentheses for grouping and controlling order of operations.
//!     *   Unary operators (`+` and `-`) for negation.
//! *   **Abstract Syntax Tree (AST):** Represents parsed expressions as an Abstract
//!     Syntax Tree (`Expr`), allowing for structural analysis and evaluation.
//! *   **Evaluation:** Evaluates dice expressions, performing the actual random rolls
//!     and calculations. It returns the final result along with a detailed breakdown
//!     of each individual dice roll performed.
//! *   **Statistical Properties:** Calculates minimum, maximum, and average possible
//!     outcomes for any given dice expression without needing to perform a random roll.
//!
//! 
//! ## Adding to your project
//! ```cmd
//! cargo add math-rocks
//! ```
//!
//! 
//! ### Basic Usage
//! ```rust
//! use math_rocks::{parse, roll, Roll};
//!
//! // Parse and evaluate a simple dice roll
//! let result1 = parse("2d6").unwrap();
//! println!("2d6 result: {}", result1.value); // Prints a random sum between 2 and 12
//!
//! // Parse and evaluate a roll with a modifier
//! let result2 = parse("4d10kh2 + 5").unwrap();
//! println!("4d10kh2 + 5 result: {}", result2.value); // Prints the sum of the 2 highest d10s + 5
//!
//! // Calculate statistical properties
//! let roll_config = Roll::builder(20).count(3).build().unwrap(); // 3d20
//! println!("Min possible for 3d20: {}", roll_config.min()); // 3
//! println!("Max possible for 3d20: {}", roll_config.max()); // 60
//! println!("Avg possible for 3d20: {}", roll_config.avg()); // 31.5
//!
//! // Using the macro
//! let result3 = roll!(3, 8, dl, 1).unwrap(); // 3d8, drop lowest 1
//! println!("3d8dl1 result: {}", result_result.value);
//! ```
//! For more details please refer to the documentantion of [`parse`], [`roll`] and [`Roll`].
//! 
//! ## Features
//! The following features are available:
//!
//! *   `serde`: Enable serialization and deserialization of `Roll`, `Mode`, `RollValue`,
//!     `RollResult`, `Expr`, `EvaluationResult`, and `RollEvaluation` types using the
//!     `serde` crate.

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
