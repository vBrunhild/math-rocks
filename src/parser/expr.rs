use std::convert::From;
use std::fmt::Display;
use crate::{Roll, RollResult};


/// Represents an abstract syntax tree (AST) node for a dice expression.
///
/// An `Expr` can be a literal number, a dice roll configuration,
/// a unary operation (like negation), or a binary operation (like addition or subtraction).
/// This structure allows for recursive evaluation and analysis of complex dice expressions.
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// A literal numeric value.
    Literal(u16),
    /// A dice roll configuration using [`Roll`].
    Roll(Roll),
    /// A unary operation (e.g., `-5`, `+ (2d6)`).
    UnaryOperator {
        /// The unary operator (e.g., Plus, Minus).
        op: UnaryOperator,
        /// The operand expression.
        operand: Box<Expr>,
    },
    /// A binary operation (e.g., `1d6 + 5`, `(2d4) * 3`).
    BinaryOperator {
        /// The binary operator (e.g., Add, Subtract, Multiply, Divide).
        op: BinaryOperator,
        /// The left-hand side operand expression.
        left: Box<Expr>,
        /// The right-hand side operand expression.
        right: Box<Expr>,
    }
}

impl Expr {
    /// Evaluates the expression, performing dice rolls and calculating the final numerical value.
    ///
    /// This method recursively traverses the expression tree:
    /// - For [`Expr::Literal`], it returns the value.
    /// - For [`Expr::Roll`], it performs the dice roll and returns its total.
    /// - For [`Expr::UnaryOperator`] and [`Expr::BinaryOperator`], it evaluates the operand(s)
    ///   and then applies the operator.
    ///
    /// All dice rolls performed during evaluation are collected.
    ///
    /// # Returns
    /// An [`EvaluationResult`] containing the final calculated `value` and a `Vec`
    /// of [`RollEvaluation`]s detailing each dice roll that occurred.
    ///
    /// # Examples
    /// ```
    /// use math_rocks::{Roll, Expr, UnaryOperator, BinaryOperator};
    ///
    /// // Example: 1d4 + 5
    /// let roll_expr = Expr::Roll(Roll::builder(4).build().unwrap());
    /// let five_expr = Expr::Literal(5);
    /// let add_expr = Expr::BinaryOperator {
    ///     op: BinaryOperator::Add,
    ///     left: Box::new(roll_expr),
    ///     right: Box::new(five_expr),
    /// };
    ///
    /// let evaluation = add_expr.evaluate();
    /// dbg!(evaluation);
    ///
    /// // Example: -(2)
    /// let two_expr = Expr::Literal(2);
    /// let neg_expr = Expr::UnaryOperator {
    ///     op: UnaryOperator::Minus,
    ///     operand: Box::new(two_expr),
    /// };
    /// let neg_evaluation = neg_expr.evaluate();
    /// assert_eq!(neg_evaluation.value, -2);
    /// assert!(neg_evaluation.rolls.is_empty());
    /// ```
    pub fn evaluate(&self) -> EvaluationResult {
        match self {
            Expr::Literal(value) => EvaluationResult { value: *value as i32, rolls: Vec::new() },

            Expr::Roll(roll) => {
                let evaluation: RollEvaluation = roll.clone().into();
                EvaluationResult { value: evaluation.value, rolls: vec![evaluation] }
            },

            Expr::UnaryOperator { op, operand } => {
                let result = operand.evaluate();

                EvaluationResult {
                    value: op.op(result.value),
                    rolls: result.rolls
                }
            },

            Expr::BinaryOperator { op, left, right } => {
                let mut left = left.evaluate();
                let mut right = right.evaluate();

                let mut rolls = Vec::with_capacity(left.rolls.len() + right.rolls.len());
                rolls.append(&mut left.rolls);
                rolls.append(&mut right.rolls);

                EvaluationResult {
                    value: op.op(left.value, right.value),
                    rolls
                }
            }
        }
    }

    /// Calculates the minimum and maximum possible values this expression can yield.
    ///
    /// - For [`Expr::Literal`], min and max are the literal's value.
    /// - For [`Expr::Roll`], it uses `roll.min()` and `roll.max()`.
    /// - For [`Expr::UnaryOperator`], it applies the operator to the operand's min/max.
    /// - For [`Expr::BinaryOperator`], it considers all four combinations of the operands'
    ///   min/max values to find the overall min and max.
    ///
    /// # Returns
    /// A tuple `(min, max)`.
    ///
    /// # Examples
    /// ```
    /// use math_rocks::{Roll, Expr, BinaryOperator};
    ///
    /// // 1d6 + 2
    /// let roll_1d6 = Expr::Roll(Roll::builder(6).build().unwrap()); // min 1, max 6
    /// let literal_2 = Expr::Literal(2); // min 2, max 2
    /// let expr = Expr::add(roll_1d6, literal_2);
    ///
    /// assert_eq!(expr.possible_values(), (1 + 2, 6 + 2)); // (3, 8)
    ///
    /// // 2 * 1d4
    /// let roll_1d4 = Expr::Roll(Roll::builder(4).build().unwrap()); // min 1, max 4
    /// let expr_mul = Expr::mul(Expr::Literal(2), roll_1d4);
    /// // Combinations: 2 * 1 = 2, 2 * 4 = 8. So min = 2, max = 8.
    /// assert_eq!(expr_mul.possible_values(), (2, 8));
    /// ```
    pub fn possible_values(&self) -> (i32, i32) {
        match self {
            Expr::Literal(value) => {
                let value = *value as i32;
                (value, value)
            },

            Expr::Roll(roll) => (roll.min() as i32, roll.max() as i32),

            Expr::UnaryOperator { op, operand } => {
                let (min, max) = operand.possible_values();
                match op {
                    UnaryOperator::Plus => (min, max),
                    UnaryOperator::Minus => (-max, -min)
                }
            },

            Expr::BinaryOperator { op, left, right } => {
                let (l_min, l_max) = left.possible_values();
                let (r_min, r_max) = right.possible_values();

                let combinations = [
                    op.op(l_min, r_min),
                    op.op(l_min, r_max),
                    op.op(l_max, r_min),
                    op.op(l_max, r_max),
                ];

                (combinations.iter().min().copied().unwrap(), combinations.iter().max().copied().unwrap())
            }
        }
    }

    /// Calculates the average of the minimum and maximum possible values of the expression.
    /// This provides a simple statistical average for the expression's outcome.
    /// 
    /// # Examples
    /// ```
    /// use math_rocks::{Roll, Expr};
    ///
    /// // For 1d6 + 1 (min 2, max 7), avg is (2 + 7) / 2 = 4.5
    /// let expr = Expr::add(Roll::builder(6).build().unwrap(), 1);
    /// assert_eq!(expr.avg(), 4.5);
    /// ```
    pub fn avg(&self) -> f32 {
        let (min, max) = self.possible_values();
        (min as f32 + max as f32) / 2.0
    }

    /// Helper function to create a `UnaryOperator` expression.
    /// This is private as public construction is via `pos` and `neg`.
    fn unary_op<T: Into<Expr>>(op: UnaryOperator, operand: T) -> Self {
        Self::UnaryOperator { op, operand: Box::new(operand.into()) }
    }

    /// Creates a unary plus expression (e.g., `+operand`).
    ///
    /// # Arguments
    /// * `operand`: The expression to apply the unary plus to. Can be any type that implements `Into<Expr>`.
    pub fn pos<T: Into<Expr>>(operand: T) -> Self {
        Self::unary_op(UnaryOperator::Plus, operand)
    }

    /// Creates a unary minus expression (e.g., `-operand`).
    ///
    /// # Arguments
    /// * `operand`: The expression to negate. Can be any type that implements `Into<Expr>`.
    pub fn neg<T: Into<Expr>>(operand: T) -> Self {
        Self::unary_op(UnaryOperator::Minus, operand)
    }

    /// Helper function to create a `BinaryOperator` expression.
    /// This is private as public construction is via specific operator methods.
    fn binary_op<L: Into<Expr>, R: Into<Expr>>(op: BinaryOperator, left: L, right: R) -> Self {
        Self::BinaryOperator { op, left: Box::new(left.into()), right: Box::new(right.into()) }
    }

    /// Creates an addition expression (`left + right`).
    ///
    /// # Arguments
    /// * `left`: The left-hand operand.
    /// * `right`: The right-hand operand.
    /// 
    /// Both can be any type that implements `Into<Expr>`.
    pub fn add<L: Into<Expr>, R: Into<Expr>>(left: L, right: R) -> Self {
        Self::binary_op(BinaryOperator::Add, left, right)
    }

    /// Creates a subtraction expression (`left - right`).
    ///
    /// # Arguments
    /// * `left`: The left-hand operand.
    /// * `right`: The right-hand operand.
    /// 
    /// Both can be any type that implements `Into<Expr>`.
    pub fn sub<L: Into<Expr>, R: Into<Expr>>(left: L, right: R) -> Self {
        Self::binary_op(BinaryOperator::Subtract, left, right)
    }

    /// Creates a multiplication expression (`left * right`).
    ///
    /// # Arguments
    /// * `left`: The left-hand operand.
    /// * `right`: The right-hand operand.
    /// 
    /// Both can be any type that implements `Into<Expr>`.
    pub fn mul<L: Into<Expr>, R: Into<Expr>>(left: L, right: R) -> Self {
        Self::binary_op(BinaryOperator::Multiply, left, right)
    }

    /// Creates a division expression (`left / right`).
    ///
    /// # Arguments
    /// * `left`: The left-hand operand.
    /// * `right`: The right-hand operand.
    /// 
    /// Both can be any type that implements `Into<Expr>`.
    /// Note: Division by zero in `evaluate` will result in `0`.
    pub fn div<L: Into<Expr>, R: Into<Expr>>(left: L, right: R) -> Self {
        Self::binary_op(BinaryOperator::Divide, left, right)
    }
}

impl From<Roll> for Expr {
    fn from(value: Roll) -> Self {
        Self::Roll(value)
    }
}

impl From<u16> for Expr {
    fn from(value: u16) -> Self {
        Self::Literal(value)
    }
}

impl Display for Expr {
    /// Formats the `Expr` into a string representation.
    ///
    /// - Literals are formatted as their number.
    /// - Rolls are formatted using their `Display` implementation (e.g., "3d6kh1").
    /// - Unary operators are formatted as `op<operand>` (e.g., "-5").
    /// - Binary operators are formatted as `(<left> op <right>)` (e.g., "(1d6 + 5)").
    #[cfg(not(tarpaulin_include))]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Literal(v) => write!(f, "{v}"),
            Expr::Roll(roll) => write!(f, "{roll}"),
            Expr::UnaryOperator { op, operand } => write!(f, "{op}{operand}"),
            Expr::BinaryOperator { op, left, right } =>
                write!(f, "({left} {op} {right})")
        }
    }
}


/// Represents a unary operator (acting on a single operand).
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum UnaryOperator {
    /// Unary plus.
    Plus,
    /// Unary minus.
    Minus,
}

impl UnaryOperator {
    /// Applies the unary operator to the given integer value.
    ///
    /// - `Plus` returns the value unchanged.
    /// - `Minus` returns the negation of the value.
    pub fn op(&self, value: i32) -> i32 {
        use UnaryOperator as Op;
        match self {
            Op::Plus => value,
            Op::Minus => -value
        }
    }
}

impl Display for UnaryOperator {
    #[cfg(not(tarpaulin_include))]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnaryOperator::Plus => write!(f, "+"),
            UnaryOperator::Minus => write!(f, "-")
        }
    }
}


/// Represents a binary operator (acting on two operands).
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BinaryOperator {
    /// Addition (`+`).
    Add,
    /// Subtraction (`-`).
    Subtract,
    /// Multiplication (`*`).
    Multiply,
    /// Division (`/`).
    Divide
}

impl BinaryOperator {
    /// Applies the binary operator to the given left and right integer values.
    ///
    /// Operations use saturating arithmetic (`saturating_add`, `saturating_sub`, `saturating_mul`)
    /// to prevent overflow panics, clamping results to `i32::MIN` or `i32::MAX`.
    /// Division by zero results in `0`.
    pub fn op(&self, left: i32, right: i32) -> i32 {
        use BinaryOperator as Op;
        match self {
            Op::Add => left.saturating_add(right),
            Op::Subtract => left.saturating_sub(right),
            Op::Multiply => left.saturating_mul(right),
            Op::Divide => left.checked_div(right).unwrap_or(0)
        }
    }
}

impl Display for BinaryOperator {
    #[cfg(not(tarpaulin_include))]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BinaryOperator::Add => write!(f, "+"),
            BinaryOperator::Subtract => write!(f, "-"),
            BinaryOperator::Multiply => write!(f, "*"),
            BinaryOperator::Divide => write!(f, "/")
        }
    }
}


/// Holds the result of evaluating an [`Expr`].
///
/// It contains the final numerical `value` and a [`Vec`] of all
/// individual dice [`RollEvaluation`]s that occurred during the evaluation.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct EvaluationResult {
    /// The final integer value of the evaluated expression.
    pub value: i32,
    /// A list of all dice rolls performed during the evaluation,
    /// including their configuration, individual results, and total for that roll.
    pub rolls: Vec<RollEvaluation>
}


/// Contains detailed information about a single dice roll performed as part of an [`Expr`] evaluation.
///
/// This includes the original [`Roll`] configuration, the [`RollResult`] (individual die outcomes),
/// and the `value` (total sum) of that specific roll.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct RollEvaluation {
    /// The [`Roll`] configuration that was evaluated.
    pub roll: Roll,
    /// The outcome of the roll.
    pub result: RollResult,
    /// The total numerical value obtained from this specific roll (sum of kept dice).
    pub value: i32
}

impl From<Roll> for RollEvaluation {
    /// Converts a [`Roll`] configuration into a [`RollEvaluation`] by performing the roll.
    ///
    /// This involves calling `value.roll()` to get the `RollResult` and then
    /// calculating its total.
    fn from(value: Roll) -> Self {
        let result = value.roll();
        let total = result.total();
        Self { roll: value, result, value: total as i32 }
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;
    use crate::roll_test_strategies::roll_strategy;

    fn literal_strategy() -> impl Strategy<Value = Expr> {
        (1..=100u16).prop_map(Expr::Literal)
    }

    fn unary_strategy() -> impl Strategy<Value = Expr> {
        (0..=1, literal_strategy())
            .prop_map(|(unary_op, literal)| match unary_op {
                0 => literal,
                _ => Expr::neg(literal)
            })
    }

    fn expr_strategy() -> impl Strategy<Value = Expr> {
        let leaf = prop_oneof![
            literal_strategy(),
            roll_strategy().prop_map(Expr::Roll),
        ];

        leaf.prop_recursive(8, 64, 10, |inner| {
            prop_oneof![
                (prop::sample::select(&[UnaryOperator::Plus, UnaryOperator::Minus]), inner.clone())
                    .prop_map(|(op, operand)| Expr::UnaryOperator {
                        op,
                        operand: Box::new(operand)
                    }),

                (
                    prop::sample::select(&[
                        BinaryOperator::Add,
                        BinaryOperator::Subtract,
                        BinaryOperator::Multiply
                    ]),
                    inner.clone(),
                    inner.clone()
                ).prop_map(|(op, left, right)| Expr::BinaryOperator {
                    op,
                    left: Box::new(left),
                    right: Box::new(right)
                }),

                inner
            ]
        })
    }

    proptest! {
        #[test]
        fn test_expr_evaluate_literal(value in 1..1000u16) {
            let expr = Expr::Literal(value);
            let result = expr.evaluate();

            prop_assert_eq!(result.value, value as i32);
            prop_assert!(result.rolls.is_empty());
        }

        #[test]
        fn test_expr_evaluate_roll(roll in roll_strategy()) {
            let expr = Expr::Roll(roll.clone());
            let result = expr.evaluate();

            prop_assert_eq!(result.rolls.len(), 1);
            prop_assert_eq!(result.rolls[0].roll.to_string(), roll.to_string());
            prop_assert!(result.value >= roll.min() as i32);
            prop_assert!(result.value <= roll.max() as i32);
        }

        #[test]
        fn test_expr_evaluate_unary(
            value in 1..1000u16,
            op in prop::sample::select(&[UnaryOperator::Plus, UnaryOperator::Minus])
        ) {
            let expr = Expr::UnaryOperator {
                op,
                operand: Box::new(Expr::Literal(value))
            };
            let result = expr.evaluate();

            let expected = match op {
                UnaryOperator::Plus => value as i32,
                UnaryOperator::Minus => -(value as i32),
            };

            prop_assert_eq!(result.value, expected);
            prop_assert!(result.rolls.is_empty());
        }

        #[test]
        fn test_expr_evaluate_binary(
            left_val in 1..100u16,
            right_val in 1..100u16,
            op in prop::sample::select(&[
                BinaryOperator::Add,
                BinaryOperator::Subtract,
                BinaryOperator::Multiply
            ])
        ) {
            let expr = Expr::BinaryOperator {
                op,
                left: Box::new(Expr::Literal(left_val)),
                right: Box::new(Expr::Literal(right_val)),
            };
            let result = expr.evaluate();

            let expected = match op {
                BinaryOperator::Add => left_val as i32 + right_val as i32,
                BinaryOperator::Subtract => left_val as i32 - right_val as i32,
                BinaryOperator::Multiply => left_val as i32 * right_val as i32,
                BinaryOperator::Divide => left_val as i32 / right_val as i32,
            };

            prop_assert_eq!(result.value, expected);
            prop_assert!(result.rolls.is_empty());
        }

        #[test]
        fn test_expr_possible_values_literal(value in 1..1000u16) {
            let expr = Expr::Literal(value);
            let (min, max) = expr.possible_values();

            prop_assert_eq!(min, value as i32);
            prop_assert_eq!(max, value as i32);
        }

        #[test]
        fn test_expr_possible_values_roll(roll in roll_strategy()) {
            let expr = Expr::Roll(roll.clone());
            let (min, max) = expr.possible_values();

            prop_assert_eq!(min, roll.min() as i32);
            prop_assert_eq!(max, roll.max() as i32);
            prop_assert!(min <= max);
        }

        #[test]
        fn test_expr_possible_values_unary(
            value in 1..1000u16,
            op in prop::sample::select(&[UnaryOperator::Plus, UnaryOperator::Minus])
        ) {
            let expr = Expr::UnaryOperator {
                op,
                operand: Box::new(Expr::Literal(value))
            };
            let (min, max) = expr.possible_values();

            match op {
                UnaryOperator::Plus => {
                    prop_assert_eq!(min, value as i32);
                    prop_assert_eq!(max, value as i32);
                },
                UnaryOperator::Minus => {
                    prop_assert_eq!(min, -(value as i32));
                    prop_assert_eq!(max, -(value as i32));
                },
            }
        }

        #[test]
        fn test_expr_possible_values_binary(
            left_val in 1..100u16,
            right_val in 1..100u16,
            op in prop::sample::select(&[
                BinaryOperator::Add,
                BinaryOperator::Subtract,
                BinaryOperator::Multiply,
                BinaryOperator::Divide
            ])
        ) {
            let expr = Expr::BinaryOperator {
                op,
                left: Box::new(Expr::Literal(left_val)),
                right: Box::new(Expr::Literal(right_val)),
            };
            let (min, max) = expr.possible_values();

            let expected = match op {
                BinaryOperator::Add => left_val as i32 + right_val as i32,
                BinaryOperator::Subtract => left_val as i32 - right_val as i32,
                BinaryOperator::Multiply => left_val as i32 * right_val as i32,
                BinaryOperator::Divide => left_val as i32 / right_val as i32,
            };

            prop_assert_eq!(min, expected);
            prop_assert_eq!(max, expected);
        }

        #[test]
        fn test_expr_avg_literal(value in 1..1000u16) {
            let expr = Expr::Literal(value);
            let avg = expr.avg();

            prop_assert_eq!(avg, value as f32);
        }

        #[test]
        fn test_expr_avg_roll(roll in roll_strategy()) {
            let expr = Expr::Roll(roll.clone());
            let avg = expr.avg();
            let (min, max) = expr.possible_values();

            prop_assert_eq!(avg, (min as f32 + max as f32) / 2.0);
        }

        #[test]
        fn test_expr_avg_unary(
            value in 1..1000u16,
            op in prop::sample::select(&[UnaryOperator::Plus, UnaryOperator::Minus])
        ) {
            let expr = Expr::UnaryOperator {
                op,
                operand: Box::new(Expr::Literal(value))
            };
            let avg = expr.avg();
            let (min, max) = expr.possible_values();

            prop_assert_eq!(avg, (min as f32 + max as f32) / 2.0);
        }

        #[test]
        fn test_expr_avg_binary(
            left_val in 1..100u16,
            right_val in 1..100u16,
            op in prop::sample::select(&[
                BinaryOperator::Add,
                BinaryOperator::Subtract,
                BinaryOperator::Multiply,
                BinaryOperator::Divide
            ])
        ) {
            let expr = Expr::BinaryOperator {
                op,
                left: Box::new(Expr::Literal(left_val)),
                right: Box::new(Expr::Literal(right_val)),
            };
            let avg = expr.avg();
            let (min, max) = expr.possible_values();

            prop_assert_eq!(avg, (min as f32 + max as f32) / 2.0);
        }

        #[test]
        fn test_unary_op_helper(
            value in 1..100u16,
            op in prop::sample::select(&[UnaryOperator::Plus, UnaryOperator::Minus])
        ) {
            let expr = Expr::unary_op(op, value);

            match expr {
                Expr::UnaryOperator { op: result_op, operand } => {
                    prop_assert_eq!(result_op, op);
                    match *operand {
                        Expr::Literal(v) => prop_assert_eq!(v, value),
                        _ => panic!("Expected literal operand")
                    }
                },
                _ => panic!("Expected unary operator")
            }
        }

        #[test]
        fn test_binary_op_helper(
            left in 1..100u16,
            right in 1..100u16,
            op in prop::sample::select(&[
                BinaryOperator::Add,
                BinaryOperator::Subtract,
                BinaryOperator::Multiply,
                BinaryOperator::Divide
            ])
        ) {
            let expr = Expr::binary_op(op, left, right);

            match expr {
                Expr::BinaryOperator { op: result_op, left: l, right: r } => {
                    prop_assert_eq!(result_op, op);
                    match (*l, *r) {
                        (Expr::Literal(lv), Expr::Literal(rv)) => {
                            prop_assert_eq!(lv, left);
                            prop_assert_eq!(rv, right);
                        },
                        _ => panic!("Expected literal operands")
                    }
                },
                _ => panic!("Expected binary operator")
            }
        }

        #[test]
        fn test_expr_constructors(
            left in 1..100u16,
            right in 1..100u16
        ) {
            let add_expr = Expr::add(left, right);
            let sub_expr = Expr::sub(left, right);
            let mul_expr = Expr::mul(left, right);
            let div_expr = Expr::div(left, right);

            assert!(matches!(add_expr, Expr::BinaryOperator { op: BinaryOperator::Add, .. }));
            assert!(matches!(sub_expr, Expr::BinaryOperator { op: BinaryOperator::Subtract, .. }));
            assert!(matches!(mul_expr, Expr::BinaryOperator { op: BinaryOperator::Multiply, .. }));
            assert!(matches!(div_expr, Expr::BinaryOperator { op: BinaryOperator::Divide, .. }));
        }

        #[test]
        fn test_expr_unary_constructors(value in 1..100u16) {
            let pos_expr = Expr::pos(value);
            let neg_expr = Expr::neg(value);

            assert!(matches!(pos_expr, Expr::UnaryOperator { op: UnaryOperator::Plus, .. }));
            assert!(matches!(neg_expr, Expr::UnaryOperator { op: UnaryOperator::Minus, .. }));
        }

        #[test]
        fn test_unary_operator_op(
            value in -1000..1000i32,
            op in prop::sample::select(&[UnaryOperator::Plus, UnaryOperator::Minus])
        ) {
            let result = op.op(value);

            match op {
                UnaryOperator::Plus => prop_assert_eq!(result, value),
                UnaryOperator::Minus => prop_assert_eq!(result, -value),
            }
        }

        #[test]
        fn test_binary_operator_op(
            left in -100..100i32,
            right in -100..100i32,
            op in prop::sample::select(&[
                BinaryOperator::Add,
                BinaryOperator::Subtract,
                BinaryOperator::Multiply,
                BinaryOperator::Divide
            ])
        ) {
            let result = op.op(left, right);

            match op {
                BinaryOperator::Add => prop_assert_eq!(result, left + right),
                BinaryOperator::Subtract => prop_assert_eq!(result, left - right),
                BinaryOperator::Multiply => prop_assert_eq!(result, left * right),
                BinaryOperator::Divide => prop_assert_eq!(result, left.checked_div(right).unwrap_or(0)),
            }
        }

        #[test]
        fn test_expr_from_u16(value in 1..1000u16) {
            let expr: Expr = value.into();
            prop_assert!(matches!(expr, Expr::Literal(v) if v == value));
        }

        #[test]
        fn test_expr_from_roll(roll in roll_strategy()) {
            let expr: Expr = roll.clone().into();
            prop_assert!(matches!(expr, Expr::Roll(r) if r.to_string() == roll.to_string()));
        }

        #[test]
        fn test_roll_evaluation_from_roll(roll in roll_strategy()) {
            let evaluation: RollEvaluation = roll.clone().into();

            prop_assert_eq!(evaluation.roll.to_string(), roll.to_string());
            prop_assert!(evaluation.value >= roll.min() as i32);
            prop_assert!(evaluation.value <= roll.max() as i32);
            prop_assert_eq!(evaluation.value, evaluation.result.total() as i32);
        }

        #[test]
        fn test_expr_evaluation(expr in expr_strategy()) {
            let (min, max) = expr.possible_values();
            let evaluation = expr.evaluate();

            prop_assert!(evaluation.value >= min);
            prop_assert!(evaluation.value <= max);
        }

        #[test]
        fn test_edge_case_div_0(expr in unary_strategy()) {
            let div_expr = Expr::BinaryOperator {
                op: BinaryOperator::Divide,
                left: Box::new(expr),
                right: Box::new(Expr::Literal(0))
            };

            let evaluation = div_expr.evaluate();
            prop_assert_eq!(evaluation.value, 0)
        }
    }
}
