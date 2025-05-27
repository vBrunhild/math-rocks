use std::convert::From;
use std::fmt::Display;
use crate::{Roll, RollResult};


#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Literal(u16),
    Roll(Roll),
    UnaryOperator {
        op: UnaryOperator,
        operand: Box<Expr>
    },
    BinaryOperator {
        op: BinaryOperator,
        left: Box<Expr>,
        right: Box<Expr>
    }
}

impl Expr {
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

    pub fn avg(&self) -> f32 {
        let (min, max) = self.possible_values();
        (min as f32 + max as f32) / 2.0
    }

    fn unary_op<T: Into<Expr>>(op: UnaryOperator, operand: T) -> Self {
        Self::UnaryOperator { op, operand: Box::new(operand.into()) }
    }

    pub fn pos<T: Into<Expr>>(operand: T) -> Self {
        Self::unary_op(UnaryOperator::Plus, operand)
    }

    pub fn neg<T: Into<Expr>>(operand: T) -> Self {
        Self::unary_op(UnaryOperator::Minus, operand)
    }

    fn binary_op<L: Into<Expr>, R: Into<Expr>>(op: BinaryOperator, left: L, right: R) -> Self {
        Self::BinaryOperator { op, left: Box::new(left.into()), right: Box::new(right.into()) }
    }

    pub fn add<L: Into<Expr>, R: Into<Expr>>(left: L, right: R) -> Self {
        Self::binary_op(BinaryOperator::Add, left, right)
    }

    pub fn sub<L: Into<Expr>, R: Into<Expr>>(left: L, right: R) -> Self {
        Self::binary_op(BinaryOperator::Subtract, left, right)
    }

    pub fn mul<L: Into<Expr>, R: Into<Expr>>(left: L, right: R) -> Self {
        Self::binary_op(BinaryOperator::Multiply, left, right)
    }

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


#[derive(Debug, Clone, PartialEq)]
pub enum UnaryOperator {
    Plus,
    Minus,
}

impl UnaryOperator {
    pub fn op(&self, value: i32) -> i32 {
        use UnaryOperator as Op;
        match self {
            Op::Plus => value,
            Op::Minus => -value
        }
    }
}

impl Display for UnaryOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnaryOperator::Plus => write!(f, "+"),
            UnaryOperator::Minus => write!(f, "-")
        }
    }
}


#[derive(Debug, Clone, PartialEq)]
pub enum BinaryOperator {
    Add,
    Subtract,
    Multiply,
    Divide,
}

impl BinaryOperator {
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
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BinaryOperator::Add => write!(f, "+"),
            BinaryOperator::Subtract => write!(f, "-"),
            BinaryOperator::Multiply => write!(f, "*"),
            BinaryOperator::Divide => write!(f, "/")
        }
    }
}


#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct EvaluationResult {
    pub value: i32,
    pub rolls: Vec<RollEvaluation>
}


#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct RollEvaluation {
    pub roll: Roll,
    pub result: RollResult,
    pub value: i32
}

impl From<Roll> for RollEvaluation {
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
    use crate::{Roll, Mode};

    fn mode_strategy(max_n: u16) -> impl Strategy<Value = Mode> {
        if max_n <= 1 {
            return Just(Mode::None).boxed();
        }
        
        (1u16..max_n, 0u8..5).prop_map(|(n, mode_type)| {
            match mode_type {
                0 => Mode::None,
                1 => Mode::kh(n),
                2 => Mode::kl(n),
                3 => Mode::dh(n),
                _ => Mode::dl(n),
            }
        }).boxed()
    }

    fn roll_strategy() -> impl Strategy<Value = Roll> {
        (1..=20u16, 1..=10u16)
            .prop_flat_map(|(size, count)| {
                mode_strategy(count).prop_map(move |mode| {
                    Roll::builder(size).count(count).mode(mode).build().unwrap()
                })
            })
    }

    fn expr_strategy() -> impl Strategy<Value = Expr> {
        let leaf = prop_oneof![
            (1..1000u16).prop_map(Expr::Literal),
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
                    inner
                ).prop_map(|(op, left, right)| Expr::BinaryOperator {
                    op,
                    left: Box::new(left),
                    right: Box::new(right)
                }),
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
                op: op.clone(),
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
                op: op.clone(),
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
                op: op.clone(),
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
            left_val in 1..50u16,
            right_val in 1..50u16,
            op in prop::sample::select(&[
                BinaryOperator::Add,
                BinaryOperator::Subtract,
                BinaryOperator::Multiply
            ])
        ) {
            let expr = Expr::BinaryOperator {
                op: op.clone(),
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
    }
}
