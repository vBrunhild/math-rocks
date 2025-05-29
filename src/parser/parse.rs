use crate::{Mode, Roll};
use crate::parser::error::*;
use crate::parser::{Lexer, Token, Expr};


#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
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


#[derive(Debug)]
pub struct Parser {
    lexer: Lexer,
    current: Token,
    peek: Token
}

impl Parser {
    pub fn new(input: &str) -> Result<Self> {
        let mut lexer = Lexer::new(input);
        let current = lexer.next_token()?;

        if current == Token::Eof {
            return Err(ParserError::Empty);
        }

        let peek = lexer.next_token()?;
        Ok(Self { lexer, current, peek })
    }

    pub fn parse(&mut self) -> Result<Expr> {
        self.parse_tokens(Precedence::Lowest)
            .map_err(|err| {
                ParserError::RollExpr(format!("{}\nat position {}", err, self.lexer.position))
            })
    }

    fn next_token(&mut self) -> Result<()> {
        self.current = self.peek;
        self.peek = self.lexer.next_token()?;

        Ok(())
    }

    fn parse_tokens(&mut self, precedence: Precedence) -> Result<Expr> {
        let mut expr = self.parse_prefix()?;

        while self.peek != Token::Eof && precedence < self.peek_precedence() {
            self.next_token()?;
            expr = self.parse_infix(expr)?;
        }

        Ok(expr)
    }

    fn parse_prefix(&mut self) -> Result<Expr> {
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
                    return Err(ParserError::RollExpr("Expected closing parenthesis".into()));
                }

                self.next_token()?;
                Ok(expr)
            },

            other => Err(ParserError::RollExpr(format!("Unexpected expression {:?}", other)))
        }
    }

    fn parse_infix(&mut self, expr: Expr) -> Result<Expr> {
        match self.current {
            Token::Dice => self.parse_dice(expr),
            Token::Plus | Token::Minus | Token::Multiply | Token::Divide => self.parse_binary_op(expr),
            other => Err(ParserError::RollExpr(format!("Unexpected infix token: {:?}", other)))
        }
    }

    fn parse_binary_op(&mut self, left: Expr) -> Result<Expr> {
        let op = self.current;
        self.next_token()?;

        let right = self.parse_tokens(Precedence::of_token(&op))?;

        match op {
            Token::Plus => Ok(Expr::add(left, right)),
            Token::Minus => Ok(Expr::sub(left, right)),
            Token::Multiply => Ok(Expr::mul(left, right)),
            Token::Divide => Ok(Expr::div(left, right)),
            other => Err(ParserError::RollExpr(format!("Unexpected binary operation token: {:?}", other)))
        }
    }

    fn parse_dice(&mut self, count_expr: Expr) -> Result<Expr> {
        let count = match count_expr {
            Expr::Literal(n) => n,
            other => return Err(ParserError::RollExpr(format!("Unexpected dice count expression: {:?}", other)))
        };

        let size = match self.peek {
            Token::Number(size) => size,
            other => return Err(ParserError::RollExpr(format!("Unexpected dice size expression: {:?}", other)))
        };

        self.next_token()?;

        let mode = self.parse_dice_mode()?;

        Ok(
            Roll::builder(size)
                .count(count)
                .mode(mode)
                .build()
                .map_err(Box::new)?
                .into()
        )
    }

    fn parse_dice_mode(&mut self) -> Result<Mode> {
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
                    other => Err(ParserError::RollExpr(format!("Unexpected dice mode expression: {:?}", other)))
                }
            },
            _ => Ok(Mode::None)
        }
    }

    fn peek_precedence(&self) -> Precedence {
        Precedence::of_token(&self.peek)
    }
}


pub fn parse_to_expr(input: &str) -> std::result::Result<Expr, ParserError> {
    let mut parser = Parser::new(input)?;
    parser.parse()
}


pub fn parse(input: &str) -> std::result::Result<crate::EvaluationResult, ParserError> {
    Ok(parse_to_expr(input)?.evaluate())
}


#[cfg(test)]
mod test {
    use proptest::prelude::*;
    use super::*;

}
