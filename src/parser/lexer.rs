use crate::parser::error::*;


#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum Token {
    Number(u16),
    Dice,
    Plus,
    Minus,
    Multiply,
    Divide,
    LeftParenthesis,
    RightParenthesis,
    KeepHighest,
    KeepLowest,
    DropHighest,
    DropLowest,
    Eof,
}


#[derive(Debug)]
pub(crate) struct Lexer {
    input: Vec<char>,
    position: usize,
}

impl Lexer {
    pub fn new(input: &str) -> Self {
        Self {
            input: input.chars().collect(),
            position: 0,
        }
    }

    pub fn next_token(&mut self) -> Result<Token> {
        self.skip_whitespace();

        if self.position >= self.input.len() {
            return Ok(Token::Eof);
        }

        let ch = self.input[self.position];
        
        match ch {
            '+' => {
                self.position += 1;
                Ok(Token::Plus)
            }
            '-' => {
                self.position += 1;
                Ok(Token::Minus)
            }
            '*' => {
                self.position += 1;
                Ok(Token::Multiply)
            }
            '/' => {
                self.position += 1;
                Ok(Token::Divide)
            }
            '(' => {
                self.position += 1;
                Ok(Token::LeftParenthesis)
            }
            ')' => {
                self.position += 1;
                Ok(Token::RightParenthesis)
            }
            '0'..='9' => self.read_number(),
            'a'..='z' | 'A'..='Z' => self.read_identifier(),
            _ => Err(ParserError::Token(ch)),
        }
    }

    fn skip_whitespace(&mut self) {
        while self.position < self.input.len() && self.input[self.position].is_whitespace() {
            self.position += 1;
        }
    }

    fn read_number(&mut self) -> Result<Token> {
        let start = self.position;
        while self.position < self.input.len() && self.input[self.position].is_ascii_digit() {
            self.position += 1;
        }
        
        let number_str: String = self.input[start..self.position].iter().collect();
        let number: u16 = number_str.parse()?;

        if number == 0 {
            return Err(ParserError::ZeroValue);
        }

        Ok(Token::Number(number))
    }

    fn read_identifier(&mut self) -> Result<Token> {
        let start = self.position;
        while self.position < self.input.len() && self.input[self.position].is_alphabetic() {
            self.position += 1;
        }
        
        let identifier: String = self.input[start..self.position].iter().collect();
        match identifier.as_str() {
            "d" => Ok(Token::Dice),
            "kh" => Ok(Token::KeepHighest),
            "kl" => Ok(Token::KeepLowest),
            "dh" => Ok(Token::DropHighest),
            "dl" => Ok(Token::DropLowest),
            other => Err(ParserError::Identifier(other.into())),
        }
    }
}


#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test() {
        let expr = "2 * (3d4dl2 - 2d2)";
        let mut lexer = Lexer::new(expr);

        loop {
            let token = lexer.next_token().unwrap();

            match token {
                Token::Eof => break,
                other => dbg!(other)
            };
        };
    }
}
