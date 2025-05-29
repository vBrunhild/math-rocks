use crate::parser::error::*;


#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
    pub position: usize,
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
            _ => Err(ParserError::Token(ch))
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
    use proptest::prelude::*;
    use crate::parser::str_test_strategies::*;


    fn dice_modifier_strategy() -> impl Strategy<Value = Token> {
        prop_oneof![
            Just(Token::KeepHighest),
            Just(Token::KeepLowest),
            Just(Token::DropHighest),
            Just(Token::DropLowest),
        ]
    }

    proptest! {
        #[test]
        fn test_single_number_token(n in 1u16..=1000) {
            let mut lexer = Lexer::new(&n.to_string());
            let token = lexer.next_token().unwrap();

            prop_assert_eq!(token, Token::Number(n));
            prop_assert_eq!(lexer.next_token().unwrap(), Token::Eof);
        }

        #[test]
        fn test_binary_operators(op in "[+\\-*/]") {
            let mut lexer = Lexer::new(&op);
            let token = lexer.next_token().unwrap();

            let expected = match op.as_str() {
                "+" => Token::Plus,
                "-" => Token::Minus,
                "*" => Token::Multiply,
                "/" => Token::Divide,
                _ => unreachable!(),
            };

            prop_assert_eq!(token, expected);
            prop_assert_eq!(lexer.next_token().unwrap(), Token::Eof);
        }

        #[test]
        fn test_parenthesis(paren in "[()]") {
            let mut lexer = Lexer::new(&paren);
            let token = lexer.next_token().unwrap();

            let expected = match paren.as_str() {
                "(" => Token::LeftParenthesis,
                ")" => Token::RightParenthesis,
                _ => unreachable!(),
            };

            prop_assert_eq!(token, expected);
            prop_assert_eq!(lexer.next_token().unwrap(), Token::Eof);
        }

        #[test]
        fn test_dice_modifiers(modifier in "(kh|kl|dh|dl)") {
            let mut lexer = Lexer::new(&modifier);
            let token = lexer.next_token().unwrap();

            let expected = match modifier.as_str() {
                "kh" => Token::KeepHighest,
                "kl" => Token::KeepLowest,
                "dh" => Token::DropHighest,
                "dl" => Token::DropLowest,
                _ => unreachable!(),
            };

            prop_assert_eq!(token, expected);
            prop_assert_eq!(lexer.next_token().unwrap(), Token::Eof);
        }

        #[test]
        fn test_invalid_character(
            ch in any::<char>().prop_filter("remove", |c| {
                !c.is_ascii_digit() &&
                !c.is_ascii_alphabetic() &&
                !"+-*/()".contains(*c) &&
                !c.is_whitespace()
            })
        ) {
            let mut lexer = Lexer::new(&ch.to_string());
            let result = lexer.next_token();

            assert!(matches!(result, Err(ParserError::Token(_))));
        }

        #[test]
        fn test_invalid_identifier(
            prefix in "[a-zA-Z]",
            suffix in "[a-zA-Z]{1,5}"
        ) {
            let identifier = format!("{}{}", prefix, suffix);
            if matches!(identifier.as_str(), "d" | "kh" | "kl" | "dh" | "dl") {
                return Ok(());
            }

            let mut lexer = Lexer::new(&identifier);
            let result = lexer.next_token();

            assert!(matches!(result, Err(ParserError::Identifier(_))));
        }

        #[test]
        fn test_simple_dice_expression(count in 1u16..=1000, sides in 1u16..=1000) {
            let expr = format!("{}d{}", count, sides);
            let mut lexer = Lexer::new(&expr);

            let tokens: Vec<Token> = std::iter::from_fn(|| {
                match lexer.next_token() {
                    Ok(Token::Eof) => None,
                    Ok(token) => Some(token),
                    Err(_) => None,
                }
            }).collect();

            prop_assert_eq!(tokens, vec![
                Token::Number(count),
                Token::Dice,
                Token::Number(sides)
            ]);
        }

        #[test]
        fn test_dice_with_modifier(
            count in 1u16..=1000,
            sides in 1u16..=1000,
            modifier in dice_modifier_strategy(),
            mod_value in prop::option::of(1u16..=1000)
        ) {
            let modifier_str = match modifier {
                Token::KeepHighest => "kh",
                Token::KeepLowest => "kl",
                Token::DropHighest => "dh",
                Token::DropLowest => "dl",
                _ => unreachable!(),
            };

            let expr = match mod_value {
                Some(val) => format!("{}d{}{}{}", count, sides, modifier_str, val),
                None => format!("{}d{}{}", count, sides, modifier_str),
            };

            let mut lexer = Lexer::new(&expr);
            let mut expected_tokens = vec![
                Token::Number(count),
                Token::Dice,
                Token::Number(sides),
                modifier,
            ];

            if let Some(val) = mod_value {
                expected_tokens.push(Token::Number(val));
            }

            let tokens: Vec<Token> = std::iter::from_fn(|| {
                match lexer.next_token() {
                    Ok(Token::Eof) => None,
                    Ok(token) => Some(token),
                    Err(_) => None,
                }
            }).collect();

            prop_assert_eq!(tokens, expected_tokens);
        }

        #[test]
        fn test_complex_expression(expr in dice_expression_strategy()) {
            let mut lexer = Lexer::new(&expr);

            let mut token_count = 0;
            loop {
                match lexer.next_token() {
                    Ok(Token::Eof) => break,
                    Ok(_) => token_count += 1,
                    Err(e) => {
                        eprintln!("Failed to tokenize: {}", expr);
                        return Err(TestCaseError::Fail(format!("Tokenization error: {:?}", e).into()));
                    }
                }

                if token_count > 100 {
                    return Err(TestCaseError::Fail("Too many tokens generated".into()));
                }
            }

            prop_assert!(token_count > 0, "Expression should produce at least one token");
        }
    }

    #[test]
    fn test_zero_number_error() {
        let mut lexer = Lexer::new("0");
        let result = lexer.next_token();

        assert!(matches!(result, Err(ParserError::ZeroValue)));
    }

    #[test]
    fn test_dice_token() {
        let mut lexer = Lexer::new("d");

        let token = lexer.next_token().unwrap();
        let eof = lexer.next_token().unwrap();

        assert_eq!(token, Token::Dice);
        assert_eq!(eof, Token::Eof);
    }
}
