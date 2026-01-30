use crate::ast::{BinaryOp, Binding, Expr, UnaryOp};
use crate::lexer::{Token, TokenIter, TokenKind};
use logos::Span;

#[derive(thiserror::Error, Debug, PartialEq)]
pub enum Error {
    #[error("unexpected token (expected {expected:?}, found {found:?})")]
    UnexpectedToken {
        expected: TokenKind,
        found: Option<TokenKind>,
        span: Option<Span>,
    },
    #[error("expected number, found {found:?}")]
    ExpectedNumber {
        found: Option<TokenKind>,
        span: Option<Span>,
    },
    #[error("expected string, found {found:?}")]
    ExpectedString {
        found: Option<TokenKind>,
        span: Option<Span>,
    },
    #[error("expected identifier, found {found:?}")]
    ExpectedIdentifier {
        found: Option<TokenKind>,
        span: Option<Span>,
    },

    #[error("invalid number")]
    InvalidNumber { span: Span },

    #[error("expected EOF, found {found:?})")]
    ExpectedEof { found: TokenKind, span: Span },
}

pub struct Parser<'a> {
    source: &'a str,
    tokens: TokenIter<'a>,
    current_token: Option<Token>,
    next_token: Option<Token>,
}

impl<'a> Parser<'a> {
    pub fn new(lexer: TokenIter<'a>, source: &'a str) -> Self {
        let mut parser = Self {
            source,
            tokens: lexer,
            current_token: None,
            next_token: None,
        };

        parser.advance();
        parser.advance();

        parser
    }

    #[inline]
    fn advance(&mut self) {
        self.current_token = self.next_token.take();
        self.next_token = self.tokens.next();
    }

    #[inline]
    pub fn current(&self) -> Option<&Token> {
        self.current_token.as_ref()
    }

    #[inline]
    pub fn next(&self) -> Option<&Token> {
        self.next_token.as_ref()
    }

    #[inline]
    pub fn check(&self, kind: &crate::lexer::TokenKind) -> bool {
        self.current_token
            .as_ref()
            .is_some_and(|token| &token.kind == kind)
    }

    #[inline]
    pub fn check_next(&self, kind: &crate::lexer::TokenKind) -> bool {
        self.next_token
            .as_ref()
            .is_some_and(|token| &token.kind == kind)
    }

    pub fn check_consume(&mut self, kind: &crate::lexer::TokenKind) -> Option<Token> {
        if self.check(kind) {
            let token = self.current_token.take();
            self.advance();
            token
        } else {
            None
        }
    }

    pub fn consume(&mut self) -> Option<Token> {
        let token = self.current_token.take();
        self.advance();
        token
    }

    #[inline]
    pub fn is_eof(&self) -> bool {
        self.current_token.is_none() && self.next_token.is_none()
    }

    #[inline]
    fn token_kind(&self) -> Option<&TokenKind> {
        self.current_token.as_ref().map(|t| &t.kind)
    }

    #[inline]
    fn token_span(&self) -> Option<Span> {
        self.current_token.as_ref().map(|t| t.span.clone())
    }

    fn binary_op(&self) -> Option<BinaryOp> {
        match self.token_kind() {
            Some(TokenKind::Add) => Some(BinaryOp::Add),
            Some(TokenKind::Sub) => Some(BinaryOp::Sub),
            Some(TokenKind::Mul) => Some(BinaryOp::Mul),
            Some(TokenKind::Div) => Some(BinaryOp::Div),
            Some(TokenKind::Eq) => Some(BinaryOp::Eq),
            Some(TokenKind::NotEq) => Some(BinaryOp::NotEq),
            Some(TokenKind::Lt) => Some(BinaryOp::Lt),
            Some(TokenKind::Gt) => Some(BinaryOp::Gt),
            Some(TokenKind::LtEq) => Some(BinaryOp::LtEq),
            Some(TokenKind::GtEq) => Some(BinaryOp::GtEq),
            _ => None,
        }
    }

    fn unary_op(&self) -> Option<UnaryOp> {
        match self.token_kind() {
            Some(TokenKind::Sub) => Some(UnaryOp::Neg),
            Some(TokenKind::Not) => Some(UnaryOp::Not),
            _ => None,
        }
    }

    fn expect(&mut self, kind: TokenKind) -> Result<Token, Error> {
        match self.check_consume(&kind) {
            Some(token) => Ok(token),
            None => Err(Error::UnexpectedToken {
                expected: kind,
                found: self.token_kind().cloned(),
                span: self.token_span(),
            }),
        }
    }

    fn number(&mut self) -> Result<Expr, Error> {
        if let Some(TokenKind::Number) = self.token_kind() {
            let token = self.consume().unwrap();
            let span = token.span;
            let lexeme = &self.source[span.start..span.end];
            let value = lexeme
                .parse::<f64>()
                .map_err(|_| Error::InvalidNumber { span: span.clone() })?;
            Ok(Expr::Number(value))
        } else {
            Err(Error::ExpectedNumber {
                found: self.token_kind().cloned(),
                span: self.token_span(),
            })
        }
    }

    fn string(&mut self) -> Result<Expr, Error> {
        if let Some(TokenKind::String) = self.token_kind() {
            let token = self.consume().unwrap();
            let span = token.span;
            let lexeme = &self.source[span.start..span.end];

            // remove quotes
            let content = &lexeme[1..lexeme.len() - 1];
            Ok(Expr::String(content.to_string()))
        } else {
            Err(Error::ExpectedString {
                found: self.token_kind().cloned(),
                span: self.token_span(),
            })
        }
    }

    fn ident(&mut self) -> Result<Expr, Error> {
        if let Some(TokenKind::Ident) = self.token_kind() {
            let token = self.consume().unwrap();
            let span = token.span;
            let name = &self.source[span.start..span.end];
            Ok(Expr::Ident(name.to_string()))
        } else {
            Err(Error::ExpectedIdentifier {
                found: self.token_kind().cloned(),
                span: self.token_span(),
            })
        }
    }

    fn expect_eof(&mut self) -> Result<(), Error> {
        if self.is_eof() {
            Ok(())
        } else {
            let token = self.current_token.as_ref().unwrap();
            Err(Error::ExpectedEof {
                found: token.kind.clone(),
                span: token.span.clone(),
            })
        }
    }

    fn paren_expr(&mut self) -> Result<Expr, Error> {
        self.expect(TokenKind::ParenL)?;
        let expr = self.expr()?;
        self.expect(TokenKind::ParenR)?;
        Ok(Expr::Paren(Box::new(expr)))
    }

    fn block(&mut self) -> Result<Expr, Error> {
        self.expect(TokenKind::BraceL)?;

        let mut bindings = Vec::new();

        while self.check(&TokenKind::Ident) && self.check_next(&TokenKind::Assign) {
            let name = match self.ident()? {
                Expr::Ident(name) => name,
                _ => unreachable!(),
            };
            self.expect(TokenKind::Assign)?;
            let expr = self.expr()?;
            self.expect(TokenKind::Semicolon)?;

            bindings.push(Binding {
                name,
                expr: Box::new(expr),
            });
        }

        if self.check_consume(&TokenKind::BraceR).is_some() {
            return Ok(Expr::Map { bindings });
        }

        let expr = self.expr()?;
        self.expect(TokenKind::BraceR)?;

        Ok(Expr::Block {
            bindings,
            expr: Box::new(expr),
        })
    }

    fn atom(&mut self) -> Result<Expr, Error> {
        match self.token_kind() {
            Some(TokenKind::Number) => self.number(),
            Some(TokenKind::String) => self.string(),
            Some(TokenKind::Ident) => self.ident(),
            Some(TokenKind::ParenL) => self.paren_expr(),
            Some(TokenKind::BraceL) => self.block(),
            _ => Err(Error::UnexpectedToken {
                expected: TokenKind::Eof,
                found: self.token_kind().cloned(),
                span: self.token_span(),
            }),
        }
    }

    pub fn expr(&mut self) -> Result<Expr, Error> {
        self.binary_expr(0)
    }

    fn binary_expr(&mut self, min_precedence: u8) -> Result<Expr, Error> {
        let mut lhs = self.unary_expr()?;

        while let Some(op) = self.binary_op() {
            let precedence = op.precedence();

            if precedence < min_precedence {
                break;
            }

            self.consume();

            let rhs = self.binary_expr(precedence + 1)?;

            lhs = Expr::Binary {
                op,
                left: Box::new(lhs),
                right: Box::new(rhs),
            };
        }

        Ok(lhs)
    }

    fn unary_expr(&mut self) -> Result<Expr, Error> {
        if let Some(op) = self.unary_op() {
            self.consume();

            let expr = self.unary_expr()?;

            return Ok(Expr::Unary {
                op,
                expr: Box::new(expr),
            });
        }

        self.atom()
    }

    pub fn parse_program(&mut self) -> Result<Expr, Error> {
        let expr = self.expr()?;
        self.expect_eof()?;
        Ok(expr)
    }
}
