use crate::ast::{self, BinaryOp, Binding, Expr, Ident, List, Param, UnaryOp};
use crate::lexer::{Token, TokenIter, TokenKind};
use logos::Span;

pub use _hide_warnings::*;

// weird warning bug with the miette macros
mod _hide_warnings {
    #![allow(unused_assignments)]

    use crate::lexer::TokenKind;
    use miette::{Diagnostic, SourceSpan};

    #[derive(thiserror::Error, Diagnostic, Debug)]
    #[diagnostic(code(kisu::parser))]
    pub enum Error {
        #[error("unexpected token (expected {expected:?}, found {found:?})")]
        UnexpectedToken {
            expected: TokenKind,
            found: TokenKind,
            #[label("unexpected token")]
            span: SourceSpan,
        },
        #[error("expected number, found {found:?}")]
        ExpectedNumber {
            found: TokenKind,
            #[label("expected a number")]
            span: SourceSpan,
        },
        #[error("expected string, found {found:?}")]
        ExpectedString {
            found: TokenKind,
            #[label("expected a string")]
            span: SourceSpan,
        },
        #[error("expected identifier, found {found:?}")]
        ExpectedIdentifier {
            found: TokenKind,
            #[label("expected an identifier")]
            span: SourceSpan,
        },
        #[error("invalid number")]
        InvalidNumber {
            #[label("invalid number")]
            span: SourceSpan,
        },
        #[error("expected EOF, found {found:?}")]
        ExpectedEof {
            found: TokenKind,
            #[label("expected end of file")]
            span: SourceSpan,
        },
        #[error("expected expression, found {found:?}")]
        ExpectedExpr {
            found: TokenKind,
            #[label("expected expression")]
            span: SourceSpan,
        },
        #[error("invalid operand for operator {op:?}")]
        InvalidOperand {
            op: TokenKind,
            #[label("invalid operand")]
            span: SourceSpan,
        },
    }
}

#[derive(Clone)]
pub struct Parser<'a> {
    source: &'a str,
    tokens: TokenIter<'a>,
    current_token: Token,
    next_token: Token,
}

impl<'a> Parser<'a> {
    pub fn new(lexer: TokenIter<'a>, source: &'a str) -> Self {
        let mut parser = Self {
            source,
            tokens: lexer,
            current_token: Token::NONE,
            next_token: Token::NONE,
        };
        parser.advance();
        parser.advance();

        parser
    }

    #[inline]
    fn advance(&mut self) {
        std::mem::swap(&mut self.next_token, &mut self.current_token);
        self.next_token = self.tokens.next().unwrap_or(Token {
            kind: TokenKind::Eof,
            span: self.token_span().clone(),
        });
    }

    #[inline]
    pub fn current(&self) -> &Token {
        &self.current_token
    }

    #[inline]
    pub fn next(&self) -> &Token {
        &self.next_token
    }

    #[inline]
    pub fn check(&self, kind: &crate::lexer::TokenKind) -> bool {
        &self.current_token.kind == kind
    }

    #[inline]
    pub fn check_next(&self, kind: &crate::lexer::TokenKind) -> bool {
        &self.next_token.kind == kind
    }

    pub fn check_consume(&mut self, kind: &crate::lexer::TokenKind) -> Option<Token> {
        if self.check(kind) {
            let token = self.consume();
            Some(token)
        } else {
            None
        }
    }

    pub fn consume(&mut self) -> Token {
        let mut token = Token::NONE;
        std::mem::swap(&mut token, &mut self.current_token);
        std::mem::swap(&mut self.next_token, &mut self.current_token);
        self.next_token = self.tokens.next().unwrap_or(Token {
            kind: TokenKind::Eof,
            span: self.token_span().clone(),
        });
        token
    }

    #[inline]
    pub fn is_eof(&self) -> bool {
        self.current_token.kind == TokenKind::Eof && self.next_token.kind == TokenKind::Eof
    }

    #[inline]
    fn token_kind(&self) -> &TokenKind {
        &self.current_token.kind
    }

    #[inline]
    fn token_span(&self) -> &Span {
        &self.current_token.span
    }

    fn binary_op(&self) -> Option<BinaryOp> {
        match self.token_kind() {
            TokenKind::Add => Some(BinaryOp::Add),
            TokenKind::Sub => Some(BinaryOp::Sub),
            TokenKind::Mul => Some(BinaryOp::Mul),
            TokenKind::Div => Some(BinaryOp::Div),
            TokenKind::Eq => Some(BinaryOp::Eq),
            TokenKind::NotEq => Some(BinaryOp::NotEq),
            TokenKind::Lt => Some(BinaryOp::Lt),
            TokenKind::Gt => Some(BinaryOp::Gt),
            TokenKind::LtEq => Some(BinaryOp::LtEq),
            TokenKind::GtEq => Some(BinaryOp::GtEq),
            TokenKind::Dot => Some(BinaryOp::Dot),
            _ => None,
        }
    }

    fn unary_op(&self) -> Option<UnaryOp> {
        match self.token_kind() {
            TokenKind::Sub => Some(UnaryOp::Neg),
            TokenKind::Not => Some(UnaryOp::Not),
            _ => None,
        }
    }

    fn expect(&mut self, kind: TokenKind) -> Result<Token, Error> {
        match self.check_consume(&kind) {
            Some(token) => Ok(token),
            None => Err(Error::UnexpectedToken {
                expected: kind,
                found: self.token_kind().clone(),
                span: self.token_span().clone().into(),
            }),
        }
    }

    fn number(&mut self) -> Result<Expr, Error> {
        if let Some(token) = self.check_consume(&TokenKind::Number) {
            let span = token.span;
            let lexeme = &self.source[span.start..span.end];
            let value = lexeme.parse::<f64>().map_err(|_| Error::InvalidNumber {
                span: span.clone().into(),
            })?;
            Ok(Expr::Number(value.into()))
        } else {
            Err(Error::ExpectedNumber {
                found: self.token_kind().clone(),
                span: self.token_span().clone().into(),
            })
        }
    }

    fn string(&mut self) -> Result<Expr, Error> {
        if let Some(token) = self.check_consume(&TokenKind::String) {
            let span = token.span;
            let lexeme = &self.source[span.start..span.end];

            // remove quotes
            let content = &lexeme[1..lexeme.len() - 1];
            Ok(Expr::String(content.into()))
        } else {
            Err(Error::ExpectedString {
                found: self.token_kind().clone(),
                span: self.token_span().clone().into(),
            })
        }
    }

    fn ident(&mut self) -> Result<Expr, Error> {
        if let Some(token) = self.check_consume(&TokenKind::Ident) {
            let span = token.span;
            let name = &self.source[span.start..span.end];

            Ok(Expr::Ident(ast::Ident {
                name: name.to_string(),
            }))
        } else {
            Err(Error::ExpectedIdentifier {
                found: self.token_kind().clone(),
                span: self.token_span().clone().into(),
            })
        }
    }

    fn expect_eof(&mut self) -> Result<(), Error> {
        if self.current().kind == TokenKind::Eof {
            Ok(())
        } else {
            let token = &self.current_token;
            Err(Error::ExpectedEof {
                found: token.kind.clone(),
                span: token.span.clone().into(),
            })
        }
    }

    fn check_key(&mut self) -> bool {
        self.check(&TokenKind::Ident) || self.check(&TokenKind::String)
    }

    fn key(&mut self) -> Result<Ident, Error> {
        if let Ok(Expr::Ident(ident)) = self.ident() {
            Ok(ident)
        } else if let Ok(Expr::String(str)) = self.string() {
            Ok(Ident { name: str.0 })
        } else {
            Err(Error::ExpectedIdentifier {
                found: self.token_kind().clone(),
                span: self.token_span().clone().into(),
            })
        }
    }

    fn block(&mut self, top_level: bool) -> Result<Expr, Error> {
        if !top_level {
            self.expect(TokenKind::ParenL)?;
        }

        let mut bindings = Vec::new();

        while self.check_key()
            && (self.check_next(&TokenKind::Assign) || self.check_next(&TokenKind::Semicolon))
        {
            let key = self.key()?;

            // desugar inherit syntax
            let expr = if self.check_consume(&TokenKind::Assign).is_some() {
                self.expr()?
            } else {
                Expr::Ident(key.clone())
            };

            self.expect(TokenKind::Semicolon)?;

            bindings.push(Binding {
                ident: key,
                expr: Box::new(expr),
            });
        }

        let expr = self.expr()?;
        if !top_level {
            self.expect(TokenKind::ParenR)?;
        }

        Ok(Expr::Block {
            bindings,
            expr: Box::new(expr),
        })
    }

    fn map_and_lambda(&mut self) -> Result<Expr, Error> {
        self.expect(TokenKind::BraceL)?;

        let mut fields = Vec::new();
        let mut trailing_token = None;

        while self.check_key() {
            let key = self.key()?;
            let expr = if self.check_consume(&TokenKind::Assign).is_some() {
                Some(Box::new(self.expr()?))
            } else {
                None
            };

            fields.push(Param { ident: key, expr });

            if self.check(&TokenKind::Semicolon) {
                self.advance();
            } else {
                trailing_token = Some(self.current_token.clone());
                if self.check(&TokenKind::BraceR) {
                    break;
                } else {
                    return Err(Error::UnexpectedToken {
                        expected: TokenKind::Semicolon,
                        found: self.token_kind().clone(),
                        span: self.token_span().clone().into(),
                    });
                }
            }
        }

        self.expect(TokenKind::BraceR)?;
        if self.check_consume(&TokenKind::Colon).is_some() {
            let body = self.expr()?;
            Ok(Expr::Lambda {
                params: fields,
                body: Box::new(body),
            })
        } else {
            if let Some(trailing_token) = trailing_token
                && !fields.is_empty()
            {
                return Err(Error::UnexpectedToken {
                    expected: TokenKind::Semicolon,
                    found: trailing_token.kind,
                    span: trailing_token.span.into(),
                });
            }
            Ok(Expr::Map {
                bindings: fields
                    .into_iter()
                    .map(|f| Binding {
                        ident: f.ident.clone(),
                        expr: f.expr.unwrap_or_else(|| Box::new(Expr::Ident(f.ident))),
                    })
                    .collect(),
            })
        }
    }

    fn list(&mut self) -> Result<Expr, Error> {
        self.expect(TokenKind::BracketL)?;
        let mut exprs = Vec::new();

        while !self.check(&TokenKind::BracketR) {
            let expr = self.expr()?;
            exprs.push(expr);
            if self.check_consume(&TokenKind::Semicolon).is_none()
                && self.check_next(&TokenKind::BracketR)
            {
                break;
            };
        }

        self.expect(TokenKind::BracketR)?;
        Ok(Expr::List(List { exprs }))
    }

    fn atom(&mut self) -> Result<Expr, Error> {
        match self.token_kind() {
            TokenKind::Number => self.number(),
            TokenKind::String => self.string(),
            TokenKind::Ident => self.ident(),
            TokenKind::BracketL => self.list(),
            TokenKind::ParenL => self.block(false),
            TokenKind::BraceL => self.map_and_lambda(),
            _ => Err(Error::UnexpectedToken {
                expected: self.token_kind().clone(),
                found: self.token_kind().clone(),
                span: self.token_span().clone().into(),
            }),
        }
    }

    pub fn expr(&mut self) -> Result<Expr, Error> {
        if self.is_eof() {
            return Err(Error::ExpectedExpr {
                found: self.current().kind.clone(),
                span: self.token_span().clone().into(),
            });
        }
        self.binary_expr(0)
    }

    fn binary_expr(&mut self, min_precedence: u8) -> Result<Expr, Error> {
        let mut lhs = self.unary_expr()?;

        while let Some(op) = self.binary_op() {
            let precedence = op.precedence();

            if precedence < min_precedence {
                break;
            }

            let op_token = self.consume();

            if op == BinaryOp::Dot {
                let key = self.key()?;

                lhs = Expr::MapAccess {
                    expr: Box::new(lhs),
                    ident: key,
                };
            } else if let Ok(rhs) = self.binary_expr(precedence + 1) {
                lhs = Expr::Binary {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                };
            } else {
                return Err(Error::InvalidOperand {
                    op: op_token.kind,
                    span: op_token.span.into(),
                });
            }
        }

        Ok(lhs)
    }

    fn app(&mut self, mut func: Expr) -> Result<Expr, Error> {
        loop {
            match self.token_kind() {
                TokenKind::BraceL | TokenKind::String | TokenKind::Number => {
                    let arg = self.atom()?;
                    func = Expr::App {
                        lhs: Box::new(func),
                        rhs: Box::new(arg),
                    };
                }
                TokenKind::Ident => {
                    // make sure its not a lambda
                    if !self.check_next(&TokenKind::Colon) {
                        let arg = self.atom()?;
                        func = Expr::App {
                            lhs: Box::new(func),
                            rhs: Box::new(arg),
                        };
                    }
                }
                _ => break,
            }
        }
        Ok(func)
    }

    fn unary_expr(&mut self) -> Result<Expr, Error> {
        if let Some(op) = self.unary_op() {
            self.consume();

            let expr = self.unary_expr()?;

            let func = Expr::Unary {
                op,
                expr: Box::new(expr),
            };
            return self.app(func);
        }

        let atom_expr = self.atom()?;
        self.app(atom_expr)
    }

    pub fn parse(&mut self) -> Result<Expr, Error> {
        let expr = self.block(true)?;
        self.expect_eof()?;
        Ok(expr)
    }
}
