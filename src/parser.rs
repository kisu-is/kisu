use crate::ast::untyped::{self, BinaryOp, Binding, Expr, Ident, List, Num, Param, Str, UnaryOp};
use crate::lexer::{Token, TokenIter, TokenKind};
use crate::types::Type;
use bumpalo::Bump;
use bumpalo::collections::Vec;
use logos::Span;

pub use _hide_warnings::*;

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
            #[label]
            span: SourceSpan,
        },
        #[error("expected number, found {found:?}")]
        ExpectedNumber {
            found: TokenKind,
            #[label]
            span: SourceSpan,
        },
        #[error("expected string, found {found:?}")]
        ExpectedString {
            found: TokenKind,
            #[label]
            span: SourceSpan,
        },
        #[error("expected identifier, found {found:?}")]
        ExpectedIdentifier {
            found: TokenKind,
            #[label]
            span: SourceSpan,
        },
        #[error("invalid number")]
        InvalidNumber {
            #[label]
            span: SourceSpan,
        },
        #[error("expected EOF, found {found:?}")]
        ExpectedEof {
            found: TokenKind,
            #[label]
            span: SourceSpan,
        },
        #[error("expected expression, found {found:?}")]
        ExpectedExpr {
            found: TokenKind,
            #[label]
            span: SourceSpan,
        },
        #[error("{found:?} not allowed when 'terminating' feature is enabled")]
        NotTerminating {
            found: TokenKind,
            #[label]
            span: SourceSpan,
        },
    }
}

#[derive(Clone)]
pub struct Parser<'src, 'ast> {
    source: &'src str,
    lexer: TokenIter<'src>,
    current_token: Token,
    next_token: Token,
    bump: &'ast Bump,
}

impl<'src, 'ast> Parser<'src, 'ast> {
    pub fn new(lexer: TokenIter<'src>, source: &'src str, bump: &'ast Bump) -> Self {
        let mut parser = Self {
            source,
            lexer,
            current_token: Token::NONE,
            next_token: Token::NONE,
            bump,
        };

        parser.advance();
        parser.advance();
        parser
    }

    pub fn parse(&mut self) -> Result<untyped::Program<'ast>, Error> {
        let mut structs = Vec::new_in(self.bump);
        while self.check(&TokenKind::Struct) {
            structs.push(self.struct_def()?);
        }
        let expr = self.block(true)?;
        self.expect_eof()?;
        Ok(untyped::Program {
            structs,
            expr: expr.clone(),
        })
    }

    #[inline]
    fn advance(&mut self) {
        std::mem::swap(&mut self.next_token, &mut self.current_token);
        self.next_token = self.lexer.next().unwrap_or(Token {
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

    #[inline]
    pub fn consume(&mut self) -> Token {
        let mut token = Token::NONE;
        std::mem::swap(&mut token, &mut self.current_token);
        std::mem::swap(&mut self.next_token, &mut self.current_token);
        self.next_token = self.lexer.next().unwrap_or(Token {
            kind: TokenKind::Eof,
            span: self.token_span().clone(),
        });
        token
    }

    #[inline]
    pub fn is_eof(&self) -> bool {
        self.current().kind == TokenKind::Eof && self.next().kind == TokenKind::Eof
    }

    #[inline]
    fn token_kind(&self) -> &TokenKind {
        &self.current().kind
    }

    #[inline]
    fn token_span(&self) -> &Span {
        &self.current().span
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

    fn number(&mut self) -> Result<&'ast Expr<'ast>, Error> {
        let token = self.expect(TokenKind::Number)?;
        let span = token.span.clone();
        let lexeme = &self.source[span.start..span.end];
        let value = lexeme.parse::<f64>().map_err(|_| Error::InvalidNumber {
            span: span.clone().into(),
        })?;
        Ok(self.bump.alloc(Expr::Number(Num(value, span))))
    }

    fn string(&mut self) -> Result<&'ast Expr<'ast>, Error> {
        let token = self.expect(TokenKind::String)?;
        let span = token.span.clone();
        let lexeme = &self.source[span.start..span.end];

        // remove quotes
        let content = &lexeme[1..lexeme.len() - 1];
        Ok(self
            .bump
            .alloc(Expr::String(Str(content.to_string(), span))))
    }

    fn ident(&mut self) -> Result<Ident, Error> {
        let token = self.expect(TokenKind::Ident)?;
        let span = token.span.clone();
        let name = &self.source[span.start..span.end];

        Ok(untyped::Ident {
            name: name.to_string(),
            span,
        })
    }

    fn ident_expr(&mut self) -> Result<&'ast Expr<'ast>, Error> {
        let ident = self.ident()?;
        Ok(self.bump.alloc(Expr::Ident(ident)))
    }

    fn type_ident(&mut self) -> Result<Type, Error> {
        let token = self.expect(TokenKind::TypeIdent)?;
        let span = token.span.clone();
        let name = &self.source[span.start..span.end];

        Ok(match name {
            "Number" => Type::Number,
            "String" => Type::String,
            "Bool" => Type::Bool,
            _ => Type::Struct(crate::ast::typed::TypeIdent {
                name: name.to_string(),
                span,
                ty: Box::new(Type::Var(0)),
            }),
        })
    }

    fn list_type(&mut self) -> Result<Type, Error> {
        self.expect(TokenKind::BracketL)?;
        let ty = self.type_expr()?;
        self.expect(TokenKind::BracketR)?;
        Ok(Type::List(Box::new(ty)))
    }

    fn lambda_type(&mut self) -> Result<Type, Error> {
        self.expect(TokenKind::Fn)?;

        let mut types = vec![];
        while !self.check(&TokenKind::Arrow) {
            let param_ty = self.type_expr()?;
            types.push(param_ty);
        }

        self.expect(TokenKind::Arrow)?;
        let ret_ty = self.type_expr()?;

        // desugar multi param lambdas
        let mut result = Type::Lambda(Box::new(types.pop().unwrap()), Box::new(ret_ty.clone()));
        for ty in types {
            if let Type::Lambda(_, rty) = &mut result {
                **rty = Type::Lambda(Box::new(ty), Box::new(ret_ty.clone()));
            }
        }

        Ok(result)
    }

    fn type_expr(&mut self) -> Result<Type, Error> {
        match self.token_kind() {
            TokenKind::ParenL => {
                self.advance();
                let ty = self.type_expr()?;
                self.expect(TokenKind::ParenR)?;
                Ok(ty)
            }
            TokenKind::TypeIdent => self.type_ident(),
            TokenKind::BracketL => self.list_type(),
            TokenKind::Fn => self.lambda_type(),
            _ => Err(Error::UnexpectedToken {
                expected: TokenKind::TypeIdent,
                found: self.token_kind().clone(),
                span: self.token_span().clone().into(),
            }),
        }
    }

    fn expect_eof(&mut self) -> Result<(), Error> {
        if self.current().kind == TokenKind::Eof {
            Ok(())
        } else {
            let token = self.current();
            Err(Error::ExpectedEof {
                found: token.kind.clone(),
                span: token.span.clone().into(),
            })
        }
    }

    fn check_key(&mut self) -> bool {
        self.check(&TokenKind::Ident) || self.check(&TokenKind::String)
    }

    fn if_expr(&mut self) -> Result<&'ast Expr<'ast>, Error> {
        let if_token = self.expect(TokenKind::If)?;
        let cond = self.expr()?;
        self.expect(TokenKind::Then)?;
        let then_expr = self.expr()?;
        let else_token = self.expect(TokenKind::Else)?;
        let else_expr = self.expr()?;

        Ok(self.bump.alloc(Expr::IfExpr {
            cond,
            then_expr,
            else_expr,
            span: if_token.span.start..else_token.span.end,
        }))
    }

    fn key(&mut self) -> Result<Ident, Error> {
        if let Ok(ident) = self.ident() {
            Ok(ident)
        } else if let Ok(Expr::String(str)) = self.string() {
            Ok(Ident {
                name: str.0.clone(),
                span: str.1.clone(),
            })
        } else {
            Err(Error::ExpectedIdentifier {
                found: self.token_kind().clone(),
                span: self.token_span().clone().into(),
            })
        }
    }

    fn constraint(&mut self) -> Result<Option<Type>, Error> {
        if self.expect(TokenKind::Colon).is_err() {
            return Ok(None);
        };

        Ok(Some(self.type_expr()?))
    }

    fn block(&mut self, top_level: bool) -> Result<&'ast Expr<'ast>, Error> {
        let mut start = self.current().span.start;

        if !top_level {
            start = self.expect(TokenKind::ParenL)?.span.end;
        }

        let mut bindings = Vec::new_in(self.bump);

        while {
            let is_normal = self.check_key()
                && (self.check_next(&TokenKind::Assign) || self.check_next(&TokenKind::Colon));

            let is_rec = self.check(&TokenKind::Rec);

            is_normal || is_rec
        } {
            let kind = if let Some(rec) = self.check_consume(&TokenKind::Rec) {
                if cfg!(feature = "terminating") {
                    return Err(Error::NotTerminating {
                        found: rec.kind,
                        span: rec.span.into(),
                    });
                };
                untyped::BindingKind::Rec
            } else {
                untyped::BindingKind::Normal
            };

            let key = self.key()?;
            let constraint = self.constraint()?;

            let expr = if self.check_consume(&TokenKind::Assign).is_some() {
                self.expr()?
            } else {
                self.bump.alloc(Expr::Ident(key.clone()))
            };

            let span = key.span.start..(self.expect(TokenKind::Semicolon)?.span.end);

            bindings.push(Binding {
                kind,
                ident: key,
                constraint,
                expr,
                span,
            });
        }

        let expr_result = self.expr()?;
        let mut end = expr_result.span().end;

        if !top_level {
            end = self.expect(TokenKind::ParenR)?.span.end;
        }

        Ok(self.bump.alloc(Expr::Block {
            bindings,
            expr: expr_result,
            span: start..end,
        }))
    }

    fn struct_expr(&mut self, type_name: untyped::TypeIdent) -> Result<&'ast Expr<'ast>, Error> {
        let start = self.expect(TokenKind::BraceL)?.span.start;
        let mut fields = Vec::new_in(self.bump);

        while !self.check(&TokenKind::BraceR) {
            let key = self.key()?;
            let constraint = self.constraint()?;

            let expr = if self.check_consume(&TokenKind::Assign).is_some() {
                self.expr()?
            } else {
                self.bump.alloc(Expr::Ident(key.clone()))
            };

            fields.push(untyped::Binding {
                kind: untyped::BindingKind::Normal,
                span: key.span.start..expr.span().end,
                constraint,
                ident: key,
                expr,
            });

            if self.check_consume(&TokenKind::Semicolon).is_none()
                && !self.check(&TokenKind::BraceR)
            {
                return Err(Error::UnexpectedToken {
                    expected: TokenKind::Semicolon,
                    found: self.token_kind().clone(),
                    span: self.token_span().clone().into(),
                });
            }
        }

        let end = self.expect(TokenKind::BraceR)?.span.end;

        Ok(self.bump.alloc(Expr::Struct {
            type_name,
            fields,
            span: start..end,
        }))
    }

    fn lambda(&mut self) -> Result<&'ast Expr<'ast>, Error> {
        let start = self.expect(TokenKind::Pipe)?.span.start;

        let mut params = Vec::new_in(self.bump);
        if !self.check(&TokenKind::Pipe) {
            loop {
                let key = self.key()?;
                let constraint = self.constraint()?;

                params.push(Param {
                    span: key.span.clone(),
                    constraint,
                    ident: key,
                    expr: None,
                });

                if self.check_consume(&TokenKind::Comma).is_none() {
                    break;
                }
            }
        }

        self.expect(TokenKind::Pipe)?;
        self.expect(TokenKind::Colon)?;
        let body = self.block(true)?;
        let span = start..body.span().end;

        Ok(self.bump.alloc(Expr::Lambda { params, body, span }))
    }

    fn list(&mut self) -> Result<&'ast Expr<'ast>, Error> {
        let start = self.expect(TokenKind::BracketL)?.span.start;

        let mut exprs = Vec::new_in(self.bump);

        while !self.check(&TokenKind::BracketR) {
            let expr = self.expr()?;
            exprs.push(expr.clone());
            if self.check_consume(&TokenKind::Comma).is_none() && !self.check(&TokenKind::BracketR)
            {
                return Err(Error::UnexpectedToken {
                    expected: TokenKind::Comma,
                    found: self.token_kind().clone(),
                    span: self.token_span().clone().into(),
                });
            }
        }

        let span = start..self.expect(TokenKind::BracketR)?.span.end;

        Ok(self.bump.alloc(Expr::List(List { exprs, span })))
    }

    fn atom(&mut self) -> Result<&'ast Expr<'ast>, Error> {
        if self.check(&TokenKind::TypeIdent) && self.check_next(&TokenKind::BraceL) {
            let type_ident_token = self.expect(TokenKind::TypeIdent)?;
            let type_name = untyped::TypeIdent {
                name: self.source[type_ident_token.span.start..type_ident_token.span.end]
                    .to_string(),
                span: type_ident_token.span,
            };
            return self.struct_expr(type_name);
        }

        let expr_result = match self.token_kind() {
            TokenKind::Number => self.number(),
            TokenKind::String => self.string(),
            TokenKind::True => {
                self.consume();
                let expr: &'ast Expr<'ast> = self.bump.alloc(Expr::Bool(true));
                Ok(expr)
            }
            TokenKind::False => {
                self.consume();
                let expr: &'ast Expr<'ast> = self.bump.alloc(Expr::Bool(false));
                Ok(expr)
            }
            TokenKind::Ident => self.ident_expr(),
            TokenKind::BracketL => self.list(),
            TokenKind::ParenL => self.block(false),
            TokenKind::Pipe => self.lambda(),
            _ => Err(Error::UnexpectedToken {
                expected: self.token_kind().clone(),
                found: self.token_kind().clone(),
                span: self.token_span().clone().into(),
            }),
        }?;

        Ok(expr_result)
    }

    fn check_atom(&self) -> bool {
        matches!(
            self.token_kind(),
            TokenKind::Number
                | TokenKind::String
                | TokenKind::Ident
                | TokenKind::True
                | TokenKind::False
                | TokenKind::BracketL
                | TokenKind::ParenL
                | TokenKind::Pipe
        ) || (self.check(&TokenKind::TypeIdent) && self.check_next(&TokenKind::BraceL))
    }

    pub fn expr(&mut self) -> Result<&'ast Expr<'ast>, Error> {
        if self.is_eof() {
            return Err(Error::ExpectedExpr {
                found: self.current().kind.clone(),
                span: self.token_span().clone().into(),
            });
        }
        self.binary_expr(0)
    }

    fn binary_expr(&mut self, min_precedence: u8) -> Result<&'ast Expr<'ast>, Error> {
        let mut lhs = self.unary_expr()?;

        loop {
            let op_precedence = if let Some(op) = self.binary_op() {
                op.precedence()
            } else if self.check_atom() {
                1
            } else {
                break;
            };

            if op_precedence < min_precedence {
                break;
            }

            if let Some(op) = self.binary_op() {
                self.consume();
                if op == BinaryOp::Dot {
                    let key = self.key()?;
                    lhs = self.bump.alloc(Expr::StructAccess {
                        span: lhs.span().start..key.span.end,
                        expr: lhs,
                        ident: key,
                    });
                    continue;
                }

                let rhs = self.binary_expr(op_precedence + 1)?;
                lhs = self.bump.alloc(Expr::Binary {
                    op,
                    span: rhs.span().start..rhs.span().end,
                    lhs,
                    rhs,
                });
                continue;
            }

            let rhs = self.binary_expr(op_precedence + 1)?;
            lhs = self.bump.alloc(Expr::App {
                span: rhs.span().start..rhs.span().end,
                lhs,
                rhs,
            });
        }

        Ok(lhs)
    }

    fn unary_expr(&mut self) -> Result<&'ast Expr<'ast>, Error> {
        if self.check(&TokenKind::If) {
            return self.if_expr();
        }
        if let Some(op) = self.unary_op() {
            let op_token = self.consume();
            let expr = self.unary_expr()?;
            let span = op_token.span.start..expr.span().end;
            return Ok(self.bump.alloc(Expr::Unary { op, expr, span }));
        }
        self.atom()
    }

    fn struct_def(&mut self) -> Result<untyped::StructDef<'ast>, Error> {
        let start = self.expect(TokenKind::Struct)?.span.start;
        let ident = self.expect(TokenKind::TypeIdent)?;
        let name = untyped::TypeIdent {
            name: self.source[ident.span.start..ident.span.end].to_string(),
            span: ident.span,
        };

        self.expect(TokenKind::BraceL)?;

        let mut fields = Vec::new_in(self.bump);
        while !self.check(&TokenKind::BraceR) {
            fields.push(self.struct_field()?);
            if self.check_consume(&TokenKind::Comma).is_none() && !self.check(&TokenKind::BraceR) {
                return Err(Error::UnexpectedToken {
                    expected: TokenKind::Comma,
                    found: self.token_kind().clone(),
                    span: self.token_span().clone().into(),
                });
            }
        }
        let end = self.expect(TokenKind::BraceR)?.span.end;

        Ok(untyped::StructDef {
            name,
            fields,
            span: start..end,
        })
    }

    fn struct_field(&mut self) -> Result<untyped::StructField, Error> {
        let ident = self.key()?;
        self.expect(TokenKind::Colon)?;
        let ty = self.type_expr()?;
        let span = ident.span.clone();
        Ok(untyped::StructField { ident, ty, span })
    }
}
