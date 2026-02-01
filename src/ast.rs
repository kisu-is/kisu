use std::ops::{Add, Div, Mul, Sub};

use crate::lexer::TokenKind;

#[derive(Debug, Clone, PartialEq)]
pub struct Ident {
    pub name: String,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Binding {
    pub ident: Ident,
    pub expr: Box<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Str(pub String);

impl From<&str> for Str {
    fn from(value: &str) -> Self {
        Self(value.to_string())
    }
}

impl Add for Str {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self(self.0 + &rhs.0)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Num(pub f64);

impl From<f64> for Num {
    fn from(value: f64) -> Self {
        Self(value)
    }
}

impl PartialEq for Num {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl PartialOrd for Num {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl Add for Num {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}

impl Sub for Num {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Self(self.0 - rhs.0)
    }
}

impl Mul for Num {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Self(self.0 * rhs.0)
    }
}

impl Div for Num {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        Self(self.0 / rhs.0)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct List {
    pub exprs: Vec<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Number(Num),
    String(Str),
    List(List),
    Ident(Ident),
    Unary {
        op: UnaryOp,
        expr: Box<Expr>,
    },
    Binary {
        op: BinaryOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    MapAccess {
        expr: Box<Expr>,
        ident: Ident,
    },
    Lambda {
        params: Vec<String>,
        body: Box<Expr>,
    },
    Block {
        bindings: Vec<Binding>,
        expr: Box<Expr>,
    },
    Map {
        bindings: Vec<Binding>,
    },
    App {
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum UnaryOp {
    Neg,
    Not,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    NotEq,
    Lt,
    Gt,
    LtEq,
    GtEq,
    Dot,
}

impl BinaryOp {
    pub fn precedence(&self) -> u8 {
        match self {
            BinaryOp::Dot => 5,
            BinaryOp::Mul | BinaryOp::Div => 4,
            BinaryOp::Add | BinaryOp::Sub => 3,
            BinaryOp::Eq
            | BinaryOp::NotEq
            | BinaryOp::Lt
            | BinaryOp::Gt
            | BinaryOp::LtEq
            | BinaryOp::GtEq => 2,
        }
    }

    pub fn token_kind(&self) -> TokenKind {
        match self {
            BinaryOp::Add => TokenKind::Add,
            BinaryOp::Sub => TokenKind::Sub,
            BinaryOp::Mul => TokenKind::Mul,
            BinaryOp::Div => TokenKind::Div,
            BinaryOp::Eq => TokenKind::Eq,
            BinaryOp::NotEq => TokenKind::NotEq,
            BinaryOp::Lt => TokenKind::Lt,
            BinaryOp::Gt => TokenKind::Gt,
            BinaryOp::LtEq => TokenKind::LtEq,
            BinaryOp::GtEq => TokenKind::GtEq,
            BinaryOp::Dot => TokenKind::Dot,
        }
    }
}

pub trait Visitor<'ast>: Sized {
    type Err;

    fn visit_expr(&mut self, expr: &'ast Expr) -> Result<(), Self::Err> {
        match expr {
            Expr::Number(n) => self.visit_num(n),
            Expr::String(s) => self.visit_str(s),
            Expr::Unary { op, expr } => self.visit_unary_op(op, expr),
            Expr::Binary { op, lhs, rhs } => self.visit_binary_op(op, lhs, rhs),
            Expr::Lambda { params, body } => self.visit_lambda(params, body),
            Expr::Block { bindings, expr } => self.visit_block_expr(bindings, expr),
            Expr::Map { bindings } => self.visit_map(bindings),
            Expr::App { lhs, rhs } => self.visit_app(lhs, rhs),
            Expr::Ident(ident) => self.visit_ident(ident),
            Expr::List(list) => self.visit_list(list),
            Expr::MapAccess { expr, ident } => self.visit_map_access(expr, ident),
        }
    }

    fn visit_ident(&mut self, ident: &'ast Ident) -> Result<(), Self::Err>;
    fn visit_bind(&mut self, bind: &'ast Binding) -> Result<(), Self::Err>;
    fn visit_num(&mut self, num: &'ast Num) -> Result<(), Self::Err>;
    fn visit_str(&mut self, sstr: &'ast Str) -> Result<(), Self::Err>;
    fn visit_unary_op(&mut self, op: &'ast UnaryOp, expr: &'ast Expr) -> Result<(), Self::Err>;
    fn visit_binary_op(
        &mut self,
        op: &'ast BinaryOp,
        lhs: &'ast Expr,
        rhs: &'ast Expr,
    ) -> Result<(), Self::Err>;
    fn visit_map(&mut self, bindings: &'ast [Binding]) -> Result<(), Self::Err>;
    fn visit_block_expr(
        &mut self,
        bindings: &'ast [Binding],
        expr: &'ast Expr,
    ) -> Result<(), Self::Err>;
    fn visit_app(&mut self, lhs: &'ast Expr, rhs: &'ast Expr) -> Result<(), Self::Err>;
    fn visit_lambda(&mut self, params: &'ast [String], body: &'ast Expr) -> Result<(), Self::Err>;
    fn visit_list(&mut self, list: &'ast List) -> Result<(), Self::Err>;
    fn visit_map_access(&mut self, expr: &'ast Expr, ident: &'ast Ident) -> Result<(), Self::Err>;
}
