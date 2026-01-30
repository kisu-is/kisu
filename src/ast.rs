use crate::lexer::TokenKind;

#[derive(Debug, Clone, PartialEq)]
pub struct Binding {
    pub name: String,
    pub expr: Box<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Number(f64),
    String(String),
    Ident(String),
    Unary {
        op: UnaryOp,
        expr: Box<Expr>,
    },
    Binary {
        op: BinaryOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Lambda {
        param: String,
        body: Box<Expr>,
    },
    Paren(Box<Expr>),
    Block {
        bindings: Vec<Binding>,
        expr: Box<Expr>,
    },
    Map {
        bindings: Vec<Binding>,
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
}

impl BinaryOp {
    pub fn precedence(&self) -> u8 {
        match self {
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
        }
    }
}
