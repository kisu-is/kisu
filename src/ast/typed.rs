use crate::span::Span;
use crate::types::{TypeId, Types};

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Ident<'ast> {
    pub name: &'ast str,
    pub span: Span,
    pub ty: TypeId,
}

#[derive(Debug, Clone, PartialEq, Copy)]
pub enum BindingKind {
    Normal,
    Rec,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Str<'ast>(pub &'ast str, pub Span, pub TypeId);

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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TypeIdent<'ast> {
    pub name: &'ast str,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct StructField<'ast> {
    pub ident: Ident<'ast>,
    pub ty: TypeId,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct StructDef<'ast> {
    pub name: TypeIdent<'ast>,
    pub fields: &'ast [StructField<'ast>],
    pub span: Span,
    pub ty: TypeId,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Binding<'ast> {
    pub kind: BindingKind,
    pub ident: Ident<'ast>,
    pub expr: &'ast Expr<'ast>,
    pub span: Span,
    pub ty: TypeId,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Param<'ast> {
    pub ident: Ident<'ast>,
    pub ty: TypeId,
    pub span: Span,
}

#[derive(Debug)]
pub struct Program<'ast> {
    pub expr: &'ast Expr<'ast>,
    pub structs: &'ast [StructDef<'ast>],
    pub types: Types<'ast>,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Num(pub f64, pub Span, pub TypeId);

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct List<'ast> {
    pub exprs: &'ast [Expr<'ast>],
    pub span: Span,
    pub ty: TypeId,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Expr<'ast> {
    pub kind: ExprKind<'ast>,
    pub span: Span,
    pub ty: TypeId,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ExprKind<'ast> {
    Number(Num),
    String(Str<'ast>),
    Bool(bool),
    List(List<'ast>),
    Ident(Ident<'ast>),
    Unary {
        op: UnaryOp,
        expr: &'ast Expr<'ast>,
    },
    Binary {
        op: BinaryOp,
        lhs: &'ast Expr<'ast>,
        rhs: &'ast Expr<'ast>,
        ty: TypeId,
    },
    StructAccess {
        expr: &'ast Expr<'ast>,
        ident: Ident<'ast>,
    },
    Lambda {
        params: &'ast [Param<'ast>],
        body: &'ast Expr<'ast>,
    },
    Block {
        bindings: &'ast [Binding<'ast>],
        expr: &'ast Expr<'ast>,
    },
    Struct {
        name: TypeIdent<'ast>,
        fields: &'ast [Binding<'ast>],
    },
    App {
        lhs: &'ast Expr<'ast>,
        rhs: &'ast Expr<'ast>,
    },
    IfExpr {
        cond: &'ast Expr<'ast>,
        then_expr: &'ast Expr<'ast>,
        else_expr: &'ast Expr<'ast>,
    },
}

#[allow(clippy::missing_safety_doc)]
pub trait Visitor<'ast>: Sized {
    unsafe fn visit_program(&mut self, program: &Program<'ast>) {
        unsafe {
            for s in program.structs {
                self.visit_struct_def(s);
            }
            self.visit_expr(program.expr)
        }
    }

    unsafe fn visit_expr(&mut self, expr: &'ast Expr<'ast>) {
        unsafe {
            match &expr.kind {
                ExprKind::Number(n) => self.visit_num(n),
                ExprKind::String(s) => self.visit_str(s),
                ExprKind::Bool(b) => self.visit_bool(*b),
                ExprKind::List(l) => self.visit_list(l),
                ExprKind::Ident(i) => self.visit_ident(i),
                ExprKind::Unary { op, expr } => self.visit_unary_op(op, expr),
                ExprKind::Binary { op, lhs, rhs, ty } => self.visit_binary_op(op, lhs, rhs, ty),
                ExprKind::StructAccess { expr, ident } => self.visit_struct_access(expr, ident),
                ExprKind::Lambda { params, body } => self.visit_lambda(params, body),
                ExprKind::Block { bindings, expr } => self.visit_block_expr(bindings, expr),
                ExprKind::Struct { name, fields } => self.visit_struct_expr(fields, name),
                ExprKind::App { lhs, rhs } => self.visit_app(lhs, rhs),
                ExprKind::IfExpr {
                    cond,
                    then_expr,
                    else_expr,
                } => self.visit_if_expr(cond, then_expr, else_expr),
            }
        }
    }

    unsafe fn visit_num(&mut self, num: &'ast Num);
    unsafe fn visit_str(&mut self, str: &'ast Str<'ast>);
    unsafe fn visit_bool(&mut self, b: bool);
    unsafe fn visit_list(&mut self, list: &'ast List<'ast>);
    unsafe fn visit_ident(&mut self, ident: &'ast Ident<'ast>);
    unsafe fn visit_unary_op(&mut self, op: &'ast UnaryOp, expr: &'ast Expr<'ast>);
    unsafe fn visit_binary_op(
        &mut self,
        op: &'ast BinaryOp,
        lhs: &'ast Expr<'ast>,
        rhs: &'ast Expr<'ast>,
        ty: &'ast TypeId,
    );
    unsafe fn visit_struct_access(&mut self, expr: &'ast Expr<'ast>, ident: &'ast Ident<'ast>);
    unsafe fn visit_lambda(&mut self, params: &'ast [Param<'ast>], body: &'ast Expr<'ast>);
    unsafe fn visit_block_expr(&mut self, bindings: &'ast [Binding<'ast>], expr: &'ast Expr<'ast>);
    unsafe fn visit_struct_expr(
        &mut self,
        fields: &'ast [Binding<'ast>],
        name: &'ast TypeIdent<'ast>,
    );
    unsafe fn visit_app(&mut self, lhs: &'ast Expr<'ast>, rhs: &'ast Expr<'ast>);
    unsafe fn visit_if_expr(
        &mut self,
        cond: &'ast Expr<'ast>,
        then_expr: &'ast Expr<'ast>,
        else_expr: &'ast Expr<'ast>,
    );
    unsafe fn visit_bind(&mut self, bind: &'ast Binding<'ast>);
    unsafe fn visit_struct_def(&mut self, struct_def: &'ast StructDef<'ast>);
}
