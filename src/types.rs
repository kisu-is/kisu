use crate::ast::untyped::{
    BinaryOp, Binding, Expr, Ident, List, Num, Param, Program, Str, UnaryOp, Visitor,
};
use crate::ast::{typed, untyped};
use crate::span::Span;
use bumpalo::Bump;
use bumpalo::collections::Vec as BumpVec;
use std::collections::HashMap;
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Var(u32),
    Lambda(Box<Type>, Box<Type>),
    List(Box<Type>),
    Struct(String),
    Number,
    String,
    Bool,
    Unit,
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::Var(n) => write!(f, "t{}", n),
            Type::Lambda(arg, ret) => write!(f, "(fn {} -> {})", arg, ret),
            Type::List(t) => write!(f, "[{}]", t),
            Type::Struct(name) => write!(f, "{}", name),
            Type::Number => write!(f, "Number"),
            Type::String => write!(f, "String"),
            Type::Bool => write!(f, "Bool"),
            Type::Unit => write!(f, "Unit"),
        }
    }
}

pub use _hide_warnings::*;
mod _hide_warnings {
    #![allow(unused_assignments)]

    use miette::{Diagnostic, SourceSpan};
    use thiserror::Error;

    #[derive(Debug, PartialEq, Error, Diagnostic)]
    pub enum Error {
        #[error("Unexpected type: {t1} != {t2}")]
        UnexpectedType {
            t1: String,
            t2: String,
            #[label]
            span: SourceSpan,
        },
        #[error("Infinite type")]
        InfiniteType {
            #[label]
            span: SourceSpan,
        },
        #[error("Identifier {name} is undefined")]
        UndefinedIdent {
            name: String,
            #[label]
            span: SourceSpan,
        },
        #[error("Unknown type: {name}")]
        UnknownType {
            name: String,
            #[label]
            span: SourceSpan,
        },
        #[error("Duplicate struct definition: {name}")]
        DuplicateDef {
            name: String,
            #[label]
            span: SourceSpan,
        },
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeId(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeKind<'ast> {
    Var(u32),
    Lambda(TypeId, TypeId),
    List(TypeId),
    Struct(&'ast str),
    Number,
    String,
    Bool,
    Unit,
}

#[derive(Debug, Clone, Copy)]
struct TypeVar {
    binding: Option<TypeId>,
    level: u32,
}

#[derive(Debug)]
pub struct Types<'ast> {
    kinds: Vec<TypeKind<'ast>>,
    interned: HashMap<TypeKind<'ast>, TypeId>,
    vars: Vec<TypeVar>,
}

impl<'ast> Types<'ast> {
    pub const NUMBER: TypeId = TypeId(0);
    pub const STRING: TypeId = TypeId(1);
    pub const BOOL: TypeId = TypeId(2);
    pub const UNIT: TypeId = TypeId(3);

    fn new() -> Self {
        let mut types = Self {
            kinds: Vec::new(),
            interned: HashMap::new(),
            vars: Vec::new(),
        };
        for kind in [
            TypeKind::Number,
            TypeKind::String,
            TypeKind::Bool,
            TypeKind::Unit,
        ] {
            types.intern(kind);
        }
        types
    }

    fn push(&mut self, kind: TypeKind<'ast>) -> TypeId {
        let id = TypeId(self.kinds.len() as u32);
        self.kinds.push(kind);
        id
    }

    fn intern(&mut self, kind: TypeKind<'ast>) -> TypeId {
        if let Some(&id) = self.interned.get(&kind) {
            return id;
        }
        let id = self.push(kind);
        self.interned.insert(kind, id);
        id
    }

    fn new_var(&mut self, level: u32) -> TypeId {
        let var = self.vars.len() as u32;
        self.vars.push(TypeVar {
            binding: None,
            level,
        });
        self.push(TypeKind::Var(var))
    }

    pub fn resolve(&self, mut ty: TypeId) -> TypeId {
        while let TypeKind::Var(var) = self.kinds[ty.0 as usize]
            && let Some(binding) = self.vars[var as usize].binding
        {
            ty = binding;
        }
        ty
    }

    pub fn kind(&self, ty: TypeId) -> TypeKind<'ast> {
        self.kinds[self.resolve(ty).0 as usize]
    }

    pub fn to_type(&self, ty: TypeId) -> Type {
        match self.kind(ty) {
            TypeKind::Var(var) => Type::Var(var),
            TypeKind::Lambda(arg, ret) => {
                Type::Lambda(Box::new(self.to_type(arg)), Box::new(self.to_type(ret)))
            }
            TypeKind::List(ty) => Type::List(Box::new(self.to_type(ty))),
            TypeKind::Struct(name) => Type::Struct(name.to_string()),
            TypeKind::Number => Type::Number,
            TypeKind::String => Type::String,
            TypeKind::Bool => Type::Bool,
            TypeKind::Unit => Type::Unit,
        }
    }

    fn occurs(&mut self, var: u32, level: u32, ty: TypeId) -> bool {
        match self.kind(ty) {
            TypeKind::Var(other) => {
                if other == var {
                    return true;
                }
                let other = &mut self.vars[other as usize];
                other.level = other.level.min(level);
                false
            }
            TypeKind::Lambda(arg, ret) => {
                self.occurs(var, level, arg) || self.occurs(var, level, ret)
            }
            TypeKind::List(ty) => self.occurs(var, level, ty),
            _ => false,
        }
    }

    fn free_vars(&self, ty: TypeId, level: u32, vars: &mut Vec<u32>) {
        match self.kind(ty) {
            TypeKind::Var(var) => {
                if self.vars[var as usize].level > level && !vars.contains(&var) {
                    vars.push(var);
                }
            }
            TypeKind::Lambda(arg, ret) => {
                self.free_vars(arg, level, vars);
                self.free_vars(ret, level, vars);
            }
            TypeKind::List(ty) => self.free_vars(ty, level, vars),
            _ => (),
        }
    }

    fn substitute(&mut self, ty: TypeId, subst: &[(u32, TypeId)]) -> TypeId {
        let ty = self.resolve(ty);
        match self.kind(ty) {
            TypeKind::Var(var) => subst
                .iter()
                .find(|(from, _)| *from == var)
                .map_or(ty, |&(_, to)| to),
            TypeKind::Lambda(arg, ret) => {
                let arg = self.substitute(arg, subst);
                let ret = self.substitute(ret, subst);
                self.intern(TypeKind::Lambda(arg, ret))
            }
            TypeKind::List(ty) => {
                let ty = self.substitute(ty, subst);
                self.intern(TypeKind::List(ty))
            }
            _ => ty,
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct Scheme<'ast> {
    vars: &'ast [u32],
    ty: TypeId,
}

impl Scheme<'_> {
    fn mono(ty: TypeId) -> Self {
        Self { vars: &[], ty }
    }
}

#[derive(Default)]
struct Scope<'ast> {
    schemes: HashMap<&'ast str, Vec<Scheme<'ast>>>,
    history: Vec<&'ast str>,
}

impl<'ast> Scope<'ast> {
    fn extend(&mut self, name: &'ast str, scheme: Scheme<'ast>) {
        self.schemes.entry(name).or_default().push(scheme);
        self.history.push(name);
    }

    fn get(&self, name: &str) -> Option<Scheme<'ast>> {
        self.schemes.get(name).and_then(|s| s.last()).copied()
    }

    fn mark(&self) -> usize {
        self.history.len()
    }

    fn restore(&mut self, mark: usize) {
        for name in self.history.drain(mark..) {
            if let Some(schemes) = self.schemes.get_mut(name) {
                schemes.pop();
            }
        }
    }
}

pub struct TypeChecker<'ast> {
    bump: &'ast Bump,
    types: Types<'ast>,
    scope: Scope<'ast>,
    struct_defs: HashMap<&'ast str, typed::StructDef<'ast>>,
    structs: &'ast [typed::StructDef<'ast>],
    level: u32,
    last_expr: Option<typed::Expr<'ast>>,
    last_binding: Option<typed::Binding<'ast>>,
}

impl<'ast> TypeChecker<'ast> {
    pub fn new(bump: &'ast Bump) -> Self {
        Self {
            bump,
            types: Types::new(),
            scope: Scope::default(),
            struct_defs: HashMap::new(),
            structs: &[],
            level: 0,
            last_expr: None,
            last_binding: None,
        }
    }

    pub fn new_with_native(bump: &'ast Bump, native_types: HashMap<String, Type>) -> Self {
        let mut checker = TypeChecker::new(bump);
        for (name, ty) in native_types {
            checker.level += 1;
            let ty = checker.lower_type(&ty, &mut Vec::new());
            checker.level -= 1;
            let scheme = checker.generalize(ty);
            checker.scope.extend(bump.alloc_str(&name), scheme);
        }
        checker
    }

    pub fn consume(mut self) -> Result<typed::Program<'ast>, Error> {
        let expr = self.alloc_expr();
        Ok(typed::Program {
            expr,
            structs: self.structs,
            types: self.types,
        })
    }

    fn new_var(&mut self) -> TypeId {
        self.types.new_var(self.level)
    }

    fn take_expr(&mut self) -> typed::Expr<'ast> {
        self.last_expr.take().unwrap()
    }

    fn alloc_expr(&mut self) -> &'ast typed::Expr<'ast> {
        let expr = self.take_expr();
        self.bump.alloc(expr)
    }

    fn set_expr(&mut self, kind: typed::ExprKind<'ast>, span: Span, ty: TypeId) {
        self.last_expr = Some(typed::Expr { kind, span, ty });
    }

    fn type_error(&self, t1: TypeId, t2: TypeId, span: Span) -> Error {
        Error::UnexpectedType {
            t1: self.types.to_type(t1).to_string(),
            t2: self.types.to_type(t2).to_string(),
            span: span.into(),
        }
    }

    fn lower_type(&mut self, ty: &Type, vars: &mut Vec<(u32, TypeId)>) -> TypeId {
        match ty {
            Type::Var(var) => {
                if let Some(&(_, ty)) = vars.iter().find(|(from, _)| from == var) {
                    return ty;
                }
                let ty = self.new_var();
                vars.push((*var, ty));
                ty
            }
            Type::Lambda(arg, ret) => {
                let arg = self.lower_type(arg, vars);
                let ret = self.lower_type(ret, vars);
                self.types.intern(TypeKind::Lambda(arg, ret))
            }
            Type::List(ty) => {
                let ty = self.lower_type(ty, vars);
                self.types.intern(TypeKind::List(ty))
            }
            Type::Struct(name) => {
                let name = match self.struct_defs.get_key_value(name.as_str()) {
                    Some((name, _)) => *name,
                    None => self.bump.alloc_str(name),
                };
                self.types.intern(TypeKind::Struct(name))
            }
            Type::Number => Types::NUMBER,
            Type::String => Types::STRING,
            Type::Bool => Types::BOOL,
            Type::Unit => Types::UNIT,
        }
    }

    fn unify(&mut self, t1: TypeId, t2: TypeId, span: Span) -> Result<TypeId, Error> {
        let t1 = self.types.resolve(t1);
        let t2 = self.types.resolve(t2);

        if t1 == t2 {
            return Ok(t1);
        }

        match (self.types.kind(t1), self.types.kind(t2)) {
            (TypeKind::Var(var), _) => {
                self.bind_var(var, t2, span)?;
                Ok(t2)
            }
            (_, TypeKind::Var(var)) => {
                self.bind_var(var, t1, span)?;
                Ok(t1)
            }
            (TypeKind::Lambda(arg1, ret1), TypeKind::Lambda(arg2, ret2)) => {
                self.unify(arg1, arg2, span)?;
                self.unify(ret1, ret2, span)?;
                Ok(t1)
            }
            (TypeKind::List(elem1), TypeKind::List(elem2)) => {
                self.unify(elem1, elem2, span)?;
                Ok(t1)
            }
            _ => Err(self.type_error(t1, t2, span)),
        }
    }

    fn bind_var(&mut self, var: u32, ty: TypeId, span: Span) -> Result<(), Error> {
        let level = self.types.vars[var as usize].level;
        if self.types.occurs(var, level, ty) {
            return Err(Error::InfiniteType { span: span.into() });
        }
        self.types.vars[var as usize].binding = Some(ty);
        Ok(())
    }

    fn generalize(&mut self, ty: TypeId) -> Scheme<'ast> {
        let mut vars = Vec::new();
        self.types.free_vars(ty, self.level, &mut vars);
        Scheme {
            vars: self.bump.alloc_slice_copy(&vars),
            ty,
        }
    }

    fn instantiate(&mut self, scheme: Scheme<'ast>) -> TypeId {
        if scheme.vars.is_empty() {
            return scheme.ty;
        }
        let subst: Vec<(u32, TypeId)> = scheme
            .vars
            .iter()
            .map(|&var| (var, self.new_var()))
            .collect();
        self.types.substitute(scheme.ty, &subst)
    }
}

impl<'ast> Visitor<'ast> for TypeChecker<'ast> {
    type Err = Error;

    fn visit_program(&mut self, program: &'ast Program<'ast>) -> Result<(), Self::Err> {
        let mut structs = BumpVec::with_capacity_in(program.structs.len(), self.bump);
        for s in program.structs.iter() {
            self.visit_struct_def(s)?;
            structs.push(self.struct_defs[s.name.name]);
        }
        self.structs = structs.into_bump_slice();
        self.visit_expr(program.expr)
    }

    fn visit_ident(&mut self, ident: &'ast Ident<'ast>) -> Result<(), Self::Err> {
        let Some(scheme) = self.scope.get(ident.name) else {
            return Err(Error::UndefinedIdent {
                name: ident.name.to_string(),
                span: ident.span.into(),
            });
        };

        let ty = self.instantiate(scheme);
        self.set_expr(
            typed::ExprKind::Ident(typed::Ident {
                name: ident.name,
                span: ident.span,
                ty,
            }),
            ident.span,
            ty,
        );
        Ok(())
    }

    fn visit_bind(&mut self, bind: &'ast untyped::Binding<'ast>) -> Result<(), Self::Err> {
        self.level += 1;

        let expr = if bind.kind == untyped::BindingKind::Rec {
            let tv = self.new_var();
            let mark = self.scope.mark();
            self.scope.extend(bind.ident.name, Scheme::mono(tv));
            self.visit_expr(bind.expr)?;
            self.scope.restore(mark);

            let expr = self.take_expr();
            self.unify(tv, expr.ty, bind.ident.span)?;
            expr
        } else {
            self.visit_expr(bind.expr)?;
            self.take_expr()
        };

        let ty = if let Some(constraint) = &bind.constraint {
            let constraint = self.lower_type(constraint, &mut Vec::new());
            self.unify(expr.ty, constraint, bind.ident.span)?
        } else {
            expr.ty
        };

        self.level -= 1;

        let scheme = self.generalize(ty);
        self.scope.extend(bind.ident.name, scheme);

        self.last_binding = Some(typed::Binding {
            kind: match bind.kind {
                untyped::BindingKind::Normal => typed::BindingKind::Normal,
                untyped::BindingKind::Rec => typed::BindingKind::Rec,
            },
            ident: typed::Ident {
                name: bind.ident.name,
                span: bind.ident.span,
                ty,
            },
            expr: self.bump.alloc(expr),
            span: bind.span,
            ty,
        });

        Ok(())
    }

    fn visit_num(&mut self, num: &'ast Num) -> Result<(), Self::Err> {
        self.set_expr(
            typed::ExprKind::Number(typed::Num(num.0, num.1, Types::NUMBER)),
            num.1,
            Types::NUMBER,
        );
        Ok(())
    }

    fn visit_str(&mut self, s: &'ast Str<'ast>) -> Result<(), Self::Err> {
        self.set_expr(
            typed::ExprKind::String(typed::Str(s.0, s.1, Types::STRING)),
            s.1,
            Types::STRING,
        );
        Ok(())
    }

    fn visit_bool(&mut self, b: bool) -> Result<(), Self::Err> {
        self.set_expr(typed::ExprKind::Bool(b), Span::default(), Types::BOOL);
        Ok(())
    }

    fn visit_unary_op(
        &mut self,
        op: &'ast UnaryOp,
        expr: &'ast Expr<'ast>,
    ) -> Result<(), Self::Err> {
        self.visit_expr(expr)?;
        let ty_expr = self.alloc_expr();

        let span = ty_expr.span.to(expr.span());
        let inferred_ty = match op {
            UnaryOp::Neg => self.unify(ty_expr.ty, Types::NUMBER, span)?,
            UnaryOp::Not => self.unify(ty_expr.ty, Types::BOOL, span)?,
        };

        self.set_expr(
            typed::ExprKind::Unary {
                op: match op {
                    untyped::UnaryOp::Neg => typed::UnaryOp::Neg,
                    untyped::UnaryOp::Not => typed::UnaryOp::Not,
                },
                expr: ty_expr,
            },
            expr.span(),
            inferred_ty,
        );
        Ok(())
    }

    fn visit_binary_op(
        &mut self,
        op: &'ast BinaryOp,
        lhs: &'ast Expr<'ast>,
        rhs: &'ast Expr<'ast>,
    ) -> Result<(), Self::Err> {
        self.visit_expr(lhs)?;
        let ty_lhs = self.alloc_expr();
        self.visit_expr(rhs)?;
        let ty_rhs = self.alloc_expr();

        let span = lhs.span().to(rhs.span());

        let (operand_ty, result_ty) = match op {
            BinaryOp::Add => {
                let operand_ty = if self.types.resolve(ty_lhs.ty) == Types::STRING
                    || self.types.resolve(ty_rhs.ty) == Types::STRING
                {
                    Types::STRING
                } else {
                    Types::NUMBER
                };
                self.unify(ty_lhs.ty, operand_ty, span)?;
                self.unify(ty_rhs.ty, operand_ty, span)?;
                (operand_ty, operand_ty)
            }
            BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div => {
                self.unify(ty_lhs.ty, Types::NUMBER, span)?;
                self.unify(ty_rhs.ty, Types::NUMBER, span)?;
                (Types::NUMBER, Types::NUMBER)
            }
            BinaryOp::Eq
            | BinaryOp::NotEq
            | BinaryOp::Lt
            | BinaryOp::Gt
            | BinaryOp::LtEq
            | BinaryOp::GtEq => (self.unify(ty_lhs.ty, ty_rhs.ty, span)?, Types::BOOL),
            BinaryOp::Dot => {
                unreachable!();
            }
        };

        self.set_expr(
            typed::ExprKind::Binary {
                op: match op {
                    untyped::BinaryOp::Add => typed::BinaryOp::Add,
                    untyped::BinaryOp::Sub => typed::BinaryOp::Sub,
                    untyped::BinaryOp::Mul => typed::BinaryOp::Mul,
                    untyped::BinaryOp::Div => typed::BinaryOp::Div,
                    untyped::BinaryOp::Eq => typed::BinaryOp::Eq,
                    untyped::BinaryOp::NotEq => typed::BinaryOp::NotEq,
                    untyped::BinaryOp::Lt => typed::BinaryOp::Lt,
                    untyped::BinaryOp::Gt => typed::BinaryOp::Gt,
                    untyped::BinaryOp::LtEq => typed::BinaryOp::LtEq,
                    untyped::BinaryOp::GtEq => typed::BinaryOp::GtEq,
                    untyped::BinaryOp::Dot => unreachable!(),
                },
                lhs: ty_lhs,
                rhs: ty_rhs,
                ty: operand_ty,
            },
            span,
            result_ty,
        );
        Ok(())
    }

    fn visit_struct_expr(
        &mut self,
        type_name: &'ast untyped::TypeIdent<'ast>,
        fields: &'ast [Binding<'ast>],
    ) -> Result<(), Self::Err> {
        let Some(struct_def) = self.struct_defs.get(type_name.name).copied() else {
            return Err(Error::UnknownType {
                name: type_name.name.to_string(),
                span: type_name.span.into(),
            });
        };

        let mut expected_fields: HashMap<&str, TypeId> = struct_def
            .fields
            .iter()
            .map(|f| (f.ident.name, f.ty))
            .collect();

        let mut ty_fields = BumpVec::with_capacity_in(fields.len(), self.bump);

        for bind in fields {
            let mark = self.scope.mark();
            self.visit_bind(bind)?;
            self.scope.restore(mark);

            let ty_bind = self.last_binding.take().unwrap();

            let Some(expected_ty) = expected_fields.remove(bind.ident.name) else {
                return Err(Error::UndefinedIdent {
                    name: bind.ident.name.to_string(),
                    span: bind.ident.span.into(),
                });
            };
            self.unify(ty_bind.ty, expected_ty, bind.ident.span)?;
            ty_fields.push(ty_bind);
        }

        if !expected_fields.is_empty() {
            return Err(Error::UnexpectedType {
                t1: "Missing fields".to_string(),
                t2: format!("Expected: {:?}", expected_fields.keys()),
                span: type_name.span.into(),
            });
        }

        self.set_expr(
            typed::ExprKind::Struct {
                name: typed::TypeIdent {
                    name: struct_def.name.name,
                    span: type_name.span,
                },
                fields: ty_fields.into_bump_slice(),
            },
            type_name
                .span
                .to(fields.last().map_or(type_name.span, |b| b.span)),
            struct_def.ty,
        );
        Ok(())
    }

    fn visit_struct_def(
        &mut self,
        struct_def: &'ast untyped::StructDef<'ast>,
    ) -> Result<(), Self::Err> {
        let name = struct_def.name.name;
        if self.struct_defs.contains_key(name) {
            return Err(Error::DuplicateDef {
                name: name.to_string(),
                span: struct_def.span.into(),
            });
        }

        let mut ty_fields = BumpVec::with_capacity_in(struct_def.fields.len(), self.bump);
        for field in struct_def.fields.iter() {
            let field_ty = self.lower_type(&field.ty, &mut Vec::new());
            ty_fields.push(typed::StructField {
                ident: typed::Ident {
                    name: field.ident.name,
                    span: field.ident.span,
                    ty: field_ty,
                },
                ty: field_ty,
                span: field.span,
            });
        }

        let ty = self.types.intern(TypeKind::Struct(name));
        self.struct_defs.insert(
            name,
            typed::StructDef {
                name: typed::TypeIdent {
                    name,
                    span: struct_def.name.span,
                },
                fields: ty_fields.into_bump_slice(),
                span: struct_def.span,
                ty,
            },
        );

        Ok(())
    }

    fn visit_block_expr(
        &mut self,
        bindings: &'ast [Binding<'ast>],
        expr: &'ast Expr<'ast>,
    ) -> Result<(), Self::Err> {
        let mark = self.scope.mark();
        let mut ty_bindings = BumpVec::with_capacity_in(bindings.len(), self.bump);

        for bind in bindings {
            self.visit_bind(bind)?;
            ty_bindings.push(self.last_binding.take().unwrap());
        }

        self.visit_expr(expr)?;
        self.scope.restore(mark);
        let ty_expr = self.alloc_expr();

        self.set_expr(
            typed::ExprKind::Block {
                bindings: ty_bindings.into_bump_slice(),
                expr: ty_expr,
            },
            bindings
                .first()
                .map_or(expr.span(), |b| b.span)
                .to(expr.span()),
            ty_expr.ty,
        );
        Ok(())
    }

    fn visit_app(&mut self, lhs: &'ast Expr<'ast>, rhs: &'ast Expr<'ast>) -> Result<(), Self::Err> {
        self.visit_expr(lhs)?;
        let ty_lhs = self.alloc_expr();
        self.visit_expr(rhs)?;
        let ty_rhs = self.alloc_expr();

        let ret_ty = self.new_var();
        let expected_func_ty = self.types.intern(TypeKind::Lambda(ty_rhs.ty, ret_ty));
        self.unify(ty_lhs.ty, expected_func_ty, lhs.span())?;

        self.set_expr(
            typed::ExprKind::App {
                lhs: ty_lhs,
                rhs: ty_rhs,
            },
            lhs.span().to(rhs.span()),
            ret_ty,
        );
        Ok(())
    }

    fn visit_lambda(
        &mut self,
        params: &'ast [Param<'ast>],
        body: &'ast Expr<'ast>,
    ) -> Result<(), Self::Err> {
        let mark = self.scope.mark();
        let mut ty_params = BumpVec::with_capacity_in(params.len(), self.bump);

        for param in params {
            let tv = self.new_var();
            if let Some(constraint) = &param.constraint {
                let constraint = self.lower_type(constraint, &mut Vec::new());
                self.unify(tv, constraint, param.ident.span)?;
            }

            self.scope.extend(param.ident.name, Scheme::mono(tv));
            ty_params.push(typed::Param {
                ident: typed::Ident {
                    name: param.ident.name,
                    span: param.ident.span,
                    ty: tv,
                },
                ty: tv,
                span: param.span,
            });
        }

        self.visit_expr(body)?;
        self.scope.restore(mark);
        let ty_body = self.alloc_expr();

        let mut lambda_ty = ty_body.ty;
        for param in ty_params.iter().rev() {
            lambda_ty = self.types.intern(TypeKind::Lambda(param.ty, lambda_ty));
        }

        self.set_expr(
            typed::ExprKind::Lambda {
                params: ty_params.into_bump_slice(),
                body: ty_body,
            },
            params
                .first()
                .map_or(body.span(), |p| p.span)
                .to(body.span()),
            lambda_ty,
        );
        Ok(())
    }

    fn visit_list(&mut self, list: &'ast List<'ast>) -> Result<(), Self::Err> {
        let elem_ty = self.new_var();
        let mut ty_exprs = BumpVec::with_capacity_in(list.exprs.len(), self.bump);

        for expr in list.exprs.iter() {
            self.visit_expr(expr)?;
            let ty_expr = self.take_expr();
            self.unify(elem_ty, ty_expr.ty, expr.span())?;
            ty_exprs.push(ty_expr);
        }

        let ty = self.types.intern(TypeKind::List(elem_ty));
        self.set_expr(
            typed::ExprKind::List(typed::List {
                exprs: ty_exprs.into_bump_slice(),
                span: list.span,
                ty,
            }),
            list.span,
            ty,
        );
        Ok(())
    }

    fn visit_struct_access(
        &mut self,
        expr: &'ast Expr<'ast>,
        ident: &'ast Ident<'ast>,
    ) -> Result<(), Self::Err> {
        self.visit_expr(expr)?;
        let ty_expr = self.alloc_expr();

        let TypeKind::Struct(name) = self.types.kind(ty_expr.ty) else {
            return Err(Error::UnexpectedType {
                t1: format!(
                    "Expected struct type, found {}",
                    self.types.to_type(ty_expr.ty)
                ),
                t2: "Struct".to_string(),
                span: expr.span().into(),
            });
        };

        let struct_def = self
            .struct_defs
            .get(name)
            .ok_or_else(|| Error::UnknownType {
                name: name.to_string(),
                span: expr.span().into(),
            })?;

        let field_ty = struct_def
            .fields
            .iter()
            .find(|f| f.ident.name == ident.name)
            .map(|f| f.ty)
            .ok_or_else(|| Error::UndefinedIdent {
                name: ident.name.to_string(),
                span: ident.span.into(),
            })?;

        self.set_expr(
            typed::ExprKind::StructAccess {
                expr: ty_expr,
                ident: typed::Ident {
                    name: ident.name,
                    span: ident.span,
                    ty: field_ty,
                },
            },
            expr.span().to(ident.span),
            field_ty,
        );
        Ok(())
    }

    fn visit_if_expr(
        &mut self,
        cond: &'ast Expr<'ast>,
        then_expr: &'ast Expr<'ast>,
        else_expr: &'ast Expr<'ast>,
    ) -> Result<(), Self::Err> {
        self.visit_expr(cond)?;
        let ty_cond = self.alloc_expr();
        self.unify(ty_cond.ty, Types::BOOL, cond.span())?;

        self.visit_expr(then_expr)?;
        let ty_then = self.alloc_expr();
        self.visit_expr(else_expr)?;
        let ty_else = self.alloc_expr();
        self.unify(ty_then.ty, ty_else.ty, then_expr.span())?;

        self.set_expr(
            typed::ExprKind::IfExpr {
                cond: ty_cond,
                then_expr: ty_then,
                else_expr: ty_else,
            },
            cond.span().to(else_expr.span()),
            ty_then.ty,
        );
        Ok(())
    }

    fn visit_type(&mut self, _ty: &'ast Type) -> Result<(), Self::Err> {
        Ok(())
    }
}
