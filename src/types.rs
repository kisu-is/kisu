use crate::ast::untyped::{
    BinaryOp, Binding, Expr, Ident, List, Num, Param, Program, Str, UnaryOp, Visitor,
};
use crate::ast::{typed, untyped};
use miette::SourceSpan;
use std::collections::{HashMap, HashSet};
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Var(u32),
    Lambda(Box<Type>, Box<Type>),
    List(Box<Type>),
    Struct(typed::TypeIdent),
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
            Type::Struct(ident) => write!(f, "{}", ident.name),
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

#[derive(Default)]
pub struct TypeChecker {
    subst: HashMap<u32, Type>,
    count: u32,
    scope: Scope,
    program: Option<typed::Program>,
    struct_defs: HashMap<String, typed::StructDef>,
    last_expr: Option<typed::Expr>,
    last_binding: Option<typed::Binding>,
}

impl TypeChecker {
    pub fn new_with_native(native_types: HashMap<String, Type>) -> Self {
        let mut checker = TypeChecker::default();
        for (name, ty) in native_types {
            let scheme = checker.generalize(&checker.scope, &ty);
            checker.scope.extend(name, scheme);
        }
        checker
    }

    #[allow(clippy::too_many_arguments)]
    fn new(
        subst: HashMap<u32, Type>,
        count: u32,
        scope: Scope,
        program: Option<typed::Program>,
        struct_defs: HashMap<String, typed::StructDef>,
        last_expr: Option<typed::Expr>,
        last_binding: Option<typed::Binding>,
    ) -> Self {
        Self {
            subst,
            count,
            scope,
            program,
            struct_defs,
            last_expr,
            last_binding,
        }
    }
    pub fn consume(mut self) -> Result<typed::Program, Error> {
        Ok(self.program.take().unwrap())
    }

    fn new_var(&mut self) -> Type {
        let id = self.count;
        self.count += 1;
        Type::Var(id)
    }

    fn apply(&self, ty: &Type) -> Type {
        match ty {
            Type::Var(id) => {
                if let Some(t) = self.subst.get(id) {
                    self.apply(t)
                } else {
                    ty.clone()
                }
            }
            Type::Lambda(arg, ret) => {
                Type::Lambda(Box::new(self.apply(arg)), Box::new(self.apply(ret)))
            }
            Type::List(t) => Type::List(Box::new(self.apply(t))),
            Type::Struct(ident) => Type::Struct(ident.clone()),
            _ => ty.clone(),
        }
    }

    fn unify(&mut self, t1: &Type, t2: &Type, span: SourceSpan) -> Result<Type, Error> {
        let t1 = self.apply(t1);
        let t2 = self.apply(t2);

        if t1 == t2 {
            return Ok(t1);
        }

        if let Type::Var(id) = t1 {
            self.unify_var(id, &t2, span)?;
            return Ok(t2);
        }

        if let Type::Var(id) = t2 {
            self.unify_var(id, &t1, span)?;
            return Ok(t1);
        }

        match (&t1, &t2) {
            (Type::Lambda(arg, ret), Type::Lambda(arg2, ret2)) => {
                let arg_ty = self.unify(arg, arg2, span)?;
                let ret_ty = self.unify(ret, ret2, span)?;
                Ok(Type::Lambda(Box::new(arg_ty), Box::new(ret_ty)))
            }
            (Type::List(t1), Type::List(t2)) => {
                let ty = self.unify(t1, t2, span)?;
                Ok(Type::List(Box::new(ty)))
            }
            (Type::Struct(ident), Type::Struct(ident2)) => {
                if ident.name == ident2.name {
                    Ok(t1)
                } else {
                    Err(Error::UnexpectedType {
                        t1: t1.to_string(),
                        t2: t2.to_string(),
                        span,
                    })
                }
            }
            _ => Err(Error::UnexpectedType {
                t1: t1.to_string(),
                t2: t2.to_string(),
                span,
            }),
        }
    }

    fn unify_var(&mut self, id: u32, ty: &Type, span: SourceSpan) -> Result<(), Error> {
        if let Some(t) = self.subst.get(&id).cloned() {
            self.unify(&t, ty, span)?;
            return Ok(());
        }
        if self.occurs(id, ty) {
            return Err(Error::InfiniteType { span });
        }
        self.subst.insert(id, ty.clone());
        Ok(())
    }

    fn occurs(&self, id: u32, ty: &Type) -> bool {
        match ty {
            Type::Var(var_id) => {
                if *var_id == id {
                    true
                } else if let Some(t) = self.subst.get(var_id) {
                    self.occurs(id, t)
                } else {
                    false
                }
            }
            Type::Lambda(arg, ret) => self.occurs(id, arg) || self.occurs(id, ret),
            Type::List(t) => self.occurs(id, t),
            Type::Struct(_) => false,
            _ => false,
        }
    }

    fn generalize(&self, scope: &Scope, ty: &Type) -> Scheme {
        let vars = self
            .ftv(ty)
            .difference(&self.ftv_scope(scope))
            .cloned()
            .collect();
        Scheme {
            vars,
            ty: ty.clone(),
        }
    }

    fn instantiate(&mut self, scheme: &Scheme) -> Type {
        let mut subst = HashMap::new();
        for var in &scheme.vars {
            subst.insert(*var, self.new_var());
        }
        self.apply_scheme(&subst, &scheme.ty)
    }

    fn apply_scheme(&self, subst: &HashMap<u32, Type>, ty: &Type) -> Type {
        match ty {
            Type::Var(id) => {
                if let Some(t) = subst.get(id) {
                    t.clone()
                } else {
                    ty.clone()
                }
            }
            Type::Lambda(arg, ret) => Type::Lambda(
                Box::new(self.apply_scheme(subst, arg)),
                Box::new(self.apply_scheme(subst, ret)),
            ),
            Type::List(t) => Type::List(Box::new(self.apply_scheme(subst, t))),
            Type::Struct(ident) => Type::Struct(ident.clone()),
            _ => ty.clone(),
        }
    }

    fn ftv(&self, ty: &Type) -> HashSet<u32> {
        let mut free_vars = HashSet::new();
        let ty = self.apply(ty);
        match &ty {
            Type::Var(id) => {
                free_vars.insert(*id);
            }
            Type::Lambda(arg, ret) => {
                free_vars.extend(self.ftv(arg));
                free_vars.extend(self.ftv(ret));
            }
            Type::List(t) => {
                free_vars.extend(self.ftv(t));
            }
            Type::Struct(_) => (),
            _ => (),
        }
        free_vars
    }

    fn ftv_scope(&self, scope: &Scope) -> HashSet<u32> {
        let mut free_vars = HashSet::new();
        for scheme in scope.0.values() {
            for var in self.ftv(&scheme.ty) {
                if !scheme.vars.contains(&var) {
                    free_vars.insert(var);
                }
            }
        }
        free_vars
    }
}

impl<'ast> Visitor<'ast> for TypeChecker {
    type Err = Error;

    fn visit_program(&mut self, program: &'ast Program<'ast>) -> Result<(), Self::Err> {
        let mut structs = Vec::new();
        for s in program.structs.iter() {
            self.visit_struct_def(s)?;
            let name = s.name.name.clone();
            structs.push(self.struct_defs.get(&name).unwrap().clone());
        }

        self.visit_expr(&program.expr)?;
        let ty_expr = self.last_expr.take().unwrap();

        self.program = Some(typed::Program {
            expr: ty_expr,
            structs,
        });
        Ok(())
    }

    fn visit_ident(&mut self, ident: &'ast Ident) -> Result<(), Self::Err> {
        if let Some(scheme) = self.scope.get(&ident.name).cloned() {
            let ty = self.instantiate(&scheme);
            self.last_expr = Some(typed::Expr {
                kind: Box::new(typed::ExprKind::Ident(typed::Ident {
                    name: ident.name.clone(),
                    span: ident.span.clone(),
                    ty: ty.clone(),
                })),
                span: ident.span.clone(),
                ty,
            });
            Ok(())
        } else {
            Err(Error::UndefinedIdent {
                name: ident.name.to_string(),
                span: ident.span.clone().into(),
            })
        }
    }

    fn visit_bind(&mut self, bind: &'ast untyped::Binding<'ast>) -> Result<(), Self::Err> {
        let mut checker = TypeChecker::new(
            self.subst.clone(),
            self.count,
            self.scope.clone(),
            None,
            self.struct_defs.clone(),
            None,
            None,
        );

        if bind.kind == untyped::BindingKind::Rec {
            let tv = checker.new_var();
            let scheme = Scheme {
                vars: vec![],
                ty: tv.clone(),
            };
            checker.scope.extend(bind.ident.name.clone(), scheme);
            checker.visit_expr(bind.expr)?;

            let ty_expr = checker.last_expr.take().unwrap();
            let inferred_ty = ty_expr.ty.clone();

            let unified_ty = self.unify(&tv, &inferred_ty, bind.ident.span.clone().into())?;

            self.subst = checker.subst;
            self.count = checker.count;

            let ty = if let Some(constraint) = &bind.constraint {
                self.unify(&unified_ty, constraint, bind.ident.span.clone().into())?
            } else {
                unified_ty
            };

            let scheme = self.generalize(&self.scope, &ty);

            self.scope.extend(bind.ident.name.clone(), scheme);

            self.last_binding = Some(typed::Binding {
                kind: match bind.kind {
                    untyped::BindingKind::Normal => typed::BindingKind::Normal,
                    untyped::BindingKind::Rec => typed::BindingKind::Rec,
                },
                ident: typed::Ident {
                    name: bind.ident.name.clone(),
                    span: bind.ident.span.clone(),
                    ty: ty.clone(),
                },
                expr: Box::new(ty_expr),
                span: bind.span.clone(),
                ty,
            });

            return Ok(());
        }

        checker.visit_expr(bind.expr)?;

        let ty_expr = checker.last_expr.take().unwrap();
        let inferred_ty = ty_expr.ty.clone();

        self.subst = checker.subst;
        self.count = checker.count;

        let ty = if let Some(constraint) = &bind.constraint {
            self.unify(&inferred_ty, constraint, bind.ident.span.clone().into())?
        } else {
            inferred_ty
        };

        let scheme = self.generalize(&self.scope, &ty);

        self.scope.extend(bind.ident.name.clone(), scheme);

        self.last_binding = Some(typed::Binding {
            kind: match bind.kind {
                untyped::BindingKind::Normal => typed::BindingKind::Normal,
                untyped::BindingKind::Rec => typed::BindingKind::Rec,
            },
            ident: typed::Ident {
                name: bind.ident.name.clone(),
                span: bind.ident.span.clone(),
                ty: ty.clone(),
            },
            expr: Box::new(ty_expr),
            span: bind.span.clone(),
            ty,
        });

        Ok(())
    }

    fn visit_num(&mut self, num: &'ast Num) -> Result<(), Self::Err> {
        self.last_expr = Some(typed::Expr {
            kind: Box::new(typed::ExprKind::Number(typed::Num(
                num.0,
                num.1.clone(),
                Type::Number,
            ))),
            span: num.1.clone(),
            ty: Type::Number,
        });
        Ok(())
    }

    fn visit_str(&mut self, s: &'ast Str) -> Result<(), Self::Err> {
        self.last_expr = Some(typed::Expr {
            kind: Box::new(typed::ExprKind::String(typed::Str(
                s.0.clone(),
                s.1.clone(),
                Type::String,
            ))),
            span: s.1.clone(),
            ty: Type::String,
        });
        Ok(())
    }

    fn visit_bool(&mut self, b: bool) -> Result<(), Self::Err> {
        self.last_expr = Some(typed::Expr {
            kind: Box::new(typed::ExprKind::Bool(b)),
            span: 0..0,
            ty: Type::Bool,
        });
        Ok(())
    }

    fn visit_unary_op(
        &mut self,
        op: &'ast UnaryOp,
        expr: &'ast Expr<'ast>,
    ) -> Result<(), Self::Err> {
        self.visit_expr(expr)?;
        let ty_expr = self.last_expr.take().unwrap();

        let inferred_ty = match op {
            UnaryOp::Neg => {
                let ty = self.unify(
                    &ty_expr.ty,
                    &Type::Number,
                    (ty_expr.span.start..expr.span().end).into(),
                )?;
                Ok(ty)
            }
            UnaryOp::Not => {
                let ty = self.unify(
                    &ty_expr.ty,
                    &Type::Bool,
                    (ty_expr.span.start..expr.span().end).into(),
                )?;
                Ok(ty)
            }
        }?;

        self.last_expr = Some(typed::Expr {
            kind: Box::new(typed::ExprKind::Unary {
                op: match op {
                    untyped::UnaryOp::Neg => typed::UnaryOp::Neg,
                    untyped::UnaryOp::Not => typed::UnaryOp::Not,
                },
                expr: ty_expr,
            }),
            span: expr.span(),
            ty: inferred_ty,
        });
        Ok(())
    }

    fn visit_binary_op(
        &mut self,
        op: &'ast BinaryOp,
        lhs: &'ast Expr<'ast>,
        rhs: &'ast Expr<'ast>,
    ) -> Result<(), Self::Err> {
        self.visit_expr(lhs)?;
        let ty_lhs = self.last_expr.take().unwrap();
        self.visit_expr(rhs)?;
        let ty_rhs = self.last_expr.take().unwrap();

        let span: SourceSpan = (lhs.span().start..rhs.span().end).into();

        let operand_ty: Type;
        let result_ty: Type;
        match op {
            BinaryOp::Add => {
                if ty_lhs.ty == Type::String || ty_rhs.ty == Type::String {
                    self.unify(&ty_lhs.ty, &Type::String, span)?;
                    self.unify(&ty_rhs.ty, &Type::String, span)?;
                    operand_ty = Type::String;
                    result_ty = Type::String;
                } else {
                    self.unify(&ty_lhs.ty, &Type::Number, span)?;
                    self.unify(&ty_rhs.ty, &Type::Number, span)?;
                    operand_ty = Type::Number;
                    result_ty = Type::Number;
                }
            }
            BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div => {
                self.unify(&ty_lhs.ty, &Type::Number, span)?;
                self.unify(&ty_rhs.ty, &Type::Number, span)?;
                operand_ty = Type::Number;
                result_ty = Type::Number;
            }
            BinaryOp::Eq
            | BinaryOp::NotEq
            | BinaryOp::Lt
            | BinaryOp::Gt
            | BinaryOp::LtEq
            | BinaryOp::GtEq => {
                operand_ty = self.unify(&ty_lhs.ty, &ty_rhs.ty, span)?;
                result_ty = Type::Bool;
            }
            BinaryOp::Dot => {
                unreachable!();
            }
        }

        self.last_expr = Some(typed::Expr {
            kind: Box::new(typed::ExprKind::Binary {
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
            }),
            span: (lhs.span().start..rhs.span().end),
            ty: result_ty,
        });
        Ok(())
    }

    fn visit_struct_expr(
        &mut self,
        type_name: &'ast untyped::TypeIdent,
        fields: &'ast [Binding<'ast>],
    ) -> Result<(), Self::Err> {
        let struct_span: SourceSpan = type_name.span.clone().into();
        let struct_def =
            self.struct_defs
                .get(&type_name.name)
                .ok_or_else(|| Error::UnknownType {
                    name: type_name.name.clone(),
                    span: struct_span,
                })?;

        let mut expr_fields: HashMap<String, Type> = struct_def
            .fields
            .iter()
            .map(|f| (f.ident.name.clone(), f.ty.clone()))
            .collect();

        let mut ty_fields = Vec::with_capacity(fields.len());

        for bind in fields {
            let mut checker = TypeChecker::new(
                self.subst.clone(),
                self.count,
                self.scope.clone(),
                None,
                self.struct_defs.clone(),
                None,
                None,
            );
            checker.visit_bind(bind)?;
            self.subst = checker.subst;
            self.count = checker.count;

            let ty_bind = checker.last_binding.take().unwrap();
            let inf_ty = ty_bind.ty.clone();

            if let Some(expr_ty) = expr_fields.remove(&bind.ident.name) {
                self.unify(&inf_ty, &expr_ty, bind.ident.span.clone().into())?;
                ty_fields.push(ty_bind);
            } else {
                return Err(Error::UndefinedIdent {
                    name: bind.ident.name.clone(),
                    span: bind.ident.span.clone().into(),
                });
            }
        }

        if !expr_fields.is_empty() {
            return Err(Error::UnexpectedType {
                t1: "Missing fields".to_string(),
                t2: format!("Expected: {:?}", expr_fields.keys()),
                span: struct_span,
            });
        }

        let struct_ty = Type::Struct(typed::TypeIdent {
            name: type_name.name.clone(),
            span: type_name.span.clone(),
            ty: Box::new(self.new_var()),
        });

        self.last_expr = Some(typed::Expr {
            kind: Box::new(typed::ExprKind::Struct {
                fields: ty_fields,
                ty: struct_ty.clone(),
            }),
            span: (type_name.span.start
                ..fields
                    .last()
                    .map_or(type_name.span.clone(), |b| b.span.clone())
                    .end),
            ty: struct_ty,
        });
        Ok(())
    }

    fn visit_struct_def(
        &mut self,
        struct_def: &'ast untyped::StructDef<'ast>,
    ) -> Result<(), Self::Err> {
        let name = struct_def.name.name.clone();
        if self.struct_defs.contains_key(&name) {
            return Err(Error::DuplicateDef {
                name,
                span: struct_def.span.clone().into(),
            });
        }

        let ty_type_ident = typed::TypeIdent {
            name: struct_def.name.name.clone(),
            span: struct_def.name.span.clone(),
            ty: Box::new(self.new_var()),
        };

        let mut ty_fields = Vec::new();
        for field in struct_def.fields.iter() {
            let field_tv = self.new_var();
            self.unify(&field_tv, &field.ty, field.span.clone().into())?;

            let ty_ident = typed::Ident {
                name: field.ident.name.clone(),
                span: field.ident.span.clone(),
                ty: field_tv.clone(),
            };
            ty_fields.push(typed::StructField {
                ident: ty_ident,
                ty: field_tv,
                span: field.span.clone(),
            });
        }

        let tv = self.new_var();
        let new_ty_struct_def = typed::StructDef {
            name: ty_type_ident,
            fields: ty_fields,
            span: struct_def.span.clone(),
            ty: tv,
        };

        self.struct_defs
            .insert(name.clone(), new_ty_struct_def.clone());

        Ok(())
    }

    fn visit_block_expr(
        &mut self,
        bindings: &'ast [Binding<'ast>],
        expr: &'ast Expr<'ast>,
    ) -> Result<(), Self::Err> {
        let mut scope = self.scope.clone();
        let mut ty_bindings = Vec::with_capacity(bindings.len());

        for bind in bindings {
            let mut checker = TypeChecker::new(
                self.subst.clone(),
                self.count,
                scope.clone(),
                None,
                self.struct_defs.clone(),
                None,
                None,
            );
            checker.visit_bind(bind)?;
            self.subst = checker.subst;
            self.count = checker.count;
            scope = checker.scope;
            ty_bindings.push(checker.last_binding.take().unwrap());
        }

        let mut checker = TypeChecker::new(
            self.subst.clone(),
            self.count,
            scope.clone(),
            None,
            self.struct_defs.clone(),
            None,
            None,
        );

        checker.visit_expr(expr)?;
        let ty_expr = checker.last_expr.take().unwrap();
        let expr_ty = ty_expr.ty.clone();
        self.subst = checker.subst;
        self.count = checker.count;
        self.scope = checker.scope;

        self.last_expr = Some(typed::Expr {
            kind: Box::new(typed::ExprKind::Block {
                bindings: ty_bindings,
                expr: ty_expr,
            }),
            span: bindings
                .first()
                .map_or(expr.span(), |b| b.span.clone())
                .start..expr.span().end,
            ty: expr_ty,
        });
        Ok(())
    }

    fn visit_app(&mut self, lhs: &'ast Expr<'ast>, rhs: &'ast Expr<'ast>) -> Result<(), Self::Err> {
        self.visit_expr(lhs)?;
        let ty_lhs = self.last_expr.take().unwrap();
        self.visit_expr(rhs)?;
        let ty_rhs = self.last_expr.take().unwrap();

        let func_ty = ty_lhs.ty.clone();
        let arg_ty = ty_rhs.ty.clone();

        let tv = self.new_var();
        let expected_func_ty = Type::Lambda(Box::new(arg_ty), Box::new(tv.clone()));

        self.unify(&func_ty, &expected_func_ty, lhs.span().into())?;
        let inferred_ty = self.apply(&tv);

        self.last_expr = Some(typed::Expr {
            kind: Box::new(typed::ExprKind::App {
                lhs: ty_lhs,
                rhs: ty_rhs,
            }),
            span: (lhs.span().start..rhs.span().end),
            ty: inferred_ty,
        });
        Ok(())
    }

    fn visit_lambda(
        &mut self,
        params: &'ast [Param<'ast>],
        body: &'ast Expr<'ast>,
    ) -> Result<(), Self::Err> {
        let mut scope = self.scope.clone();
        let mut ty_params = Vec::new();
        let mut param_tys = Vec::new();

        for param in params {
            let tv = self.new_var();
            if let Some(constraint) = &param.constraint {
                self.unify(&tv, constraint, param.ident.span.clone().into())?;
            }

            scope.extend(
                param.ident.name.clone(),
                Scheme {
                    vars: vec![],
                    ty: tv.clone(),
                },
            );
            param_tys.push(tv.clone());
            ty_params.push(typed::Param {
                ident: typed::Ident {
                    name: param.ident.name.clone(),
                    span: param.ident.span.clone(),
                    ty: tv.clone(),
                },
                ty: tv,
                span: param.span.clone(),
            });
        }

        let mut typer = TypeChecker {
            subst: self.subst.clone(),
            count: self.count,
            scope,
            program: None,
            struct_defs: self.struct_defs.clone(),
            last_expr: None,
            last_binding: None,
        };

        typer.visit_expr(body)?;
        let ty_body = typer.last_expr.take().unwrap();
        let body_ty = ty_body.ty.clone();

        self.subst = typer.subst;
        self.count = typer.count;

        let mut lambda_ty = body_ty;
        for param_ty in param_tys.iter().rev() {
            lambda_ty = Type::Lambda(Box::new(self.apply(param_ty)), Box::new(lambda_ty));
        }

        self.last_expr = Some(typed::Expr {
            kind: Box::new(typed::ExprKind::Lambda {
                params: ty_params,
                body: ty_body,
            }),
            span: params.first().map_or(body.span(), |p| p.span.clone()).start..body.span().end,
            ty: lambda_ty,
        });
        Ok(())
    }

    fn visit_list(&mut self, list: &'ast List<'ast>) -> Result<(), Self::Err> {
        let tv = self.new_var();
        let mut ty_exprs = Vec::with_capacity(list.exprs.len());

        for expr in list.exprs.iter() {
            self.visit_expr(expr)?;
            let ty_expr = self.last_expr.take().unwrap();
            self.unify(&tv, &ty_expr.ty, expr.span().into())?;
            ty_exprs.push(ty_expr);
        }

        let inferred_ty = Type::List(Box::new(self.apply(&tv)));

        self.last_expr = Some(typed::Expr {
            kind: Box::new(typed::ExprKind::List(typed::List {
                exprs: ty_exprs,
                span: list.span.clone(),
                ty: inferred_ty.clone(),
            })),
            span: list.span.clone(),
            ty: inferred_ty,
        });
        Ok(())
    }

    fn visit_struct_access(
        &mut self,
        expr: &'ast Expr<'ast>,
        ident: &'ast Ident,
    ) -> Result<(), Self::Err> {
        self.visit_expr(expr)?;
        let ty_expr = self.last_expr.take().unwrap();
        let expr_ty = ty_expr.ty.clone();

        let inferred_ty = if let Type::Struct(struct_ty_ident) = self.apply(&expr_ty) {
            let struct_def_span: SourceSpan = struct_ty_ident.span.clone().into();
            let struct_def =
                self.struct_defs
                    .get(&struct_ty_ident.name)
                    .ok_or_else(|| Error::UnknownType {
                        name: struct_ty_ident.name.clone(),
                        span: struct_def_span,
                    })?;
            struct_def
                .fields
                .iter()
                .find(|f| f.ident.name == ident.name)
                .map(|f| f.ty.clone())
                .ok_or_else(|| Error::UndefinedIdent {
                    name: ident.name.clone(),
                    span: ident.span.clone().into(),
                })?
        } else {
            return Err(Error::UnexpectedType {
                t1: format!("Expected struct type, found {}", expr_ty),
                t2: "Struct".to_string(),
                span: expr.span().into(),
            });
        };
        let inferred_field_ty = inferred_ty;

        self.last_expr = Some(typed::Expr {
            kind: Box::new(typed::ExprKind::StructAccess {
                expr: ty_expr,
                ident: typed::Ident {
                    name: ident.name.clone(),
                    span: ident.span.clone(),
                    ty: inferred_field_ty.clone(),
                },
            }),
            span: (expr.span().start..ident.span.end),
            ty: inferred_field_ty,
        });
        Ok(())
    }

    fn visit_if_expr(
        &mut self,
        cond: &'ast Expr<'ast>,
        then_expr: &'ast Expr<'ast>,
        else_expr: &'ast Expr<'ast>,
    ) -> Result<(), Self::Err> {
        self.visit_expr(cond)?;
        let ty_cond = self.last_expr.take().unwrap();
        self.unify(&ty_cond.ty, &Type::Bool, cond.span().into())?;

        self.visit_expr(then_expr)?;
        let ty_then = self.last_expr.take().unwrap();
        self.visit_expr(else_expr)?;
        let ty_else = self.last_expr.take().unwrap();
        self.unify(&ty_then.ty, &ty_else.ty, then_expr.span().into())?;

        let inferred_ty = ty_then.ty.clone();

        self.last_expr = Some(typed::Expr {
            kind: Box::new(typed::ExprKind::IfExpr {
                cond: ty_cond,
                then_expr: ty_then,
                else_expr: ty_else,
            }),
            span: (cond.span().start..else_expr.span().end),
            ty: inferred_ty,
        });
        Ok(())
    }

    fn visit_type(&mut self, _ty: &'ast Type) -> Result<(), Self::Err> {
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Scheme {
    vars: Vec<u32>,
    ty: Type,
}

#[derive(Clone, Debug, PartialEq, Default)]
pub struct Scope(HashMap<String, Scheme>);

impl Scope {
    pub fn new() -> Self {
        Scope(HashMap::new())
    }

    fn extend(&mut self, name: String, scheme: Scheme) {
        self.0.insert(name, scheme);
    }

    fn get(&self, name: &str) -> Option<&Scheme> {
        self.0.get(name)
    }
}
