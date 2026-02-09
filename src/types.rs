use crate::ast::{
    self, BinaryOp, Binding, Expr, Ident, List, Num, Param, Program, Str, StructDef, TypeIdent,
    UnaryOp, Visitor,
};
use miette::SourceSpan;
use std::collections::{HashMap, HashSet};
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Var(u32),
    Lambda(Box<Type>, Box<Type>),
    List(Box<Type>),
    Struct(ast::TypeIdent),
    Number,
    String,
    Bool,
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
    ty: Option<Type>,
    struct_defs: HashMap<String, StructDef>,
}

impl TypeChecker {
    fn new(
        subst: HashMap<u32, Type>,
        count: u32,
        scope: Scope,
        ty: Option<Type>,
        struct_defs: HashMap<String, StructDef>,
    ) -> Self {
        Self {
            subst,
            count,
            scope,
            ty,
            struct_defs,
        }
    }
    pub fn check(&mut self, program: &Program) -> Result<Type, Error> {
        self.visit_program(program)?;
        Ok(self.ty.take().unwrap())
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

    fn unify(&mut self, t1: &Type, t2: &Type, span: SourceSpan) -> Result<(), Error> {
        let t1 = self.apply(t1);
        let t2 = self.apply(t2);

        if t1 == t2 {
            return Ok(());
        }

        if let Type::Var(id) = t1 {
            return self.unify_var(id, &t2, span);
        }

        if let Type::Var(id) = t2 {
            return self.unify_var(id, &t1, span);
        }

        match (&t1, &t2) {
            (Type::Lambda(arg1, ret1), Type::Lambda(arg2, ret2)) => {
                self.unify(arg1, arg2, span)?;
                self.unify(ret1, ret2, span)?;
                Ok(())
            }
            (Type::List(t1), Type::List(t2)) => {
                self.unify(t1, t2, span)?;
                Ok(())
            }
            (Type::Struct(ident1), Type::Struct(ident2)) => {
                if ident1.name == ident2.name {
                    Ok(())
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
            return self.unify(&t, ty, span);
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

    fn visit_program(&mut self, program: &'ast Program) -> Result<(), Self::Err> {
        for s in &program.structs {
            self.visit_struct_def(s)?;
        }
        self.visit_expr(&program.expr)
    }

    fn visit_ident(&mut self, ident: &'ast Ident) -> Result<(), Self::Err> {
        if let Some(scheme) = self.scope.get(&ident.name).cloned() {
            self.ty = Some(self.instantiate(&scheme));
            Ok(())
        } else {
            Err(Error::UndefinedIdent {
                name: ident.name.to_string(),
                span: ident.span.clone().into(),
            })
        }
    }

    fn visit_bind(&mut self, bind: &'ast Binding) -> Result<(), Self::Err> {
        let mut checker = TypeChecker::new(
            self.subst.clone(),
            self.count,
            self.scope.clone(),
            None,
            self.struct_defs.clone(),
        );

        checker.visit_expr(&bind.expr)?;
        let inferred_ty = checker.ty.take().unwrap();
        self.subst = checker.subst;
        self.count = checker.count;

        let ty = if let Some(constraint_ty) = &bind.constraint {
            self.unify(&inferred_ty, constraint_ty, bind.ident.span.clone().into())?;
            constraint_ty.clone()
        } else {
            inferred_ty
        };

        let scheme = self.generalize(&self.scope, &ty);
        self.scope.extend(bind.ident.name.clone(), scheme);
        self.ty = Some(ty);

        Ok(())
    }

    fn visit_num(&mut self, _num: &'ast Num) -> Result<(), Self::Err> {
        self.ty = Some(Type::Number);
        Ok(())
    }

    fn visit_str(&mut self, _str: &'ast Str) -> Result<(), Self::Err> {
        self.ty = Some(Type::String);
        Ok(())
    }

    fn visit_bool(&mut self, _b: bool) -> Result<(), Self::Err> {
        self.ty = Some(Type::Bool);
        Ok(())
    }

    fn visit_unary_op(&mut self, op: &'ast UnaryOp, expr: &'ast Expr) -> Result<(), Self::Err> {
        self.visit_expr(expr)?;
        let ty = self.ty.take().unwrap();
        let inferred_ty = match op {
            UnaryOp::Neg => {
                self.unify(&ty, &Type::Number, expr.span().into())?;
                Ok(Type::Number)
            }
            UnaryOp::Not => {
                self.unify(&ty, &Type::Bool, expr.span().into())?;
                Ok(Type::Bool)
            }
        }?;
        self.ty = Some(inferred_ty);
        Ok(())
    }

    fn visit_binary_op(
        &mut self,
        op: &'ast BinaryOp,
        lhs: &'ast Expr,
        rhs: &'ast Expr,
    ) -> Result<(), Self::Err> {
        self.visit_expr(lhs)?;
        let lhs_ty = self.ty.take().unwrap();
        self.visit_expr(rhs)?;
        let rhs_ty = self.ty.take().unwrap();

        let inferred_ty = match op {
            BinaryOp::Add => {
                if lhs_ty == Type::String || rhs_ty == Type::String {
                    self.unify(&lhs_ty, &Type::String, lhs.span().into())?;
                    self.unify(&rhs_ty, &Type::String, rhs.span().into())?;
                    Ok(Type::String)
                } else {
                    self.unify(&lhs_ty, &Type::Number, lhs.span().into())?;
                    self.unify(&rhs_ty, &Type::Number, rhs.span().into())?;
                    Ok(Type::Number)
                }
            }
            BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div => {
                self.unify(&lhs_ty, &Type::Number, lhs.span().into())?;
                self.unify(&rhs_ty, &Type::Number, rhs.span().into())?;
                Ok(Type::Number)
            }
            BinaryOp::Eq
            | BinaryOp::NotEq
            | BinaryOp::Lt
            | BinaryOp::Gt
            | BinaryOp::LtEq
            | BinaryOp::GtEq => {
                self.unify(&lhs_ty, &rhs_ty, lhs.span().into())?;
                Ok(Type::Bool)
            }
            BinaryOp::Dot => {
                unreachable!();
            }
        }?;
        self.ty = Some(inferred_ty);
        Ok(())
    }

    fn visit_struct_expr(
        &mut self,
        type_name: &'ast TypeIdent,
        fields: &'ast [Binding],
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

        let mut actual_fields = HashMap::new();

        for bind in fields {
            let mut checker = TypeChecker::new(
                self.subst.clone(),
                self.count,
                self.scope.clone(),
                None,
                self.struct_defs.clone(),
            );
            checker.visit_bind(bind)?;
            self.subst = checker.subst;
            self.count = checker.count;

            let inf_ty = checker.ty.take().unwrap();

            if let Some(expr_ty) = expr_fields.remove(&bind.ident.name) {
                self.unify(&inf_ty, &expr_ty, bind.ident.span.clone().into())?;
                actual_fields.insert(bind.ident.name.clone(), inf_ty);
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

        self.ty = Some(Type::Struct(type_name.clone()));
        Ok(())
    }

    fn visit_struct_def(&mut self, struct_def: &'ast StructDef) -> Result<(), Self::Err> {
        let name = struct_def.name.name.clone();
        if self.struct_defs.contains_key(&name) {
            return Err(Error::DuplicateDef {
                name,
                span: struct_def.span.clone().into(),
            });
        }
        self.struct_defs.insert(name, struct_def.clone());
        Ok(())
    }

    fn visit_block_expr(
        &mut self,
        bindings: &'ast [Binding],
        expr: &'ast Expr,
    ) -> Result<(), Self::Err> {
        let mut scope = self.scope.clone();
        for bind in bindings {
            let mut checker = TypeChecker::new(
                self.subst.clone(),
                self.count,
                scope.clone(),
                None,
                self.struct_defs.clone(),
            );
            checker.visit_bind(bind)?;
            self.subst = checker.subst;
            self.count = checker.count;
            scope = checker.scope;
        }

        let mut checker = TypeChecker::new(
            self.subst.clone(),
            self.count,
            scope.clone(),
            None,
            self.struct_defs.clone(),
        );

        checker.visit_expr(expr)?;
        let ty = checker.ty.take().unwrap();
        self.subst = checker.subst;
        self.count = checker.count;
        self.ty = Some(ty);
        Ok(())
    }

    fn visit_app(&mut self, lhs: &'ast Expr, rhs: &'ast Expr) -> Result<(), Self::Err> {
        self.visit_expr(lhs)?;
        let func_type = self.ty.take().unwrap();
        self.visit_expr(rhs)?;
        let arg_type = self.ty.take().unwrap();

        let ret_type = self.new_var();
        let expected_func_type = Type::Lambda(Box::new(arg_type), Box::new(ret_type.clone()));

        self.unify(&func_type, &expected_func_type, lhs.span().into())?;
        self.ty = Some(ret_type);
        Ok(())
    }

    fn visit_lambda(&mut self, params: &'ast [Param], body: &'ast Expr) -> Result<(), Self::Err> {
        let mut scope = self.scope.clone();
        let mut param_types = Vec::new();

        for param in params {
            let param_type = self.new_var();
            if let Some(constraint_ty) = &param.constraint {
                self.unify(&param_type, constraint_ty, param.ident.span.clone().into())?;
            }

            scope.extend(
                param.ident.name.clone(),
                Scheme {
                    vars: vec![],
                    ty: param_type.clone(),
                },
            );
            param_types.push(param_type);
        }

        let mut typer = TypeChecker {
            subst: self.subst.clone(),
            count: self.count,
            scope,
            ty: None,
            struct_defs: self.struct_defs.clone(),
        };

        typer.visit_expr(body)?;
        let body_type = typer.ty.take().unwrap();
        self.subst = typer.subst;
        self.count = typer.count;

        let mut lam_type = body_type;
        for param_type in param_types.iter().rev() {
            lam_type = Type::Lambda(Box::new(param_type.clone()), Box::new(lam_type));
        }

        self.ty = Some(lam_type);
        Ok(())
    }

    fn visit_list(&mut self, list: &'ast List) -> Result<(), Self::Err> {
        let elem_type = self.new_var();

        for expr in &list.exprs {
            self.visit_expr(expr)?;
            let ty = self.ty.take().unwrap();
            self.unify(&elem_type, &ty, expr.span().into())?;
        }

        self.ty = Some(Type::List(Box::new(elem_type)));
        Ok(())
    }

    fn visit_struct_access(
        &mut self,
        expr: &'ast Expr,
        ident: &'ast Ident,
    ) -> Result<(), Self::Err> {
        self.visit_expr(expr)?;
        let ty = self.ty.take().unwrap();

        let inferred_field_ty = if let Type::Struct(struct_type_ident) = self.apply(&ty) {
            let struct_def_span: SourceSpan = struct_type_ident.span.clone().into();
            let struct_def = self
                .struct_defs
                .get(&struct_type_ident.name)
                .ok_or_else(|| Error::UnknownType {
                    name: struct_type_ident.name.clone(),
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
                t1: format!("Expected struct type, found {}", ty),
                t2: "Struct".to_string(),
                span: expr.span().into(),
            });
        };

        self.ty = Some(inferred_field_ty);
        Ok(())
    }

    fn visit_if_expr(
        &mut self,
        cond: &'ast Expr,
        then_expr: &'ast Expr,
        else_expr: &'ast Expr,
    ) -> Result<(), Self::Err> {
        self.visit_expr(cond)?;
        let cond_type = self.ty.take().unwrap();
        self.unify(&cond_type, &Type::Bool, cond.span().into())?;

        self.visit_expr(then_expr)?;
        let then_type = self.ty.take().unwrap();
        self.visit_expr(else_expr)?;
        let else_type = self.ty.take().unwrap();
        self.unify(&then_type, &else_type, then_expr.span().into())?;

        self.ty = Some(then_type);
        Ok(())
    }

    fn visit_type(&mut self, ty: &'ast Type) -> Result<(), Self::Err> {
        self.ty = Some(ty.clone());
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
