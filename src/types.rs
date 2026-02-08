use crate::ast::*;
use miette::SourceSpan;
use std::collections::{HashMap, HashSet};
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Var(u32),
    Lambda(Box<Type>, Box<Type>),
    List(Box<Type>),
    Map(HashMap<String, Type>),
    Number,
    String,
    Bool,
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::Var(n) => write!(f, "t{}", n),
            Type::Lambda(arg, ret) => write!(f, "({} -> {})", arg, ret),
            Type::List(t) => write!(f, "[{}]", t),
            Type::Map(fields) => {
                let mut s = String::new();
                for (name, ty) in fields {
                    s.push_str(&format!("{}: {}, ", name, ty));
                }
                write!(f, "{{{}}}", s.trim_end_matches(", "))
            }
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
    }
}

#[derive(Default)]
pub struct TypeChecker {
    subst: HashMap<u32, Type>,
    count: u32,
    scope: Scope,
    ty: Option<Type>,
}

impl TypeChecker {
    fn new(subst: HashMap<u32, Type>, count: u32, scope: Scope, ty: Option<Type>) -> Self {
        Self {
            subst,
            count,
            scope,
            ty,
        }
    }
    pub fn check(&mut self, expr: &Expr) -> Result<Type, Error> {
        self.visit_expr(expr)?;
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
            Type::Map(fields) => {
                let mut new_fields = HashMap::new();
                for (name, ty) in fields {
                    new_fields.insert(name.clone(), self.apply(ty));
                }
                Type::Map(new_fields)
            }
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
            (Type::Map(f1), Type::Map(f2)) => {
                let mut f1 = f1.clone();
                let f2 = f2.clone();
                for (name, ty) in f2 {
                    if let Some(other_ty) = f1.remove(&name) {
                        self.unify(&ty, &other_ty, span)?;
                    }
                }
                if f1.is_empty() {
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
            Type::Map(fields) => fields.values().any(|t| self.occurs(id, t)),
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
            Type::Map(fields) => {
                let mut new_fields = HashMap::new();
                for (name, ty) in fields {
                    new_fields.insert(name.clone(), self.apply_scheme(subst, ty));
                }
                Type::Map(new_fields)
            }
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
            Type::Map(fields) => {
                for ty in fields.values() {
                    free_vars.extend(self.ftv(ty));
                }
            }
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
        let mut checker =
            TypeChecker::new(self.subst.clone(), self.count, self.scope.clone(), None);

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

    fn visit_map(&mut self, bindings: &'ast [Binding]) -> Result<(), Self::Err> {
        let mut fields = HashMap::new();
        let mut scope = self.scope.clone();

        for bind in bindings {
            let mut checker = TypeChecker::new(self.subst.clone(), self.count, scope.clone(), None);

            checker.visit_bind(bind)?;
            self.subst = checker.subst;
            self.count = checker.count;
            scope = checker.scope;

            let ty = self.instantiate(scope.get(&bind.ident.name).unwrap());
            fields.insert(bind.ident.name.clone(), ty);
        }
        self.ty = Some(Type::Map(fields));
        Ok(())
    }

    fn visit_block_expr(
        &mut self,
        bindings: &'ast [Binding],
        expr: &'ast Expr,
    ) -> Result<(), Self::Err> {
        let mut scope = self.scope.clone();
        for bind in bindings {
            let mut checker = TypeChecker::new(self.subst.clone(), self.count, scope.clone(), None);
            checker.visit_bind(bind)?;
            self.subst = checker.subst;
            self.count = checker.count;
            scope = checker.scope;
        }

        let mut checker = TypeChecker::new(self.subst.clone(), self.count, scope.clone(), None);

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

    fn visit_map_access(&mut self, expr: &'ast Expr, ident: &'ast Ident) -> Result<(), Self::Err> {
        self.visit_expr(expr)?;
        let ty = self.ty.take().unwrap();

        let mut fields = HashMap::new();
        let new_var = self.new_var();
        fields.insert(ident.name.clone(), new_var.clone());

        let expected_ty = Type::Map(fields);
        self.unify(&ty, &expected_ty, expr.span().into())?;
        self.ty = Some(new_var);
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
