use crate::ast::{
    self, BinaryOp, Binding, Expr, Num, Param, Program, Str, StructDef, TypeIdent, UnaryOp, Visitor,
};
use crate::types::Type;
use miette::SourceSpan;
use rpds::HashTrieMap;
use std::cell::OnceCell;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

#[derive(Debug, Clone)]
pub struct Thunk {
    expr: Box<Expr>,
    scope: Scope,
    value: OnceCell<Result<Value, Error>>,
}

impl Thunk {
    pub fn new(expr: Box<Expr>, scope: Scope) -> Self {
        Self {
            expr,
            scope,
            value: OnceCell::new(),
        }
    }

    pub fn force(self: &Rc<Self>, walker: &mut TreeWalker) -> Result<Value, Error> {
        self.value
            .get_or_init(|| {
                let call_stack =
                    std::mem::replace(&mut walker.call_stack, vec![self.scope.clone()]);
                let result = walker
                    .visit_expr(&self.expr)
                    .and_then(|_| walker.stack_pop());
                walker.call_stack = call_stack;
                result
            })
            .clone()
    }
}

#[derive(Debug, Clone)]
pub enum Value {
    Number(f64),
    String(Rc<String>),
    Bool(bool),
    Struct(Rc<String>, Rc<HashMap<String, Value>>),
    List(Rc<Vec<Value>>),
    Lambda {
        params: Rc<Vec<String>>,
        body: Rc<Expr>,
        scope: Scope,
    },
    Thunk(Rc<Thunk>),
    Unit,
    RecThunk(Rc<RefCell<Option<Rc<Thunk>>>>),
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Value::Number(l), Value::Number(r)) => l == r,
            (Value::String(l), Value::String(r)) => l == r,
            (Value::Struct(n1, f1), Value::Struct(n2, f2)) => n1 == n2 && f1 == f2,
            (Value::List(l), Value::List(r)) => l == r,
            (
                Value::Lambda {
                    params: p1,
                    body: b1,
                    scope: c1,
                },
                Value::Lambda {
                    params: p2,
                    body: b2,
                    scope: c2,
                },
            ) => p1 == p2 && b1 == b2 && c1 == c2,
            (Value::Unit, Value::Unit) => true,
            (Value::Thunk(l), Value::Thunk(r)) => Rc::ptr_eq(l, r),
            (Value::RecThunk(l), Value::RecThunk(r)) => Rc::ptr_eq(l, r),
            _ => false,
        }
    }
}

#[derive(thiserror::Error, miette::Diagnostic, Debug, PartialEq, Clone)]
pub enum Error {
    #[error("feature not implemented: {0}")]
    NotImplemented(String, #[label] SourceSpan),
    #[error("identifier '{0}' not found")]
    IdentifierNotFound(String),
    #[error("stack underflow")]
    StackUnderflow,
    #[error("tried accessing a struct with invalid field")]
    InvalidStructAccess(#[label] SourceSpan),
}

#[derive(Debug, PartialEq, Clone, Default)]
pub struct Scope {
    vars: HashTrieMap<String, Value>,
}

impl Scope {
    #[inline]
    pub fn get(&self, name: &str) -> Result<&Value, Error> {
        self.vars
            .get(name)
            .ok_or(Error::IdentifierNotFound(name.to_owned()))
    }

    #[inline]
    pub fn insert(&self, key: String, value: Value) -> Self {
        Self {
            vars: self.vars.insert(key, value),
        }
    }
}

pub struct TreeWalker {
    call_stack: Vec<Scope>,
    stack: Vec<Value>,
}

impl Default for TreeWalker {
    fn default() -> Self {
        Self {
            call_stack: vec![Scope::default()],
            stack: Default::default(),
        }
    }
}

impl TreeWalker {
    pub fn consume(mut self) -> Result<Value, Error> {
        let value = self.stack_pop()?;
        self.force_consume(value)
    }

    fn force_consume(&mut self, value: Value) -> Result<Value, Error> {
        let value = self.force(value)?;

        match value {
            Value::List(values) => {
                let mut list = Vec::with_capacity(values.len());
                for val in values.iter() {
                    list.push(self.force_consume(val.clone())?);
                }
                Ok(Value::List(Rc::new(list)))
            }
            Value::Struct(name, value) => {
                let mut map = HashMap::with_capacity(value.len());
                for (key, val) in value.iter() {
                    map.insert(key.clone(), self.force_consume(val.clone())?);
                }
                Ok(Value::Struct(name, Rc::new(map)))
            }
            _ => Ok(value),
        }
    }

    #[inline]
    fn force(&mut self, value: Value) -> Result<Value, Error> {
        match value {
            Value::Thunk(thunk) => thunk.force(self),
            Value::RecThunk(thunk) => {
                if let Some(thunk) = thunk.borrow().as_ref() {
                    thunk.force(self)
                } else {
                    Err(Error::NotImplemented(
                        "Recursive thunk not defined".to_string(),
                        SourceSpan::new(0.into(), 0),
                    ))
                }
            }
            _ => Ok(value),
        }
    }

    #[inline]
    fn scope(&self) -> Result<&Scope, Error> {
        self.call_stack.last().ok_or(Error::StackUnderflow)
    }

    #[inline]
    fn scope_replace(&mut self, scope: Scope) {
        *self.call_stack.last_mut().unwrap() = scope;
    }

    #[inline]
    fn scope_push(&mut self, scope: Scope) {
        self.call_stack.push(scope)
    }

    #[inline]
    fn scope_pop(&mut self) -> Result<Scope, Error> {
        self.call_stack.pop().ok_or(Error::StackUnderflow)
    }

    #[inline]
    fn stack_push(&mut self, value: Value) {
        self.stack.push(value)
    }

    #[inline]
    fn stack_pop(&mut self) -> Result<Value, Error> {
        self.stack.pop().ok_or(Error::StackUnderflow)
    }
}

impl<'ast> ast::Visitor<'ast> for TreeWalker {
    type Err = Error;

    fn visit_program(&mut self, program: &'ast Program) -> Result<(), Self::Err> {
        for s in &program.structs {
            self.visit_struct_def(s)?;
        }
        self.visit_expr(&program.expr)
    }

    fn visit_ident(&mut self, ident: &'ast ast::Ident) -> Result<(), Self::Err> {
        let val = self.scope()?.get(&ident.name)?.clone();
        let forced_val = self.force(val)?;
        self.stack_push(forced_val);
        Ok(())
    }

    fn visit_bind(&mut self, bind: &'ast Binding) -> Result<(), Self::Err> {
        let scope = self.scope()?.clone();

        if bind.kind == ast::BindingKind::Rec {
            let slot = Rc::new(RefCell::new(None));
            let rec_name = bind.ident.name.clone();
            let rec_scope = scope.insert(rec_name.clone(), Value::RecThunk(slot.clone()));

            let thunk = Rc::new(Thunk::new(bind.expr.clone(), rec_scope));

            *slot.borrow_mut() = Some(thunk.clone());

            self.scope_replace(scope.insert(rec_name, Value::Thunk(thunk)));
            return Ok(());
        }

        let thunk = Rc::new(Thunk::new(bind.expr.clone(), scope.clone()));
        let new_scope = scope.insert(bind.ident.name.clone(), Value::Thunk(thunk));
        self.scope_replace(new_scope);
        Ok(())
    }

    fn visit_num(&mut self, num: &'ast Num) -> Result<(), Self::Err> {
        self.stack_push(Value::Number(num.0));
        Ok(())
    }

    fn visit_str(&mut self, str: &'ast Str) -> Result<(), Self::Err> {
        self.stack_push(Value::String(Rc::new(str.0.clone())));
        Ok(())
    }

    fn visit_bool(&mut self, b: bool) -> Result<(), Self::Err> {
        self.stack_push(Value::Bool(b));
        Ok(())
    }

    fn visit_unary_op(&mut self, op: &'ast UnaryOp, expr: &'ast Expr) -> Result<(), Self::Err> {
        self.visit_expr(expr)?;
        let val = self.stack_pop()?;
        let forced_val = self.force(val)?;

        let result = match op {
            UnaryOp::Neg => match forced_val {
                Value::Number(n) => Ok(Value::Number(-n)),
                _ => Err(Error::NotImplemented(
                    format!("Unary op {:?} for value {:?}", op, forced_val),
                    expr.span().into(),
                )),
            },
            UnaryOp::Not => match forced_val {
                Value::Number(n) => Ok(Value::Bool(n == 0.0)),
                Value::Bool(b) => Ok(Value::Bool(!b)),
                _ => Err(Error::NotImplemented(
                    format!("Unary op {:?} for value {:?}", op, forced_val),
                    expr.span().into(),
                )),
            },
        };

        self.stack_push(result?);
        Ok(())
    }

    fn visit_binary_op(
        &mut self,
        op: &'ast BinaryOp,
        lhs: &'ast Expr,
        rhs: &'ast Expr,
    ) -> Result<(), Self::Err> {
        self.visit_expr(lhs)?;
        self.visit_expr(rhs)?;
        let rhs_val = self.stack_pop()?;
        let rhs_forced = self.force(rhs_val)?;
        let lhs_val = self.stack_pop()?;
        let lhs_forced = self.force(lhs_val)?;

        let result = match op {
            BinaryOp::Add => match (lhs_forced, rhs_forced) {
                (Value::Number(l), Value::Number(r)) => Ok(Value::Number(l + r)),
                (Value::String(l), Value::String(r)) => {
                    Ok(Value::String(Rc::new(l.to_string() + &r)))
                }
                (l, r) => Err(Error::NotImplemented(
                    format!("Binary op {:?} for values {:?} and {:?}", op, l, r),
                    (lhs.span().start..rhs.span().end).into(),
                )),
            },
            BinaryOp::Sub => match (lhs_forced, rhs_forced) {
                (Value::Number(l), Value::Number(r)) => Ok(Value::Number(l - r)),
                (l, r) => Err(Error::NotImplemented(
                    format!("Binary op {:?} for values {:?} and {:?}", op, l, r),
                    (lhs.span().start..rhs.span().end).into(),
                )),
            },
            BinaryOp::Mul => match (lhs_forced, rhs_forced) {
                (Value::Number(l), Value::Number(r)) => Ok(Value::Number(l * r)),
                (l, r) => Err(Error::NotImplemented(
                    format!("Binary op {:?} for values {:?} and {:?}", op, l, r),
                    (lhs.span().start..rhs.span().end).into(),
                )),
            },
            BinaryOp::Div => match (lhs_forced, rhs_forced) {
                (Value::Number(l), Value::Number(r)) => Ok(Value::Number(l / r)),
                (l, r) => Err(Error::NotImplemented(
                    format!("Binary op {:?} for values {:?} and {:?}", op, l, r),
                    (lhs.span().start..rhs.span().end).into(),
                )),
            },
            BinaryOp::Eq => Ok(Value::Bool(lhs_forced == rhs_forced)),
            BinaryOp::NotEq => Ok(Value::Bool(lhs_forced != rhs_forced)),
            BinaryOp::Lt => match (lhs_forced, rhs_forced) {
                (Value::Number(l), Value::Number(r)) => Ok(Value::Bool(l < r)),
                (l, r) => Err(Error::NotImplemented(
                    format!("Binary op {:?} for values {:?} and {:?}", op, l, r),
                    (lhs.span().start..rhs.span().end).into(),
                )),
            },
            BinaryOp::Gt => match (lhs_forced, rhs_forced) {
                (Value::Number(l), Value::Number(r)) => Ok(Value::Bool(l > r)),
                (l, r) => Err(Error::NotImplemented(
                    format!("Binary op {:?} for values {:?} and {:?}", op, l, r),
                    (lhs.span().start..rhs.span().end).into(),
                )),
            },
            BinaryOp::LtEq => match (lhs_forced, rhs_forced) {
                (Value::Number(l), Value::Number(r)) => Ok(Value::Bool(l <= r)),
                (l, r) => Err(Error::NotImplemented(
                    format!("Binary op {:?} for values {:?} and {:?}", op, l, r),
                    (lhs.span().start..rhs.span().end).into(),
                )),
            },
            BinaryOp::GtEq => match (lhs_forced, rhs_forced) {
                (Value::Number(l), Value::Number(r)) => Ok(Value::Bool(l >= r)),
                (l, r) => Err(Error::NotImplemented(
                    format!("Binary op {:?} for values {:?} and {:?}", op, l, r),
                    (lhs.span().start..rhs.span().end).into(),
                )),
            },
            BinaryOp::Dot => {
                unreachable!();
            }
        };

        self.stack_push(result?);
        Ok(())
    }

    fn visit_struct_expr(
        &mut self,
        ty_name: &'ast TypeIdent,
        fields: &'ast [Binding],
    ) -> Result<(), Self::Err> {
        self.scope_push(self.scope()?.clone());

        for bind in fields {
            self.visit_bind(bind)?;
        }

        let final_scope = self.scope()?.clone();
        let mut fields_map = HashMap::new();
        for bind in fields {
            let val = final_scope.get(&bind.ident.name)?.clone();
            let forced_val = self.force(val)?;
            fields_map.insert(bind.ident.name.clone(), forced_val);
        }

        self.scope_pop()?;
        self.stack_push(Value::Struct(
            Rc::new(ty_name.name.clone()),
            Rc::new(fields_map),
        ));
        Ok(())
    }

    fn visit_app(&mut self, lhs: &'ast Expr, rhs: &'ast Expr) -> Result<(), Self::Err> {
        self.visit_expr(lhs)?;
        let val = self.stack_pop()?;
        let forced_val = self.force(val)?;
        let scope = self.scope()?.clone();
        let arg_thunk = Rc::new(Thunk::new(Box::new(rhs.clone()), scope));
        let arg_val = Value::Thunk(arg_thunk);

        let result_val = match forced_val {
            Value::Lambda {
                params,
                body,
                scope,
            } => {
                if params.is_empty() {
                    return Err(Error::NotImplemented(
                        "Too many arguments for lambda".to_string(),
                        (lhs.span().start..rhs.span().end).into(),
                    ));
                }

                let mut params_clone = (*params).clone();
                let param_name = params_clone.remove(0);

                let new_scope = scope.insert(param_name, arg_val);
                self.scope_push(new_scope);

                if !params_clone.is_empty() {
                    let new_lambda_scope = self.scope()?.clone();
                    let new_lambda = Value::Lambda {
                        params: Rc::new(params_clone),
                        body,
                        scope: new_lambda_scope,
                    };
                    self.scope_pop()?;
                    new_lambda
                } else {
                    self.visit_expr(&body)?;
                    let final_result = self.stack_pop()?;
                    self.scope_pop()?;
                    final_result
                }
            }
            _ => {
                return Err(Error::NotImplemented(
                    format!("Cannot call value of type {:?}", forced_val),
                    (lhs.span().start..rhs.span().end).into(),
                ));
            }
        };

        self.stack_push(result_val);
        Ok(())
    }

    fn visit_block_expr(
        &mut self,
        bindings: &'ast [Binding],
        expr: &'ast Expr,
    ) -> Result<(), Self::Err> {
        self.scope_push(self.scope()?.clone());

        for binding in bindings {
            self.visit_bind(binding)?;
        }

        self.visit_expr(expr)?;
        let value = self.stack_pop()?;

        self.scope_pop()?;

        self.stack_push(value);
        Ok(())
    }

    fn visit_lambda(&mut self, params: &'ast [Param], body: &'ast Expr) -> Result<(), Self::Err> {
        let mut scope = self.scope()?.clone();
        let mut names = vec![];

        for param in params {
            names.push(param.ident.name.clone());
            if let Some(default) = &param.expr {
                self.visit_expr(default)?;
                let default = self.stack_pop()?;
                scope = scope.insert(param.ident.name.clone(), default);
            }
        }

        let lambda = Value::Lambda {
            params: Rc::new(names),
            body: Rc::new(body.clone()),
            scope,
        };
        self.stack_push(lambda);
        Ok(())
    }

    fn visit_list(&mut self, list: &'ast ast::List) -> Result<(), Self::Err> {
        let mut result = vec![];
        let scope = self.scope()?.clone();
        for expr in &list.exprs {
            let thunk = Rc::new(Thunk::new(Box::new(expr.clone()), scope.clone()));
            result.push(Value::Thunk(thunk));
        }
        self.stack_push(Value::List(Rc::new(result)));
        Ok(())
    }

    fn visit_struct_access(
        &mut self,
        expr: &'ast Expr,
        ident: &'ast ast::Ident,
    ) -> Result<(), Self::Err> {
        self.visit_expr(expr)?;
        let val = self.stack_pop()?;
        let forced_val = self.force(val)?;
        let result = match forced_val {
            Value::Struct(_, map) => map
                .get(&ident.name)
                .cloned()
                .ok_or(Error::InvalidStructAccess(ident.span.clone().into())),
            _ => {
                unreachable!()
            }
        }?;

        self.stack_push(result);
        Ok(())
    }

    fn visit_if_expr(
        &mut self,
        cond: &'ast Expr,
        then_expr: &'ast Expr,
        else_expr: &'ast Expr,
    ) -> Result<(), Self::Err> {
        self.visit_expr(cond)?;
        let cond_val = self.stack_pop()?;
        let forced_cond = self.force(cond_val)?;

        let is_truthy = match forced_cond {
            Value::Bool(b) => b,
            _ => {
                return Err(Error::NotImplemented(
                    "Condition in if/else must be a bool".to_string(),
                    cond.span().into(),
                ));
            }
        };

        if is_truthy {
            self.visit_expr(then_expr)?;
        } else {
            self.visit_expr(else_expr)?;
        }

        Ok(())
    }

    fn visit_type(&mut self, _ty: &'ast Type) -> Result<(), Self::Err> {
        // no runtime type checking
        Ok(())
    }

    fn visit_struct_def(&mut self, _struct_def: &'ast StructDef) -> Result<(), Self::Err> {
        Ok(())
    }
}
