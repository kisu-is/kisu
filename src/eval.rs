use crate::ast::{self, BinaryOp, Binding, Expr, Num, Str, UnaryOp};
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Number(Num),
    String(Str),
    Map(HashMap<String, Value>),
    List(Vec<Value>),
    Lambda {
        params: Vec<String>,
        body: Box<Expr>,
        closure: Closure,
    },
    Void,
}

#[derive(thiserror::Error, Debug, PartialEq)]
pub enum Error {
    #[error("feature not implemented")]
    NotImplemented(String),
    #[error("identifier '{0}' not found")]
    IdentifierNotFound(String),
    #[error("stack underflow")]
    StackUnderflow,
    #[error("tried accessing a map with invalid parameters")]
    InvalidMapAccess,
}

#[derive(Debug, PartialEq, Default, Clone)]
pub struct Scope {
    pub vars: HashMap<String, Value>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Closure {
    scope_stack: Vec<Scope>,
}

impl Default for Closure {
    fn default() -> Self {
        Self {
            scope_stack: vec![Scope::default()],
        }
    }
}

impl Closure {
    #[inline]
    fn scope_get(&self, name: &str) -> Result<&Value, Error> {
        self.scope_stack
            .iter()
            .rev()
            .find_map(|scope| scope.vars.get(name))
            .ok_or(Error::IdentifierNotFound(name.to_owned()))
    }

    #[inline]
    fn scope_insert(&mut self, key: String, value: Value) -> Result<(), Error> {
        let scope = self.scope_stack.last_mut().ok_or(Error::StackUnderflow)?;
        scope.vars.insert(key, value);
        Ok(())
    }

    #[inline]
    fn scope_push(&mut self) {
        self.scope_stack.push(Scope::default());
    }

    #[inline]
    fn scope_pop(&mut self) -> Result<(), Error> {
        self.scope_stack.pop().ok_or(Error::StackUnderflow)?;
        Ok(())
    }
}

pub struct TreeWalker {
    call_stack: Vec<Closure>,
    stack: Vec<Value>,
}

impl Default for TreeWalker {
    fn default() -> Self {
        Self {
            call_stack: vec![Closure::default()],
            stack: Default::default(),
        }
    }
}

impl TreeWalker {
    pub fn consume(mut self) -> Result<Value, Error> {
        self.stack_pop()
    }

    #[inline]
    fn closure(&mut self) -> Result<&Closure, Error> {
        self.call_stack.last().ok_or(Error::StackUnderflow)
    }

    #[inline]
    fn closure_mut(&mut self) -> Result<&mut Closure, Error> {
        self.call_stack.last_mut().ok_or(Error::StackUnderflow)
    }

    #[inline]
    fn closure_push(&mut self, closure: Closure) {
        self.call_stack.push(closure)
    }

    #[inline]
    fn closure_pop(&mut self) -> Result<Closure, Error> {
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

    fn visit_ident(&mut self, ident: &'ast ast::Ident) -> Result<(), Self::Err> {
        let value = self.closure_mut()?.scope_get(&ident.name)?.clone();
        self.stack_push(value);
        Ok(())
    }

    fn visit_bind(&mut self, bind: &'ast Binding) -> Result<(), Self::Err> {
        self.visit_expr(&bind.expr)?;
        let value = self.stack_pop()?;
        self.closure_mut()?
            .scope_insert(bind.ident.name.clone(), value.clone())?;
        Ok(())
    }

    fn visit_num(&mut self, num: &'ast Num) -> Result<(), Self::Err> {
        self.stack_push(Value::Number(*num));
        Ok(())
    }

    fn visit_str(&mut self, str: &'ast Str) -> Result<(), Self::Err> {
        self.stack_push(Value::String(str.clone()));
        Ok(())
    }

    fn visit_unary_op(&mut self, op: &'ast UnaryOp, expr: &'ast Expr) -> Result<(), Self::Err> {
        self.visit_expr(expr)?;
        let val = self.stack_pop()?;

        let result = match (op, val) {
            (UnaryOp::Neg, Value::Number(n)) => Ok(Value::Number((-n.0).into())),
            (UnaryOp::Not, Value::Number(n)) => {
                Ok(Value::Number(if n.0 == 0.0 { 1.0 } else { 0.0 }.into()))
            }
            _ => Err(Error::NotImplemented(format!(
                "Unary op {:?} for value {:?}",
                op, expr
            ))),
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
        let right_val = self.stack_pop()?;
        let left_val = self.stack_pop()?;

        let result = match (op, left_val, right_val) {
            (BinaryOp::Add, Value::Number(l), Value::Number(r)) => Ok(Value::Number(l + r)),
            (BinaryOp::Sub, Value::Number(l), Value::Number(r)) => Ok(Value::Number(l - r)),
            (BinaryOp::Mul, Value::Number(l), Value::Number(r)) => Ok(Value::Number(l * r)),
            (BinaryOp::Div, Value::Number(l), Value::Number(r)) => {
                if r.0 == 0.0 {
                    return Err(Error::NotImplemented("Division by zero".to_string()));
                }
                Ok(Value::Number(l / r))
            }
            (BinaryOp::Eq, l, r) => Ok(Value::Number(if l == r { 1.0 } else { 0.0 }.into())),
            (BinaryOp::NotEq, l, r) => Ok(Value::Number(if l != r { 1.0 } else { 0.0 }.into())),
            (BinaryOp::Lt, Value::Number(l), Value::Number(r)) => {
                Ok(Value::Number(if l < r { 1.0 } else { 0.0 }.into()))
            }
            (BinaryOp::Gt, Value::Number(l), Value::Number(r)) => {
                Ok(Value::Number(if l > r { 1.0 } else { 0.0 }.into()))
            }
            (BinaryOp::LtEq, Value::Number(l), Value::Number(r)) => {
                Ok(Value::Number(if l <= r { 1.0 } else { 0.0 }.into()))
            }
            (BinaryOp::GtEq, Value::Number(l), Value::Number(r)) => {
                Ok(Value::Number(if l >= r { 1.0 } else { 0.0 }.into()))
            }
            (BinaryOp::Add, Value::String(l), Value::String(r)) => Ok(Value::String(l + r)),
            _ => Err(Error::NotImplemented(format!(
                "Binary op {:?} for values {:?} and {:?}",
                op, lhs, rhs
            ))),
        };

        self.stack_push(result?);
        Ok(())
    }

    fn visit_map(&mut self, bindings: &'ast [Binding]) -> Result<(), Self::Err> {
        let mut map = HashMap::new();
        self.closure_mut()?.scope_push();

        for binding in bindings {
            self.visit_bind(binding)?;
            let value = self.closure()?.scope_get(&binding.ident.name)?;
            map.insert(binding.ident.name.clone(), value.clone());
        }
        self.closure_mut()?.scope_pop()?;
        self.stack_push(Value::Map(map));
        Ok(())
    }

    fn visit_app(&mut self, lhs: &'ast Expr, rhs: &'ast Expr) -> Result<(), Self::Err> {
        self.visit_expr(lhs)?;
        self.visit_expr(rhs)?;
        let arg_val = self.stack_pop()?;
        let func_val = self.stack_pop()?;

        let result = match func_val {
            Value::Lambda {
                params,
                body,
                closure,
            } => {
                self.closure_push(closure);

                self.closure_mut()?.scope_push();

                if params.len() == 1 {
                    self.closure_mut()?
                        .scope_insert(params[0].clone(), arg_val)?;
                } else if params.is_empty() {
                } else if let Value::Map(arg_map) = arg_val {
                    for p in params {
                        if let Some(val) = arg_map.get(&p) {
                            self.closure_mut()?.scope_insert(p.clone(), val.clone())?;
                        } else {
                            return Err(Error::NotImplemented(format!(
                                "Missing argument '{}' for lambda",
                                p
                            )));
                        }
                    }
                } else {
                    return Err(Error::NotImplemented(
                        "Multi-parameter lambda expects a map as argument".to_string(),
                    ));
                }

                //TODO: detect recursion
                self.visit_expr(&body)?;

                self.closure_pop()?;

                // returned value on top of stack
                self.stack_pop()
            }
            _ => Err(Error::NotImplemented(format!(
                "Cannot call value of type {:?}",
                func_val
            ))),
        };

        self.stack_push(result?);
        Ok(())
    }

    fn visit_block_expr(
        &mut self,
        bindings: &'ast [Binding],
        expr: &'ast Expr,
    ) -> Result<(), Self::Err> {
        self.closure_mut()?.scope_push();
        for binding in bindings {
            self.visit_bind(binding)?;
            let value = self.closure()?.scope_get(&binding.ident.name)?.clone();
            self.closure_mut()?
                .scope_insert(binding.ident.name.clone(), value)?;
        }

        self.visit_expr(expr)?;
        let value = self.stack_pop()?;

        self.closure_mut()?.scope_pop()?;

        self.stack_push(value);
        Ok(())
    }

    fn visit_lambda(&mut self, params: &'ast [String], body: &'ast Expr) -> Result<(), Self::Err> {
        let lambda = Value::Lambda {
            params: params.to_vec(),
            body: Box::new(body.clone()),
            // TODO: only clone used values from parent scope
            // this is fairly expensive
            closure: self.closure()?.clone(),
        };
        self.stack_push(lambda);
        Ok(())
    }

    fn visit_list(&mut self, list: &'ast ast::List) -> Result<(), Self::Err> {
        let mut result = vec![];
        for expr in &list.exprs {
            self.visit_expr(expr)?;
            result.push(self.stack_pop()?);
        }
        self.stack_push(Value::List(result));
        Ok(())
    }

    fn visit_map_access(
        &mut self,
        expr: &'ast Expr,
        ident: &'ast ast::Ident,
    ) -> Result<(), Self::Err> {
        self.visit_expr(expr)?;
        let result = match self.stack_pop()? {
            Value::Map(map) => map.get(&ident.name).cloned().ok_or(Error::InvalidMapAccess),
            _ => Err(Error::InvalidMapAccess),
        }?;

        self.stack_push(result);
        Ok(())
    }
}
