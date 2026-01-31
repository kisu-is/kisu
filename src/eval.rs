use crate::ast::{BinaryOp, Binding, Expr, UnaryOp};
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Number(f64),
    String(String),
    Map(HashMap<String, Value>),
    Lambda {
        params: Vec<String>,
        body: Box<Expr>,
        closure: Scope,
    },
    Void,
}

#[derive(thiserror::Error, Debug, PartialEq)]
pub enum Error {
    #[error("feature not implemented")]
    NotImplemented(String),
    #[error("identifier '{0}' not found")]
    IdentifierNotFound(String),
}

#[derive(Debug, PartialEq)]
pub struct Scope {
    vars: HashMap<String, Value>,
    parent: Option<Box<Scope>>,
}

impl Default for Scope {
    fn default() -> Self {
        Self::new()
    }
}

impl Scope {
    pub fn new() -> Self {
        Self {
            vars: HashMap::new(),
            parent: None,
        }
    }

    pub fn new_child(&self) -> Self {
        Self {
            vars: HashMap::new(),
            parent: Some(Box::new(self.clone())),
        }
    }

    pub fn get(&self, name: &str) -> Option<&Value> {
        self.vars
            .get(name)
            .or_else(|| self.parent.as_ref().and_then(|parent| parent.get(name)))
    }

    pub fn set(&mut self, name: String, value: Value) {
        self.vars.insert(name, value);
    }
}

impl Clone for Scope {
    fn clone(&self) -> Self {
        Self {
            vars: self.vars.clone(),
            parent: self.parent.clone(),
        }
    }
}

fn eval_unary(op: &UnaryOp, expr: &Expr, scope: &mut Scope) -> Result<Value, Error> {
    let val = eval(expr, scope)?;
    match (op, val) {
        (UnaryOp::Neg, Value::Number(n)) => Ok(Value::Number(-n)),
        (UnaryOp::Not, Value::Number(n)) => Ok(Value::Number(if n == 0.0 { 1.0 } else { 0.0 })),
        _ => Err(Error::NotImplemented(format!(
            "Unary op {:?} for value {:?}",
            op, expr
        ))),
    }
}

fn eval_binary(
    op: &BinaryOp,
    left: &Expr,
    right: &Expr,
    scope: &mut Scope,
) -> Result<Value, Error> {
    let left_val = eval(left, scope)?;
    let right_val = eval(right, scope)?;
    match (op, left_val, right_val) {
        (BinaryOp::Add, Value::Number(l), Value::Number(r)) => Ok(Value::Number(l + r)),
        (BinaryOp::Sub, Value::Number(l), Value::Number(r)) => Ok(Value::Number(l - r)),
        (BinaryOp::Mul, Value::Number(l), Value::Number(r)) => Ok(Value::Number(l * r)),
        (BinaryOp::Div, Value::Number(l), Value::Number(r)) => {
            if r == 0.0 {
                return Err(Error::NotImplemented("Division by zero".to_string()));
            }
            Ok(Value::Number(l / r))
        }
        (BinaryOp::Eq, l, r) => Ok(Value::Number(if l == r { 1.0 } else { 0.0 })),
        (BinaryOp::NotEq, l, r) => Ok(Value::Number(if l != r { 1.0 } else { 0.0 })),
        (BinaryOp::Lt, Value::Number(l), Value::Number(r)) => {
            Ok(Value::Number(if l < r { 1.0 } else { 0.0 }))
        }
        (BinaryOp::Gt, Value::Number(l), Value::Number(r)) => {
            Ok(Value::Number(if l > r { 1.0 } else { 0.0 }))
        }
        (BinaryOp::LtEq, Value::Number(l), Value::Number(r)) => {
            Ok(Value::Number(if l <= r { 1.0 } else { 0.0 }))
        }
        (BinaryOp::GtEq, Value::Number(l), Value::Number(r)) => {
            Ok(Value::Number(if l >= r { 1.0 } else { 0.0 }))
        }
        _ => Err(Error::NotImplemented(format!(
            "Binary op {:?} for values {:?} and {:?}",
            op, left, right
        ))),
    }
}

fn eval_block(bindings: &[Binding], expr: &Expr, scope: &mut Scope) -> Result<Value, Error> {
    let mut block_scope = scope.new_child();
    for binding in bindings {
        let value = eval(&binding.expr, &mut block_scope)?;
        block_scope.set(binding.name.clone(), value);
    }
    eval(expr, &mut block_scope)
}

fn eval_map(bindings: &[Binding], scope: &mut Scope) -> Result<Value, Error> {
    let mut map = HashMap::new();
    let mut map_scope = scope.new_child();
    for binding in bindings {
        let value = eval(&binding.expr, &mut map_scope)?;
        map_scope.set(binding.name.clone(), value.clone());
        map.insert(binding.name.clone(), value);
    }
    Ok(Value::Map(map))
}

fn eval_app(func: &Expr, arg: &Expr, scope: &mut Scope) -> Result<Value, Error> {
    let func_val = eval(func, scope)?;
    let arg_val = eval(arg, scope)?;

    match func_val {
        Value::Lambda {
            params,
            body,
            closure,
        } => {
            let mut call_scope = closure.new_child();

            if params.len() == 1 {
                call_scope.set(params[0].clone(), arg_val);
            } else if params.is_empty() {
            } else if let Value::Map(arg_map) = arg_val {
                for p in params {
                    if let Some(val) = arg_map.get(&p) {
                        call_scope.set(p.clone(), val.clone());
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

            eval(&body, &mut call_scope)
        }
        _ => Err(Error::NotImplemented(format!(
            "Cannot call value of type {:?}",
            func_val
        ))),
    }
}

pub fn eval(expr: &Expr, scope: &mut Scope) -> Result<Value, Error> {
    match expr {
        Expr::Number(n) => Ok(Value::Number(*n)),
        Expr::String(s) => Ok(Value::String(s.clone())),
        Expr::Ident(name) => scope
            .get(name)
            .cloned()
            .ok_or_else(|| Error::IdentifierNotFound(name.clone())),
        Expr::Unary { op, expr } => eval_unary(op, expr, scope),
        Expr::Binary { op, left, right } => eval_binary(op, left, right, scope),
        Expr::Lambda { params, body } => Ok(Value::Lambda {
            params: params.clone(),
            body: body.clone(),
            closure: scope.clone(),
        }),
        Expr::Paren(expr) => eval(expr, scope),
        Expr::Block { bindings, expr } => eval_block(bindings, expr, scope),
        Expr::Map { bindings } => eval_map(bindings, scope),
        Expr::App { func, arg } => eval_app(func, arg, scope),
    }
}
