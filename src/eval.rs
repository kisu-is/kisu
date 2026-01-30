use crate::ast::{BinaryOp, Expr, UnaryOp};
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Number(f64),
    String(String),
    Map(HashMap<String, Value>),
    Void,
}

#[derive(thiserror::Error, Debug, PartialEq)]
pub enum Error {
    #[error("feature not implemented")]
    NotImplemented(String),
    #[error("identifier '{0}' not found")]
    IdentifierNotFound(String),
}

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

pub fn eval(expr: &Expr, scope: &mut Scope) -> Result<Value, Error> {
    match expr {
        Expr::Number(n) => Ok(Value::Number(*n)),
        Expr::String(s) => Ok(Value::String(s.clone())),
        Expr::Ident(name) => scope
            .get(name)
            .cloned()
            .ok_or_else(|| Error::IdentifierNotFound(name.clone())),
        Expr::Unary { op, expr } => {
            let val = eval(expr, scope)?;
            match (op, val) {
                (UnaryOp::Neg, Value::Number(n)) => Ok(Value::Number(-n)),
                _ => Err(Error::NotImplemented(format!(
                    "Unary op {:?} for value {:?}",
                    op, expr
                ))),
            }
        }
        Expr::Binary { op, left, right } => {
            let left_val = eval(left, scope)?;
            let right_val = eval(right, scope)?;
            match (op, left_val, right_val) {
                (BinaryOp::Add, Value::Number(l), Value::Number(r)) => Ok(Value::Number(l + r)),
                (BinaryOp::Sub, Value::Number(l), Value::Number(r)) => Ok(Value::Number(l - r)),
                (BinaryOp::Mul, Value::Number(l), Value::Number(r)) => Ok(Value::Number(l * r)),
                (BinaryOp::Div, Value::Number(l), Value::Number(r)) => Ok(Value::Number(l / r)),
                _ => Err(Error::NotImplemented(format!(
                    "Binary op {:?} for values {:?} and {:?}",
                    op, left, right
                ))),
            }
        }
        Expr::Lambda { .. } => Err(Error::NotImplemented("lambda".to_string())),
        Expr::Paren(expr) => eval(expr, scope),
        Expr::Block { bindings, expr } => {
            let mut block_scope = scope.new_child();
            for binding in bindings {
                let value = eval(&binding.expr, &mut block_scope)?;
                block_scope.set(binding.name.clone(), value);
            }
            eval(expr, &mut block_scope)
        }
        Expr::Map { bindings } => {
            let mut map = HashMap::new();
            let mut map_scope = scope.new_child();
            for binding in bindings {
                let value = eval(&binding.expr, &mut map_scope)?;
                map_scope.set(binding.name.clone(), value.clone());
                map.insert(binding.name.clone(), value);
            }
            Ok(Value::Map(map))
        }
    }
}
