use crate::ast::typed;
use crate::ast::typed::Visitor;
use crate::types::Type;
use rpds::HashTrieMap;
use std::cell::OnceCell;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

#[derive(Debug, Clone)]
pub struct Thunk {
    expr: Box<typed::Expr>,
    scope: Scope,
    value: OnceCell<Value>,
}

impl Thunk {
    pub fn new(expr: Box<typed::Expr>, scope: Scope) -> Self {
        Self {
            expr,
            scope,
            value: OnceCell::new(),
        }
    }

    pub fn force(self: &Rc<Self>, walker: &mut TreeWalker) -> Value {
        self.value
            .get_or_init(|| {
                let call_stack =
                    std::mem::replace(&mut walker.call_stack, vec![self.scope.clone()]);
                walker.visit_expr(&self.expr);
                let result = walker.stack_pop();
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
        body: Rc<typed::Expr>,
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

#[derive(Debug, PartialEq, Clone, Default)]
pub struct Scope {
    vars: HashTrieMap<String, Value>,
}

impl Scope {
    #[inline]
    pub fn get(&self, name: &str) -> &Value {
        self.vars.get(name).unwrap()
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
    pub fn consume(mut self) -> Value {
        let value = self.stack_pop();
        self.force_consume(value)
    }

    fn force_consume(&mut self, value: Value) -> Value {
        let value = self.force(value);

        match value {
            Value::List(values) => {
                let mut list = Vec::with_capacity(values.len());
                for val in values.iter() {
                    list.push(self.force_consume(val.clone()));
                }
                Value::List(Rc::new(list))
            }
            Value::Struct(name, value) => {
                let mut map = HashMap::with_capacity(value.len());
                for (key, val) in value.iter() {
                    map.insert(key.clone(), self.force_consume(val.clone()));
                }
                Value::Struct(name, Rc::new(map))
            }
            _ => value,
        }
    }

    #[inline]
    fn force(&mut self, value: Value) -> Value {
        match value {
            Value::Thunk(thunk) => thunk.force(self),
            Value::RecThunk(thunk) => {
                if let Some(thunk) = thunk.borrow().as_ref() {
                    thunk.force(self)
                } else {
                    unreachable!()
                }
            }
            _ => value,
        }
    }

    #[inline]
    fn scope(&self) -> &Scope {
        self.call_stack.last().unwrap()
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
    fn scope_pop(&mut self) -> Scope {
        self.call_stack.pop().unwrap()
    }

    #[inline]
    fn stack_push(&mut self, value: Value) {
        self.stack.push(value)
    }

    #[inline]
    fn stack_pop(&mut self) -> Value {
        self.stack.pop().unwrap()
    }
}

impl<'ast> typed::Visitor<'ast> for TreeWalker {
    fn visit_program(&mut self, program: &'ast typed::Program) {
        self.visit_expr(&program.expr)
    }

    fn visit_ident(&mut self, ident: &'ast typed::Ident) {
        let val = self.scope().get(&ident.name).clone();
        let forced_val = self.force(val);
        self.stack_push(forced_val);
    }

    fn visit_bind(&mut self, bind: &'ast typed::Binding) {
        let scope = self.scope().clone();

        if bind.kind == typed::BindingKind::Rec {
            let slot = Rc::new(RefCell::new(None));
            let rec_name = bind.ident.name.clone();
            let rec_scope = scope.insert(rec_name.clone(), Value::RecThunk(slot.clone()));

            let thunk = Rc::new(Thunk::new(bind.expr.clone(), rec_scope));
            *slot.borrow_mut() = Some(thunk.clone());

            self.scope_replace(scope.insert(rec_name, Value::Thunk(thunk)));
        } else {
            let thunk = Rc::new(Thunk::new(bind.expr.clone(), scope.clone()));
            let new_scope = scope.insert(bind.ident.name.clone(), Value::Thunk(thunk));
            self.scope_replace(new_scope);
        }
    }

    fn visit_num(&mut self, num: &'ast typed::Num) {
        self.stack_push(Value::Number(num.0));
    }

    fn visit_str(&mut self, str: &'ast typed::Str) {
        self.stack_push(Value::String(Rc::new(str.0.clone())));
    }

    fn visit_bool(&mut self, b: bool) {
        self.stack_push(Value::Bool(b));
    }

    fn visit_unary_op(&mut self, op: &'ast typed::UnaryOp, expr: &'ast typed::Expr) {
        self.visit_expr(expr);
        let val = self.stack_pop();
        let forced_val = self.force(val);

        let result = match op {
            typed::UnaryOp::Neg => match forced_val {
                Value::Number(n) => Value::Number(-n),
                _ => unreachable!(),
            },
            typed::UnaryOp::Not => match forced_val {
                Value::Number(n) => Value::Bool(n == 0.0),
                Value::Bool(b) => Value::Bool(!b),
                _ => unreachable!(),
            },
        };

        self.stack_push(result);
    }

    fn visit_binary_op(
        &mut self,
        op: &'ast typed::BinaryOp,
        lhs: &'ast typed::Expr,
        rhs: &'ast typed::Expr,
    ) {
        self.visit_expr(lhs);
        self.visit_expr(rhs);
        let rhs_val = self.stack_pop();
        let rhs_forced = self.force(rhs_val);
        let lhs_val = self.stack_pop();
        let lhs_forced = self.force(lhs_val);

        let result = match op {
            typed::BinaryOp::Add => match (lhs_forced, rhs_forced) {
                (Value::Number(l), Value::Number(r)) => Value::Number(l + r),
                (Value::String(l), Value::String(r)) => Value::String(Rc::new(l.to_string() + &r)),
                _ => unreachable!(),
            },
            typed::BinaryOp::Sub => match (lhs_forced, rhs_forced) {
                (Value::Number(l), Value::Number(r)) => Value::Number(l - r),
                _ => unreachable!(),
            },
            typed::BinaryOp::Mul => match (lhs_forced, rhs_forced) {
                (Value::Number(l), Value::Number(r)) => Value::Number(l * r),
                _ => unreachable!(),
            },
            typed::BinaryOp::Div => match (lhs_forced, rhs_forced) {
                (Value::Number(l), Value::Number(r)) => Value::Number(l / r),
                _ => unreachable!(),
            },
            typed::BinaryOp::Eq => Value::Bool(lhs_forced == rhs_forced),
            typed::BinaryOp::NotEq => Value::Bool(lhs_forced != rhs_forced),
            typed::BinaryOp::Lt => match (lhs_forced, rhs_forced) {
                (Value::Number(l), Value::Number(r)) => Value::Bool(l < r),
                _ => unreachable!(),
            },
            typed::BinaryOp::Gt => match (lhs_forced, rhs_forced) {
                (Value::Number(l), Value::Number(r)) => Value::Bool(l > r),
                _ => unreachable!(),
            },
            typed::BinaryOp::LtEq => match (lhs_forced, rhs_forced) {
                (Value::Number(l), Value::Number(r)) => Value::Bool(l <= r),
                _ => unreachable!(),
            },
            typed::BinaryOp::GtEq => match (lhs_forced, rhs_forced) {
                (Value::Number(l), Value::Number(r)) => Value::Bool(l >= r),
                _ => unreachable!(),
            },
            typed::BinaryOp::Dot => {
                unreachable!();
            }
        };

        self.stack_push(result);
    }

    fn visit_struct_expr(&mut self, fields: &'ast [typed::Binding], struct_type: &'ast Type) {
        self.scope_push(self.scope().clone());

        for bind in fields {
            self.visit_bind(bind);
        }

        let final_scope = self.scope().clone();
        let mut fields_map = HashMap::new();
        for bind in fields {
            let val = final_scope.get(&bind.ident.name).clone();
            let forced_val = self.force(val);
            fields_map.insert(bind.ident.name.clone(), forced_val);
        }

        self.scope_pop();
        self.stack_push(Value::Struct(
            Rc::new(struct_type.to_string()),
            Rc::new(fields_map),
        ));
    }

    fn visit_app(&mut self, lhs: &'ast typed::Expr, rhs: &'ast typed::Expr) {
        self.visit_expr(lhs);
        let val = self.stack_pop();
        let forced_val = self.force(val);
        let scope = self.scope().clone();
        let arg_thunk = Rc::new(Thunk::new(Box::new(rhs.clone()), scope));
        let arg_val = Value::Thunk(arg_thunk);

        let result_val = match forced_val {
            Value::Lambda {
                params,
                body,
                scope,
            } => {
                let mut params_clone = (*params).clone();
                let param_name = params_clone.remove(0);

                let new_scope = scope.insert(param_name, arg_val);
                self.scope_push(new_scope);

                if !params_clone.is_empty() {
                    let new_lambda_scope = self.scope().clone();
                    let new_lambda = Value::Lambda {
                        params: Rc::new(params_clone),
                        body,
                        scope: new_lambda_scope,
                    };
                    self.scope_pop();
                    new_lambda
                } else {
                    self.visit_expr(&body);
                    let final_result = self.stack_pop();
                    self.scope_pop();
                    final_result
                }
            }
            _ => {
                unreachable!();
            }
        };

        self.stack_push(result_val);
    }

    fn visit_block_expr(&mut self, bindings: &'ast [typed::Binding], expr: &'ast typed::Expr) {
        self.scope_push(self.scope().clone());

        for binding in bindings {
            self.visit_bind(binding);
        }

        self.visit_expr(expr);
        let value = self.stack_pop();

        self.scope_pop();

        self.stack_push(value);
    }

    fn visit_lambda(&mut self, params: &'ast [typed::Param], body: &'ast typed::Expr) {
        let scope = self.scope().clone();
        let names = params.iter().map(|p| p.ident.name.clone()).collect();

        let lambda = Value::Lambda {
            params: Rc::new(names),
            body: Rc::new(body.clone()),
            scope,
        };
        self.stack_push(lambda);
    }

    fn visit_list(&mut self, list: &'ast typed::List) {
        let mut result = vec![];
        let scope = self.scope().clone();
        for expr in &list.exprs {
            let thunk = Rc::new(Thunk::new(Box::new(expr.clone()), scope.clone()));
            result.push(Value::Thunk(thunk));
        }
        self.stack_push(Value::List(Rc::new(result)));
    }

    fn visit_struct_access(&mut self, expr: &'ast typed::Expr, ident: &'ast typed::Ident) {
        self.visit_expr(expr);
        let val = self.stack_pop();
        let forced_val = self.force(val);
        let result = match forced_val {
            Value::Struct(_, map) => map.get(&ident.name).cloned(),
            _ => {
                unreachable!()
            }
        };

        self.stack_push(result.unwrap());
    }

    fn visit_if_expr(
        &mut self,
        cond: &'ast typed::Expr,
        then_expr: &'ast typed::Expr,
        else_expr: &'ast typed::Expr,
    ) {
        self.visit_expr(cond);
        let cond_val = self.stack_pop();
        let forced_cond = self.force(cond_val);

        let is_truthy = match forced_cond {
            Value::Bool(b) => b,
            _ => unreachable!(),
        };

        if is_truthy {
            self.visit_expr(then_expr);
        } else {
            self.visit_expr(else_expr);
        }
    }

    fn visit_struct_def(&mut self, _struct_def: &'ast typed::StructDef) {}
}
