use crate::ast::typed;
use crate::ast::typed::Visitor;
use crate::types::{Type, TypeId, TypeKind, Types};
use bumpalo::Bump;
use rpds::HashTrieMap;
use std::cell::OnceCell;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

pub struct NativeFn {
    pub name: String,
    pub fun: Box<dyn Fn(Value) -> Value + 'static>,
    pub arg_ty: Type,
    pub ret_ty: Type,
}

impl std::fmt::Debug for NativeFn {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NativeFn")
            .field("name", &self.name)
            .field("arg_ty", &self.arg_ty)
            .field("ret_ty", &self.ret_ty)
            .finish()
    }
}

impl PartialEq for NativeFn {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.arg_ty == other.arg_ty && self.ret_ty == other.ret_ty
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Number(f64),
    String(Rc<String>),
    Bool(bool),
    Struct(Rc<String>, Rc<HashMap<String, Value>>),
    List(Rc<Vec<Value>>),
    Lambda,
    Unit,
    NativeFn(Rc<NativeFn>),
}

#[derive(Debug, Clone)]
pub struct Thunk<'ast> {
    expr: &'ast typed::Expr<'ast>,
    scope: Scope<'ast>,
    value: OnceCell<Object<'ast>>,
}

impl<'ast> Thunk<'ast> {
    pub fn new(expr: &'ast typed::Expr<'ast>, scope: Scope<'ast>) -> Self {
        Self {
            expr,
            scope,
            value: OnceCell::new(),
        }
    }

    unsafe fn force(self: &Rc<Self>, walker: &mut TreeWalker<'_, 'ast>) -> Object<'ast> {
        unsafe {
            self.value
                .get_or_init(|| {
                    let call_stack =
                        std::mem::replace(&mut walker.call_stack, vec![self.scope.clone()]);
                    walker.visit_expr(self.expr);
                    let result = walker.stack_pop();
                    walker.call_stack = call_stack;
                    result
                })
                .clone()
        }
    }
}

#[derive(Debug, Clone)]
pub enum Object<'ast> {
    Number(f64),
    String(Rc<String>),
    Bool(bool),
    Struct(&'ast str, Rc<HashMap<&'ast str, Object<'ast>>>),
    List(Rc<Vec<Object<'ast>>>),
    Lambda {
        params: &'ast [typed::Param<'ast>],
        body: &'ast typed::Expr<'ast>,
        scope: Scope<'ast>,
    },
    Thunk(Rc<Thunk<'ast>>),
    Unit,
    RecThunk(Rc<RefCell<Option<Rc<Thunk<'ast>>>>>),
    NativeFn(Rc<NativeFn>),
}

#[derive(Debug, Clone, Default)]
pub struct Scope<'ast> {
    vars: HashTrieMap<&'ast str, Object<'ast>>,
}

impl<'ast> Scope<'ast> {
    #[inline]
    pub fn get(&self, name: &str) -> &Object<'ast> {
        self.vars.get(name).unwrap()
    }

    #[inline]
    pub fn insert(&self, key: &'ast str, value: Object<'ast>) -> Self {
        Self {
            vars: self.vars.insert(key, value),
        }
    }
}

pub struct TreeWalker<'t, 'ast> {
    types: &'t Types<'ast>,
    bump: &'ast Bump,
    call_stack: Vec<Scope<'ast>>,
    stack: Vec<Object<'ast>>,
}

impl<'t, 'ast> TreeWalker<'t, 'ast> {
    pub fn new(types: &'t Types<'ast>, bump: &'ast Bump) -> Self {
        Self {
            types,
            bump,
            call_stack: vec![Scope::default()],
            stack: Default::default(),
        }
    }

    pub fn with_bindings(
        types: &'t Types<'ast>,
        bump: &'ast Bump,
        bindings: HashMap<String, Value>,
    ) -> Self {
        let mut walker = Self::new(types, bump);
        let mut scope = Scope::default();
        for (name, value) in bindings {
            scope = scope.insert(bump.alloc_str(&name), walker.object_of(&value));
        }
        walker.call_stack = vec![scope];
        walker
    }
}

#[allow(clippy::missing_safety_doc)]
impl<'ast> TreeWalker<'_, 'ast> {
    pub unsafe fn consume(mut self) -> Value {
        unsafe {
            let object = self.stack_pop();
            self.value_of(object)
        }
    }

    unsafe fn value_of(&mut self, object: Object<'ast>) -> Value {
        unsafe {
            match self.force(object) {
                Object::Number(n) => Value::Number(n),
                Object::String(s) => Value::String(s),
                Object::Bool(b) => Value::Bool(b),
                Object::Struct(name, fields) => {
                    let mut map = HashMap::with_capacity(fields.len());
                    for (key, field) in fields.iter() {
                        map.insert(key.to_string(), self.value_of(field.clone()));
                    }
                    Value::Struct(Rc::new(name.to_string()), Rc::new(map))
                }
                Object::List(objects) => {
                    let mut list = Vec::with_capacity(objects.len());
                    for object in objects.iter() {
                        list.push(self.value_of(object.clone()));
                    }
                    Value::List(Rc::new(list))
                }
                Object::Lambda { .. } => Value::Lambda,
                Object::Unit => Value::Unit,
                Object::NativeFn(native_fn) => Value::NativeFn(native_fn),
                Object::Thunk(_) | Object::RecThunk(_) => unreachable!(),
            }
        }
    }

    fn object_of(&self, value: &Value) -> Object<'ast> {
        match value {
            Value::Number(n) => Object::Number(*n),
            Value::String(s) => Object::String(s.clone()),
            Value::Bool(b) => Object::Bool(*b),
            Value::Struct(name, fields) => {
                let mut map = HashMap::with_capacity(fields.len());
                for (key, field) in fields.iter() {
                    map.insert(&*self.bump.alloc_str(key), self.object_of(field));
                }
                Object::Struct(self.bump.alloc_str(name), Rc::new(map))
            }
            Value::List(values) => {
                Object::List(Rc::new(values.iter().map(|v| self.object_of(v)).collect()))
            }
            Value::Lambda => unreachable!(),
            Value::Unit => Object::Unit,
            Value::NativeFn(native_fn) => Object::NativeFn(native_fn.clone()),
        }
    }

    #[inline]
    unsafe fn force(&mut self, object: Object<'ast>) -> Object<'ast> {
        unsafe {
            match object {
                Object::Thunk(thunk) => thunk.force(self),
                Object::RecThunk(thunk) => {
                    if let Some(thunk) = thunk.borrow().as_ref() {
                        thunk.force(self)
                    } else {
                        unreachable!()
                    }
                }
                _ => object,
            }
        }
    }

    #[inline]
    fn scope(&self) -> &Scope<'ast> {
        self.call_stack.last().unwrap()
    }

    #[inline]
    fn scope_replace(&mut self, scope: Scope<'ast>) {
        *self.call_stack.last_mut().unwrap() = scope;
    }

    #[inline]
    fn scope_push(&mut self, scope: Scope<'ast>) {
        self.call_stack.push(scope)
    }

    #[inline]
    fn scope_pop(&mut self) -> Scope<'ast> {
        self.call_stack.pop().unwrap()
    }

    #[inline]
    fn stack_push(&mut self, object: Object<'ast>) {
        self.stack.push(object)
    }

    #[inline]
    fn stack_pop(&mut self) -> Object<'ast> {
        self.stack.pop().unwrap()
    }
}

impl<'ast> typed::Visitor<'ast> for TreeWalker<'_, 'ast> {
    unsafe fn visit_program(&mut self, program: &typed::Program<'ast>) {
        unsafe { self.visit_expr(program.expr) }
    }

    unsafe fn visit_ident(&mut self, ident: &'ast typed::Ident<'ast>) {
        unsafe {
            let val = self.scope().get(ident.name).clone();
            let forced_val = self.force(val);
            self.stack_push(forced_val);
        }
    }

    unsafe fn visit_bind(&mut self, bind: &'ast typed::Binding<'ast>) {
        let scope = self.scope().clone();

        if bind.kind == typed::BindingKind::Rec {
            let slot = Rc::new(RefCell::new(None));
            let rec_name = bind.ident.name;
            let rec_scope = scope.insert(rec_name, Object::RecThunk(slot.clone()));

            let thunk = Rc::new(Thunk::new(bind.expr, rec_scope));
            *slot.borrow_mut() = Some(thunk.clone());

            self.scope_replace(scope.insert(rec_name, Object::Thunk(thunk)));
        } else {
            let thunk = Rc::new(Thunk::new(bind.expr, scope.clone()));
            let new_scope = scope.insert(bind.ident.name, Object::Thunk(thunk));
            self.scope_replace(new_scope);
        }
    }

    unsafe fn visit_num(&mut self, num: &'ast typed::Num) {
        self.stack_push(Object::Number(num.0));
    }

    unsafe fn visit_str(&mut self, str: &'ast typed::Str<'ast>) {
        self.stack_push(Object::String(Rc::new(str.0.to_string())));
    }

    unsafe fn visit_bool(&mut self, b: bool) {
        self.stack_push(Object::Bool(b));
    }

    unsafe fn visit_unary_op(&mut self, op: &'ast typed::UnaryOp, expr: &'ast typed::Expr<'ast>) {
        unsafe {
            self.visit_expr(expr);
            let val = self.stack_pop();
            let forced_val = self.force(val);

            let result = match op {
                typed::UnaryOp::Neg => match forced_val {
                    Object::Number(n) => Object::Number(-n),
                    _ => unreachable!(),
                },
                typed::UnaryOp::Not => match forced_val {
                    Object::Number(n) => Object::Bool(n == 0.0),
                    Object::Bool(b) => Object::Bool(!b),
                    _ => unreachable!(),
                },
            };

            self.stack_push(result);
        }
    }

    unsafe fn visit_binary_op(
        &mut self,
        op: &'ast typed::BinaryOp,
        lhs: &'ast typed::Expr<'ast>,
        rhs: &'ast typed::Expr<'ast>,
        ty: &'ast TypeId,
    ) {
        unsafe {
            self.visit_expr(lhs);
            self.visit_expr(rhs);
            let rhs_val = self.stack_pop();
            let rhs_forced = self.force(rhs_val);
            let lhs_val = self.stack_pop();
            let lhs_forced = self.force(lhs_val);

            match self.types.kind(*ty) {
                TypeKind::Number => {
                    let l = if let Object::Number(n) = lhs_forced {
                        n
                    } else {
                        std::hint::unreachable_unchecked()
                    };
                    let r = if let Object::Number(n) = rhs_forced {
                        n
                    } else {
                        std::hint::unreachable_unchecked()
                    };

                    let result = match op {
                        typed::BinaryOp::Add => Object::Number(l + r),
                        typed::BinaryOp::Sub => Object::Number(l - r),
                        typed::BinaryOp::Mul => Object::Number(l * r),
                        typed::BinaryOp::Div => Object::Number(l / r),
                        typed::BinaryOp::Eq => Object::Bool(l == r),
                        typed::BinaryOp::NotEq => Object::Bool(l != r),
                        typed::BinaryOp::Lt => Object::Bool(l < r),
                        typed::BinaryOp::Gt => Object::Bool(l > r),
                        typed::BinaryOp::LtEq => Object::Bool(l <= r),
                        _ => std::hint::unreachable_unchecked(),
                    };
                    self.stack_push(result);
                }
                TypeKind::String => {
                    let l = if let Object::String(s) = lhs_forced {
                        s
                    } else {
                        std::hint::unreachable_unchecked()
                    };
                    let r = if let Object::String(s) = rhs_forced {
                        s
                    } else {
                        std::hint::unreachable_unchecked()
                    };

                    let result = match op {
                        typed::BinaryOp::Add => Object::String(Rc::new(l.to_string() + &r)),
                        typed::BinaryOp::Eq => Object::Bool(l == r),
                        typed::BinaryOp::NotEq => Object::Bool(l != r),
                        _ => std::hint::unreachable_unchecked(),
                    };
                    self.stack_push(result);
                }
                TypeKind::Bool => {
                    let l = if let Object::Bool(b) = lhs_forced {
                        b
                    } else {
                        std::hint::unreachable_unchecked()
                    };
                    let r = if let Object::Bool(b) = rhs_forced {
                        b
                    } else {
                        std::hint::unreachable_unchecked()
                    };

                    let result = match op {
                        typed::BinaryOp::Eq => Object::Bool(l == r),
                        typed::BinaryOp::NotEq => Object::Bool(l != r),
                        _ => std::hint::unreachable_unchecked(),
                    };
                    self.stack_push(result);
                }
                _ => std::hint::unreachable_unchecked(),
            }
        }
    }

    unsafe fn visit_struct_expr(
        &mut self,
        fields: &'ast [typed::Binding<'ast>],
        name: &'ast typed::TypeIdent<'ast>,
    ) {
        unsafe {
            self.scope_push(self.scope().clone());

            for bind in fields {
                self.visit_bind(bind);
            }

            let final_scope = self.scope().clone();
            let mut fields_map = HashMap::with_capacity(fields.len());
            for bind in fields {
                let val = final_scope.get(bind.ident.name).clone();
                let forced_val = self.force(val);
                fields_map.insert(bind.ident.name, forced_val);
            }

            self.scope_pop();
            self.stack_push(Object::Struct(name.name, Rc::new(fields_map)));
        }
    }

    unsafe fn visit_app(&mut self, lhs: &'ast typed::Expr<'ast>, rhs: &'ast typed::Expr<'ast>) {
        unsafe {
            self.visit_expr(lhs);
            let val = self.stack_pop();
            let forced_val = self.force(val);
            let scope = self.scope().clone();
            let arg_val = Object::Thunk(Rc::new(Thunk::new(rhs, scope)));

            let result_val = match forced_val {
                Object::Lambda {
                    params,
                    body,
                    scope,
                } => {
                    let Some((param, rest)) = params.split_first() else {
                        unreachable!()
                    };
                    let new_scope = scope.insert(param.ident.name, arg_val);

                    if !rest.is_empty() {
                        Object::Lambda {
                            params: rest,
                            body,
                            scope: new_scope,
                        }
                    } else {
                        self.scope_push(new_scope);
                        self.visit_expr(body);
                        let final_result = self.stack_pop();
                        self.scope_pop();
                        final_result
                    }
                }
                Object::NativeFn(native_fn) => {
                    let arg = self.value_of(arg_val);
                    let result = (native_fn.fun)(arg);
                    self.object_of(&result)
                }
                _ => {
                    unreachable!();
                }
            };

            self.stack_push(result_val);
        }
    }

    unsafe fn visit_block_expr(
        &mut self,
        bindings: &'ast [typed::Binding<'ast>],
        expr: &'ast typed::Expr<'ast>,
    ) {
        unsafe {
            self.scope_push(self.scope().clone());

            for binding in bindings {
                self.visit_bind(binding);
            }

            self.visit_expr(expr);
            let value = self.stack_pop();

            self.scope_pop();

            self.stack_push(value);
        }
    }

    unsafe fn visit_lambda(
        &mut self,
        params: &'ast [typed::Param<'ast>],
        body: &'ast typed::Expr<'ast>,
    ) {
        let lambda = Object::Lambda {
            params,
            body,
            scope: self.scope().clone(),
        };
        self.stack_push(lambda);
    }

    unsafe fn visit_list(&mut self, list: &'ast typed::List<'ast>) {
        let scope = self.scope().clone();
        let result = list
            .exprs
            .iter()
            .map(|expr| Object::Thunk(Rc::new(Thunk::new(expr, scope.clone()))))
            .collect();
        self.stack_push(Object::List(Rc::new(result)));
    }

    unsafe fn visit_struct_access(
        &mut self,
        expr: &'ast typed::Expr<'ast>,
        ident: &'ast typed::Ident<'ast>,
    ) {
        unsafe {
            self.visit_expr(expr);
            let val = self.stack_pop();
            let forced_val = self.force(val);
            let result = match forced_val {
                Object::Struct(_, map) => map.get(ident.name).cloned(),
                _ => {
                    unreachable!()
                }
            };

            self.stack_push(result.unwrap());
        }
    }

    unsafe fn visit_if_expr(
        &mut self,
        cond: &'ast typed::Expr<'ast>,
        then_expr: &'ast typed::Expr<'ast>,
        else_expr: &'ast typed::Expr<'ast>,
    ) {
        unsafe {
            self.visit_expr(cond);
            let cond_val = self.stack_pop();
            let forced_cond = self.force(cond_val);

            let is_truthy = match forced_cond {
                Object::Bool(b) => b,
                _ => unreachable!(),
            };

            if is_truthy {
                self.visit_expr(then_expr);
            } else {
                self.visit_expr(else_expr);
            }
        }
    }

    unsafe fn visit_struct_def(&mut self, _struct_def: &'ast typed::StructDef<'ast>) {}
}
