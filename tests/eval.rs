use kisu::ast::{BinaryOp, Expr, UnaryOp};
use kisu::eval::{Scope, Value, eval};

#[test]
fn number() {
    let expr = Expr::Number(10.0);
    let mut env = Scope::new();
    assert_eq!(eval(&expr, &mut env), Ok(Value::Number(10.0)));
}

#[test]
fn string() {
    let expr = Expr::String("hello".to_string());
    let mut env = Scope::new();
    assert_eq!(
        eval(&expr, &mut env),
        Ok(Value::String("hello".to_string()))
    );
}

#[test]
fn neg() {
    let expr = Expr::Unary {
        op: UnaryOp::Neg,
        expr: Box::new(Expr::Number(5.0)),
    };
    let mut env = Scope::new();
    assert_eq!(eval(&expr, &mut env), Ok(Value::Number(-5.0)));
}

#[test]
fn add() {
    let expr = Expr::Binary {
        op: BinaryOp::Add,
        left: Box::new(Expr::Number(2.0)),
        right: Box::new(Expr::Number(3.0)),
    };
    let mut env = Scope::new();
    assert_eq!(eval(&expr, &mut env), Ok(Value::Number(5.0)));
}

#[test]
fn sub() {
    let expr = Expr::Binary {
        op: BinaryOp::Sub,
        left: Box::new(Expr::Number(5.0)),
        right: Box::new(Expr::Number(3.0)),
    };
    let mut env = Scope::new();
    assert_eq!(eval(&expr, &mut env), Ok(Value::Number(2.0)));
}

#[test]
fn mul() {
    let expr = Expr::Binary {
        op: BinaryOp::Mul,
        left: Box::new(Expr::Number(2.0)),
        right: Box::new(Expr::Number(3.0)),
    };
    let mut env = Scope::new();
    assert_eq!(eval(&expr, &mut env), Ok(Value::Number(6.0)));
}

#[test]
fn div() {
    let expr = Expr::Binary {
        op: BinaryOp::Div,
        left: Box::new(Expr::Number(6.0)),
        right: Box::new(Expr::Number(3.0)),
    };
    let mut env = Scope::new();
    assert_eq!(eval(&expr, &mut env), Ok(Value::Number(2.0)));
}

#[test]
fn paren() {
    let expr = Expr::Paren(Box::new(Expr::Number(10.0)));
    let mut env = Scope::new();
    assert_eq!(eval(&expr, &mut env), Ok(Value::Number(10.0)));
}

#[test]
fn complex_expr() {
    // (2 + 3) * 4
    let expr = Expr::Binary {
        op: BinaryOp::Mul,
        left: Box::new(Expr::Paren(Box::new(Expr::Binary {
            op: BinaryOp::Add,
            left: Box::new(Expr::Number(2.0)),
            right: Box::new(Expr::Number(3.0)),
        }))),
        right: Box::new(Expr::Number(4.0)),
    };
    let mut env = Scope::new();
    assert_eq!(eval(&expr, &mut env), Ok(Value::Number(20.0)));
}
