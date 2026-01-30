use kisu::{
    ast::{BinaryOp, Expr, UnaryOp},
    lexer::TokenIter,
    parser::Parser,
};
use logos::Lexer;

#[test]
fn number() {
    let source = "42";
    let lexer = Lexer::new(source);
    let mut parser = Parser::new(TokenIter::from(lexer), source);

    let result = parser.parse_program();
    assert!(result.is_ok());

    let expr = result.unwrap();
    assert!(matches!(expr, Expr::Number(42.0)));
}

#[test]
fn string() {
    let source = "\"hello\"";
    let lexer = Lexer::new(source);
    let mut parser = Parser::new(TokenIter::from(lexer), source);

    let result = parser.parse_program();
    assert!(result.is_ok());

    let expr = result.unwrap();
    assert!(matches!(expr, Expr::String(s) if s == "hello"));
}

#[test]
fn ident() {
    let source = "x";
    let lexer = Lexer::new(source);
    let mut parser = Parser::new(TokenIter::from(lexer), source);

    let result = parser.parse_program();
    assert!(result.is_ok());

    let expr = result.unwrap();
    assert!(matches!(expr, Expr::Ident(name) if name == "x"));
}

#[test]
fn paren_expr() {
    let source = "(42)";
    let lexer = Lexer::new(source);
    let mut parser = Parser::new(TokenIter::from(lexer), source);

    let result = parser.parse_program();
    assert!(result.is_ok());

    let expr = result.unwrap();
    if let Expr::Paren(inner) = expr {
        assert!(matches!(*inner, Expr::Number(42.0)));
    } else {
        panic!("Expected parenthesized expression");
    }
}

#[test]
fn error() {
    let source = "@";
    let lexer = Lexer::new(source);
    let mut parser = Parser::new(TokenIter::from(lexer), source);

    let result = parser.parse_program();
    assert!(result.is_err());
}

#[test]
fn binary() {
    let source = "1 + 2";
    let lexer = Lexer::new(source);
    let mut parser = Parser::new(TokenIter::from(lexer), source);

    let result = parser.parse_program();
    assert!(result.is_ok());

    let expr = result.unwrap();
    if let Expr::Binary { op, left, right } = expr {
        assert_eq!(op, BinaryOp::Add);
        assert!(matches!(*left, Expr::Number(1.0)));
        assert!(matches!(*right, Expr::Number(2.0)));
    } else {
        panic!("Expected binary expression");
    }
}

#[test]
fn precedence() {
    let source = "1 + 2 * 3";
    let lexer = Lexer::new(source);
    let mut parser = Parser::new(TokenIter::from(lexer), source);

    let result = parser.parse_program();
    assert!(result.is_ok());

    let expr = result.unwrap();
    if let Expr::Binary { op, left, right } = expr {
        assert_eq!(op, BinaryOp::Add);
        assert!(matches!(*left, Expr::Number(1.0)));

        if let Expr::Binary {
            op: right_op,
            left: right_left,
            right: right_right,
        } = *right
        {
            assert_eq!(right_op, BinaryOp::Mul);
            assert!(matches!(*right_left, Expr::Number(2.0)));
            assert!(matches!(*right_right, Expr::Number(3.0)));
        } else {
            panic!("Expected nested binary expression for right side");
        }
    } else {
        panic!("Expected binary expression");
    }
}

#[test]
fn unary() {
    let source = "-42";
    let lexer = Lexer::new(source);
    let mut parser = Parser::new(TokenIter::from(lexer), source);

    let result = parser.parse_program();
    assert!(result.is_ok());

    let expr = result.unwrap();
    if let Expr::Unary { op, expr: inner } = expr {
        assert_eq!(op, UnaryOp::Neg);
        assert!(matches!(*inner, Expr::Number(42.0)));
    } else {
        panic!("Expected unary expression");
    }
}

#[test]
fn complex_expr() {
    let source = "-1 + 2 * 3";
    let lexer = Lexer::new(source);
    let mut parser = Parser::new(TokenIter::from(lexer), source);

    let result = parser.parse_program();
    assert!(result.is_ok());

    let expr = result.unwrap();
    if let Expr::Binary { op, left, right } = expr {
        assert_eq!(op, BinaryOp::Add);

        if let Expr::Unary {
            op: left_op,
            expr: left_inner,
        } = *left
        {
            assert_eq!(left_op, UnaryOp::Neg);
            assert!(matches!(*left_inner, Expr::Number(1.0)));
        } else {
            panic!("Expected unary expression for left side");
        }

        if let Expr::Binary {
            op: right_op,
            left: right_left,
            right: right_right,
        } = *right
        {
            assert_eq!(right_op, BinaryOp::Mul);
            assert!(matches!(*right_left, Expr::Number(2.0)));
            assert!(matches!(*right_right, Expr::Number(3.0)));
        } else {
            panic!("Expected binary expression for right side");
        }
    } else {
        panic!("Expected binary expression");
    }
}
