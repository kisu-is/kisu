use mauve::{run, target::eval::Value};
use std::collections::HashMap;
use std::rc::Rc;

macro_rules! assert_eval {
    ($src:literal, $eq:expr) => {{
        let src = indoc::indoc! {$src};
        match run(src) {
            Err(e) => panic!("{:?}", e),
            Ok(v) => assert_eq!(v, $eq),
        }
    }};
}

#[test]
fn add() {
    assert_eval!("1 + 2", Value::Number(3.0));
}

#[test]
fn sub() {
    assert_eval!("5 - 2", Value::Number(3.0));
}

#[test]
fn mul() {
    assert_eval!("3 * 4", Value::Number(12.0));
}

#[test]
fn div() {
    assert_eval!("10 / 2", Value::Number(5.0));
}

#[test]
fn precedence() {
    assert_eval!("1 + 2 * 3", Value::Number(7.0));
}

#[test]
fn unary() {
    assert_eval!("-10", Value::Number(-10.0));
}

#[test]
fn complex() {
    assert_eval!("-1 + 2 * 3", Value::Number(5.0));
}

#[test]
fn group() {
    assert_eval!("(1 + 2) * 3", Value::Number(9.0));
}

#[test]
fn string() {
    assert_eval!(r#""hello""#, Value::String(Rc::new("hello".to_string())));
}

#[test]
fn group_with_binding() {
    assert_eval!(
        "
        (
            let a = 10;
            a * 2
        )",
        Value::Number(20.0)
    );
}

#[test]
fn group_top_level() {
    assert_eval!(
        "
            let a = 5;
            a * 2
        ",
        Value::Number(10.0)
    );
}

#[test]
fn structs() {
    let mut expected = HashMap::new();
    expected.insert("a".to_string(), Value::Number(10.0));
    expected.insert("b".to_string(), Value::Number(20.0));

    assert_eval!(
        "
        struct Test { a: Number, b: Number, }
        Test {
            a = 10,
            b = 20,
        }",
        Value::Struct(Rc::new("Test".to_string()), Rc::new(expected))
    );
}

#[test]
fn struct_access() {
    assert_eval!(
        "
        struct Test { a: Number, }
        (
            let map = Test { a = 5 };
            map.a
        )",
        Value::Number(5.0)
    );
}

#[test]
fn inherit() {
    let mut map = HashMap::new();
    map.insert("x".to_string(), Value::String(Rc::new("hello".to_string())));
    map.insert("y".to_string(), Value::Number(10.0));

    assert_eval!(
        r#"
        struct Test { x: String, y: Number, }
        let y = 10;
        Test {
            x = "hello",
            y
        }"#,
        Value::Struct(Rc::new("Test".to_string()), Rc::new(map))
    );
}

#[test]
fn lambda() {
    assert_eval!(
        "
        (
            let add = |l,r|: l + r;
            add 2 3
        )",
        Value::Number(5.0)
    );
}

#[test]
fn lambda_currying() {
    assert_eval!(
        "
        (
            let add = |l|: |r|: l + r;
            add 2 3
        )",
        Value::Number(5.0)
    );
}

#[test]
fn string_concat() {
    assert_eval!(
        r#""Hello" + " world!""#,
        Value::String(Rc::new("Hello world!".to_string()))
    );
}

#[test]
fn list() {
    let expected = vec![Value::Number(1.0), Value::Number(2.0), Value::Number(3.0)];
    assert_eval!(r#"[1, 2, 3]"#, Value::List(Rc::new(expected)));
}
#[test]
fn list_empty() {
    assert_eval!(r#"[]"#, Value::List(Rc::new(vec![])));
}

#[test]
fn if_expr() {
    assert_eval!("if true then 1 else 0", Value::Number(1.0));
}

#[test]
fn if_expr_nested() {
    assert_eval!(
        "if true then if false then 10 else 2 else 3",
        Value::Number(2.0)
    );
}

#[test]
fn type_constraint() {
    assert_eval!(
        "
            let x: Number = 10.0;
            x
        ",
        Value::Number(10.0)
    );
}

#[test]
fn type_constraint_lambda() {
    assert_eval!(
        "
            let f: fn Number Number -> Number = |x, y|: x + y + 1;
            f 1 2
        ",
        Value::Number(4.0)
    );
}

#[test]
fn type_constraint_paren() {
    assert_eval!(
        "
            let f: fn Number -> (fn Number -> Number) = |x, y|: x + y + 1;
            f 1 2
        ",
        Value::Number(4.0)
    );
}

#[test]
fn assign() {
    assert_eval!(
        "
            let a = 5;
            a = a + 1;
            a * 2
        ",
        Value::Number(12.0)
    );
}
