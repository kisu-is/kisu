use kisu::{eval::Value, run};

macro_rules! assert_eval {
    ($src:literal, $eq:expr) => {{
        let src = indoc::indoc! {$src};
        println!("{}", src);

        match run(src) {
            Err(e) => panic!("{:#?}", e),
            Ok(v) => assert_eq!(v, $eq),
        }
    }};
}

#[test]
fn add() {
    assert_eval!("1 + 2", Value::Number(3.0.into()));
}

#[test]
fn sub() {
    assert_eval!("5 - 2", Value::Number(3.0.into()));
}

#[test]
fn mul() {
    assert_eval!("3 * 4", Value::Number(12.0.into()));
}

#[test]
fn div() {
    assert_eval!("10 / 2", Value::Number(5.0.into()));
}

#[test]
fn precedence() {
    assert_eval!("1 + 2 * 3", Value::Number(7.0.into()));
}

#[test]
fn unary() {
    assert_eval!("-10", Value::Number((-10.0).into()));
}

#[test]
fn complex() {
    assert_eval!("-1 + 2 * 3", Value::Number(5.0.into()));
}

#[test]
fn paren() {
    assert_eval!("{1 + 2} * 3", Value::Number(9.0.into()));
}

#[test]
fn string() {
    assert_eval!(r#""hello""#, Value::String("hello".into()));
}

#[test]
fn block() {
    assert_eval!("{ 42 }", Value::Number(42.0.into()));
}

#[test]
fn block_with_binding() {
    assert_eval!(
        "
        {
            a = 10;
            a * 2
        }",
        Value::Number(20.0.into())
    );
}

#[test]
fn map() {
    use std::collections::HashMap;
    let mut expected = HashMap::new();
    expected.insert("a".to_string(), Value::Number(10.0.into()));
    expected.insert("b".to_string(), Value::Number(20.0.into()));

    assert_eval!(
        "
        {
            a = 10;
            b = 20;
        }",
        Value::Map(expected)
    );
}

#[test]
fn map_access() {
    assert_eval!(
        "
        {
            map = { a = 5; };
            map.a
        }",
        Value::Number(5.0.into())
    );
}

#[test]
fn map_string_key() {
    use std::collections::HashMap;
    let mut expected = HashMap::new();
    expected.insert("a".to_string(), Value::Number(10.0.into()));
    expected.insert("b".to_string(), Value::Number(20.0.into()));

    assert_eval!(
        r#"
        {
            "a" = 10;
            "b" = 20;
        }"#,
        Value::Map(expected)
    );
}

#[test]
fn inherit() {
    use std::collections::HashMap;
    let mut map = HashMap::new();
    map.insert("x".to_string(), Value::String("hello".into()));
    let mut map2 = HashMap::new();
    map2.insert("x".to_string(), Value::String("hello".into()));
    map.insert("y".to_string(), Value::Map(map2));

    assert_eval!(
        r#"
        {
            x = "hello";
            y = {
                x;
            };
        }"#,
        Value::Map(map)
    );
}

#[test]
fn inherit_string_key() {
    use std::collections::HashMap;
    let mut map = HashMap::new();
    map.insert("a b".to_string(), Value::String("hello".into()));
    let mut map2 = HashMap::new();
    map2.insert("a b".to_string(), Value::String("hello".into()));
    map.insert("c".to_string(), Value::Map(map2));

    assert_eval!(
        r#"
        {
            "a b" = "hello";
            c = {
                "a b";
            };
        }"#,
        Value::Map(map)
    );
}

#[test]
fn lambda() {
    assert_eval!(
        "
        {
            add_one = x: x + 1;
            add_one 2
        }",
        Value::Number(3.0.into())
    );
}

#[test]
fn named_lambda() {
    assert_eval!(
        "
        {
            add = {l;r}: l + r;
            add {l = 2; r = 3;}
        }",
        Value::Number(5.0.into())
    );
}

#[test]
fn lambda_currying() {
    assert_eval!(
        "
        {
            add = l: r: l + r;
            add 2 3
        }",
        Value::Number(5.0.into())
    );
}

#[test]
fn lambda_string_param() {
    assert_eval!(
        r#"
        {
            add = "l": "r": l + r;
            add 5 6
        }"#,
        Value::Number(11.0.into())
    );
}

#[test]
fn named_lambda_string_param() {
    assert_eval!(
        r#"
        {
            add = {"l";"r"}: l + r;
            add {l = 5; r = 6;}
        }"#,
        Value::Number(11.0.into())
    );
}

#[test]
fn string_concat() {
    assert_eval!(
        r#""Hello" + " world!""#,
        Value::String("Hello world!".into())
    );
}

#[test]
fn list() {
    let expected = vec![
        Value::Number(1.0.into()),
        Value::String("forsen".into()),
        Value::Number(3.0.into()),
    ];
    assert_eval!(r#"[1; "forsen"; 3]"#, Value::List(expected));
}
#[test]
fn list_empty() {
    assert_eval!(r#"[]"#, Value::List(vec![]));
}
