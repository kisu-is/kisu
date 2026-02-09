#[test]
fn structs() {
    #[derive(serde::Deserialize, Debug, PartialEq)]
    struct Config {
        name: String,
    }

    let config: Config =
        kisu::from_str(r#"struct Config { name: String; } Config { name = "Joe"; }"#).unwrap();

    assert_eq!(
        config,
        Config {
            name: "Joe".to_string()
        }
    )
}

#[test]
fn struct_nested() {
    #[derive(serde::Deserialize, Debug, PartialEq)]
    struct Config {
        user: User,
    }

    #[derive(serde::Deserialize, Debug, PartialEq)]
    struct User {
        name: String,
    }

    let config: Config = kisu::from_str(
        r#"
        struct User { name: String; }
        struct Config { user: User; }
        Config {
            user = User { name = "Joe"; };
        }
        "#,
    )
    .unwrap();

    assert_eq!(
        config,
        Config {
            user: User {
                name: "Joe".to_string()
            }
        }
    )
}

#[test]
fn number() {
    let config: f32 = kisu::from_str(r#" 10.0 "#).unwrap();

    assert_eq!(config, 10.0)
}

#[test]
fn string() {
    let config: String = kisu::from_str(r#" "Hello" + " world!" "#).unwrap();

    assert_eq!(config, "Hello world!".to_string())
}

#[test]
fn list() {
    #[derive(serde::Deserialize, Debug, PartialEq)]
    struct Config {
        features: Vec<String>,
    }

    let config: Config = kisu::from_str(
        r#"struct Config { features: [String]; } Config { features = [ "derive" ]; }"#,
    )
    .unwrap();

    assert_eq!(
        config,
        Config {
            features: vec!["derive".into()]
        }
    )
}
