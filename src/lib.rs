use bumpalo::Bump;
use logos::Lexer;

pub mod ast;
pub mod lexer;
pub mod parser;
#[cfg(feature = "serde")]
pub mod serialize;
pub mod target;
pub mod types;

#[cfg(feature = "serde")]
pub use serialize::de::from_str;

use crate::target::eval::Value;

/// run kisu program with pretty printed errors
pub fn run(source: &str) -> Result<Value, miette::Error> {
    let source = String::from(source);
    eval(&source).map_err(|error| miette::Error::new(error).with_source_code(source))
}

/// run kisu program with internal error type
pub fn eval(source: &str) -> Result<Value, Error> {
    let bump = Bump::new();

    let ast = {
        use crate::{lexer::TokenIter, parser::Parser};
        let lexer = Lexer::new(source);
        let mut parser = Parser::new(TokenIter::from(lexer), source, &bump);
        parser.parse()?
    };

    let typed_ast = {
        use crate::ast::untyped::Visitor;
        use crate::types::TypeChecker;
        let mut checker = TypeChecker::default();
        checker.visit_program(&ast)?;
        checker.consume()?
    };

    let result = {
        use crate::ast::typed::Visitor;
        use crate::target::eval::TreeWalker;
        let mut walker = TreeWalker::default();
        walker.visit_program(&typed_ast);
        walker.consume()
    };

    Ok(result)
}

#[derive(thiserror::Error, miette::Diagnostic, Debug)]
pub enum Error {
    #[error(transparent)]
    #[diagnostic(transparent)]
    Parser(#[from] parser::Error),
    #[cfg(feature = "serde")]
    #[error(transparent)]
    #[diagnostic(transparent)]
    Deserialize(#[from] serialize::de::Error),
    #[error(transparent)]
    #[diagnostic(transparent)]
    Type(#[from] types::Error),
}
