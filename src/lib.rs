use logos::Lexer;

use crate::{
    ast::Visitor,
    eval::{TreeWalker, Value},
    lexer::TokenIter,
    parser::Parser,
    types::TypeChecker,
};

pub mod ast;
pub mod deserialize;
pub mod eval;
pub mod lexer;
pub mod parser;
pub mod types;

pub use deserialize::from_str;

/// run kisu program with pretty printed errors
pub fn run(source: &str) -> Result<Value, miette::Error> {
    let source = String::from(source);
    eval(&source).map_err(|error| miette::Error::new(error).with_source_code(source))
}

/// run kisu program with internal error type
pub fn eval(source: &str) -> Result<Value, Error> {
    let lexer = Lexer::new(source);
    let mut parser = Parser::new(TokenIter::from(lexer), source);
    let program = parser.parse()?;
    let mut checker = TypeChecker::default();
    checker.check(&program)?;
    let mut walker = TreeWalker::default();
    walker.visit_program(&program)?;
    Ok(walker.consume()?)
}

#[derive(thiserror::Error, miette::Diagnostic, Debug)]
pub enum Error {
    #[error(transparent)]
    #[diagnostic(transparent)]
    Parser(#[from] parser::Error),
    #[error(transparent)]
    #[diagnostic(transparent)]
    Runtime(#[from] eval::Error),
    #[error(transparent)]
    #[diagnostic(transparent)]
    Deserialize(#[from] deserialize::Error),
    #[error(transparent)]
    #[diagnostic(transparent)]
    Type(#[from] types::Error),
}
