use logos::Lexer;

use crate::{
    eval::{Scope, Value},
    lexer::TokenIter,
    parser::Parser,
};

pub mod ast;
pub mod eval;
pub mod lexer;
pub mod parser;

pub fn run(source: &str) -> Result<Value, Error> {
    let lexer = Lexer::new(source);
    let mut parser = Parser::new(TokenIter::from(lexer), source);
    let expr = parser.parse_program()?;
    let mut env = Scope::new();
    Ok(eval::eval(&expr, &mut env)?)
}

#[derive(thiserror::Error, Debug, PartialEq)]
pub enum Error {
    #[error("error parsing")]
    Parser(#[from] parser::Error),
    #[error("error evaluating")]
    Eval(#[from] eval::Error),
}
