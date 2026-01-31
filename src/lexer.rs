use logos::{Lexer, Logos, Span, SpannedIter};

#[derive(Logos, Clone, Debug, PartialEq)]
#[logos(skip r"[ \t\n\f]+")]
pub enum TokenKind {
    #[token("=")]
    Assign,
    #[token("+")]
    Add,
    #[token("-")]
    Sub,
    #[token("*")]
    Mul,
    #[token("/")]
    Div,

    #[token("(")]
    ParenL,
    #[token(")")]
    ParenR,
    #[token("{")]
    BraceL,
    #[token("}")]
    BraceR,

    #[token(":")]
    Colon,
    #[token(";")]
    Semicolon,
    #[token(",")]
    Comma,

    #[token("==")]
    Eq,
    #[token("!=")]
    NotEq,
    #[token("<")]
    Lt,
    #[token(">")]
    Gt,
    #[token("<=")]
    LtEq,
    #[token(">=")]
    GtEq,
    #[token("!")]
    Not,

    #[regex(r#""([^"\\]|\\.)*""#)]
    String,
    #[regex(r"[a-zA-Z_][a-zA-Z0-9_]*")]
    Ident,
    #[regex(r"[0-9]+(\.[0-9]+)?")]
    Number,
    #[allow(dead_code)]
    Eof,

    #[allow(dead_code)]
    None,
}

#[derive(Clone)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

impl Token {
    pub fn new(kind: TokenKind, span: impl Into<Span>) -> Self {
        Self {
            kind,
            span: span.into(),
        }
    }
}

#[derive(Clone)]
pub struct TokenIter<'a> {
    iter: SpannedIter<'a, TokenKind>,
}

impl Iterator for TokenIter<'_> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter
            .next()
            .and_then(|(kind, span)| kind.ok().map(|kind| Token::new(kind, span)))
    }
}

impl<'a> From<Lexer<'a, TokenKind>> for TokenIter<'a> {
    fn from(value: Lexer<'a, TokenKind>) -> Self {
        Self {
            iter: value.spanned(),
        }
    }
}
