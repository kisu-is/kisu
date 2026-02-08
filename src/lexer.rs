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
    #[token("[")]
    BracketL,
    #[token("]")]
    BracketR,
    #[token("{")]
    BraceL,
    #[token("}")]
    BraceR,
    #[token("|")]
    Pipe,

    #[token(":")]
    Colon,
    #[token(";")]
    Semicolon,
    #[token(",")]
    Comma,
    #[token(".")]
    Dot,

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
    #[token("if")]
    If,
    #[token("else")]
    Else,
    #[token("then")]
    Then,
    #[token("true")]
    True,
    #[token("false")]
    False,

    #[token("fn")]
    Fn,
    #[token("->")]
    Arrow,

    #[regex(r#""([^"\\]|\\.)*""#)]
    String,
    #[regex(r"[A-Z][a-zA-Z0-9_]*")]
    TypeIdent,
    #[regex(r"[a-z_][a-zA-Z0-9_]*")]
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

    pub const NONE: Self = Self {
        kind: TokenKind::None,
        span: 0..0,
    };
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
