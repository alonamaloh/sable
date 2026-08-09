//! Lexer for the program language. Runs over the blanked program text
//! produced by `scan` (proof lines are spaces there, so spans line up with
//! the original file).

use crate::diag::Diagnostic;
use crate::span::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Tok {
    Ident(String),
    Int(i128),
    KwFn,
    KwReturn,
    KwIf,
    KwElse,
    KwTrue,
    KwFalse,
    KwWhile,
    KwFor,
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Amp,
    Dot,
    Colon,
    Comma,
    Semi,
    Arrow,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Lt,
    Le,
    Gt,
    Ge,
    EqEq,
    Ne,
    AndAnd,
    OrOr,
    Bang,
    Assign,
    Eof,
}

impl Tok {
    pub fn describe(&self) -> String {
        match self {
            Tok::Ident(s) => format!("identifier `{s}`"),
            Tok::Int(n) => format!("integer literal `{n}`"),
            Tok::Eof => "end of file".to_string(),
            other => format!("`{}`", other.text()),
        }
    }
    fn text(&self) -> &'static str {
        match self {
            Tok::KwFn => "fn",
            Tok::KwReturn => "return",
            Tok::KwIf => "if",
            Tok::KwElse => "else",
            Tok::KwTrue => "true",
            Tok::KwFalse => "false",
            Tok::KwWhile => "while",
            Tok::KwFor => "for",
            Tok::LParen => "(",
            Tok::RParen => ")",
            Tok::LBrace => "{",
            Tok::RBrace => "}",
            Tok::LBracket => "[",
            Tok::RBracket => "]",
            Tok::Amp => "&",
            Tok::Dot => ".",
            Tok::Colon => ":",
            Tok::Comma => ",",
            Tok::Semi => ";",
            Tok::Arrow => "->",
            Tok::Plus => "+",
            Tok::Minus => "-",
            Tok::Star => "*",
            Tok::Slash => "/",
            Tok::Percent => "%",
            Tok::Lt => "<",
            Tok::Le => "<=",
            Tok::Gt => ">",
            Tok::Ge => ">=",
            Tok::EqEq => "==",
            Tok::Ne => "!=",
            Tok::AndAnd => "&&",
            Tok::OrOr => "||",
            Tok::Bang => "!",
            Tok::Assign => "=",
            _ => "",
        }
    }
}

#[derive(Debug, Clone)]
pub struct Token {
    pub tok: Tok,
    pub span: Span,
}

pub fn lex(text: &str) -> Result<Vec<Token>, Diagnostic> {
    let bytes = text.as_bytes();
    let mut tokens = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        let b = bytes[i];
        if b.is_ascii_whitespace() {
            i += 1;
            continue;
        }
        // Line comment. `///` never reaches the lexer (blanked by scan).
        if b == b'/' && i + 1 < bytes.len() && bytes[i + 1] == b'/' {
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        let start = i;
        if b.is_ascii_alphabetic() || b == b'_' {
            while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                i += 1;
            }
            let word = &text[start..i];
            let span = Span::new(start, i);
            if word.starts_with('_') {
                return Err(Diagnostic {
                    name: "lex.reserved_underscore".into(),
                    title: format!("identifier `{word}` starts with `_`"),
                    span,
                    label: "identifiers starting with `_` are reserved for the compiler".into(),
                    notes: vec![],
                });
            }
            let tok = match word {
                "fn" => Tok::KwFn,
                "return" => Tok::KwReturn,
                "if" => Tok::KwIf,
                "else" => Tok::KwElse,
                "true" => Tok::KwTrue,
                "false" => Tok::KwFalse,
                "while" => Tok::KwWhile,
                "for" => Tok::KwFor,
                _ => Tok::Ident(word.to_string()),
            };
            tokens.push(Token { tok, span });
            continue;
        }
        if b.is_ascii_digit() {
            while i < bytes.len() && (bytes[i].is_ascii_digit() || bytes[i] == b'_') {
                i += 1;
            }
            let raw: String = text[start..i].chars().filter(|c| *c != '_').collect();
            let span = Span::new(start, i);
            let value: i128 = raw.parse().map_err(|_| Diagnostic {
                name: "lex.int_too_large".into(),
                title: format!("integer literal `{raw}` is too large"),
                span,
                label: "does not fit in any Sable integer type".into(),
                notes: vec![],
            })?;
            tokens.push(Token {
                tok: Tok::Int(value),
                span,
            });
            continue;
        }
        let two = if i + 1 < bytes.len() {
            &text[i..i + 2]
        } else {
            ""
        };
        let (tok, len) = match two {
            "->" => (Tok::Arrow, 2),
            "<=" => (Tok::Le, 2),
            ">=" => (Tok::Ge, 2),
            "==" => (Tok::EqEq, 2),
            "!=" => (Tok::Ne, 2),
            "&&" => (Tok::AndAnd, 2),
            "||" => (Tok::OrOr, 2),
            _ => match b {
                b'(' => (Tok::LParen, 1),
                b')' => (Tok::RParen, 1),
                b'{' => (Tok::LBrace, 1),
                b'}' => (Tok::RBrace, 1),
                b'[' => (Tok::LBracket, 1),
                b']' => (Tok::RBracket, 1),
                b'&' => (Tok::Amp, 1),
                b'.' => (Tok::Dot, 1),
                b':' => (Tok::Colon, 1),
                b',' => (Tok::Comma, 1),
                b';' => (Tok::Semi, 1),
                b'+' => (Tok::Plus, 1),
                b'-' => (Tok::Minus, 1),
                b'*' => (Tok::Star, 1),
                b'/' => (Tok::Slash, 1),
                b'%' => (Tok::Percent, 1),
                b'<' => (Tok::Lt, 1),
                b'>' => (Tok::Gt, 1),
                b'!' => (Tok::Bang, 1),
                b'=' => (Tok::Assign, 1),
                _ => {
                    return Err(Diagnostic {
                        name: "lex.unexpected_char".into(),
                        title: format!("unexpected character `{}`", text[i..].chars().next().unwrap()),
                        span: Span::new(i, i + 1),
                        label: "not part of the Sable program language".into(),
                        notes: vec![],
                    })
                }
            },
        };
        tokens.push(Token {
            tok,
            span: Span::new(i, i + len),
        });
        i += len;
    }
    tokens.push(Token {
        tok: Tok::Eof,
        span: Span::new(text.len(), text.len()),
    });
    Ok(tokens)
}
