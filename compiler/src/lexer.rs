//! Lexer for the program language. Runs over the blanked program text
//! produced by `scan` (proof lines are spaces there, so spans line up with
//! the original file).

use crate::diag::Diagnostic;
use crate::span::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Tok {
    Ident(String),
    Int(i128),
    Bytes(Vec<u8>),
    Str(Vec<u8>),
    KwFn,
    KwReturn,
    KwIf,
    KwElse,
    KwTrue,
    KwFalse,
    KwWhile,
    KwFor,
    KwClass,
    KwInit,
    KwDeinit,
    KwVar,
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Amp,
    Dot,
    Colon,
    ColonColon,
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
            Tok::Bytes(_) => "byte-string literal".to_string(),
            Tok::Str(_) => "string literal".to_string(),
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
            Tok::KwClass => "class",
            Tok::KwInit => "init",
            Tok::KwDeinit => "deinit",
            Tok::KwVar => "var",
            Tok::LParen => "(",
            Tok::RParen => ")",
            Tok::LBrace => "{",
            Tok::RBrace => "}",
            Tok::LBracket => "[",
            Tok::RBracket => "]",
            Tok::Amp => "&",
            Tok::Dot => ".",
            Tok::Colon => ":",
            Tok::ColonColon => "::",
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

/// Lex the body of a byte-string literal. `open` is the offset of the
/// opening quote; returns the bytes and the offset just past the closing
/// quote. Non-ASCII source characters contribute their UTF-8 bytes
/// verbatim; escapes are `\n \r \t \0 \\ \" \xNN`.
fn lex_byte_string(text: &str, open: usize) -> Result<(Vec<u8>, usize), Diagnostic> {
    let bytes = text.as_bytes();
    let mut value = Vec::new();
    let mut i = open + 1;
    loop {
        if i >= bytes.len() || bytes[i] == b'\n' {
            return Err(Diagnostic {
                name: "lex.unterminated_string".into(),
                title: "unterminated byte-string literal".into(),
                span: Span::new(open, i),
                label: "no closing `\"` before the end of the line".into(),
                notes: vec![],
            });
        }
        match bytes[i] {
            b'"' => return Ok((value, i + 1)),
            b'\\' => {
                let esc_start = i;
                i += 1;
                let e = if i < bytes.len() { bytes[i] } else { b'\n' };
                match e {
                    b'n' => value.push(b'\n'),
                    b'r' => value.push(b'\r'),
                    b't' => value.push(b'\t'),
                    b'0' => value.push(0),
                    b'\\' => value.push(b'\\'),
                    b'"' => value.push(b'"'),
                    b'x' => {
                        let hex = text.get(i + 1..i + 3).unwrap_or("");
                        let byte = u8::from_str_radix(hex, 16).map_err(|_| Diagnostic {
                            name: "lex.bad_escape".into(),
                            title: "malformed `\\x` escape".into(),
                            span: Span::new(esc_start, (i + 3).min(bytes.len())),
                            label: "`\\x` takes exactly two hex digits (`\\x00`–`\\xff`)".into(),
                            notes: vec![],
                        })?;
                        value.push(byte);
                        i += 2;
                    }
                    _ => {
                        return Err(Diagnostic {
                            name: "lex.bad_escape".into(),
                            title: "unknown escape in byte-string literal".into(),
                            span: Span::new(esc_start, (i + 1).min(bytes.len())),
                            label: "the escapes are `\\n \\r \\t \\0 \\\\ \\\" \\xNN`".into(),
                            notes: vec![],
                        });
                    }
                }
                i += 1;
            }
            _ => {
                value.push(bytes[i]);
                i += 1;
            }
        }
    }
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
        // b"..." is a [u8] literal of the bytes between the quotes; a
        // bare "..." builds a `String` and must be valid UTF-8
        // (ADR 0014).
        if b == b'b' && i + 1 < bytes.len() && bytes[i + 1] == b'"' {
            let (value, end) = lex_byte_string(text, i + 1)?;
            tokens.push(Token {
                tok: Tok::Bytes(value),
                span: Span::new(start, end),
            });
            i = end;
            continue;
        }
        if b == b'"' {
            let (value, end) = lex_byte_string(text, i)?;
            // A bare literal builds a `String`; its bytes must be valid
            // UTF-8 (escapes can spell arbitrary bytes — those belong in
            // a b"..." byte literal).
            if std::str::from_utf8(&value).is_err() {
                return Err(Diagnostic {
                    name: "lex.string_not_utf8".into(),
                    title: "string literal is not valid UTF-8".into(),
                    span: Span::new(start, end),
                    label: "a `String` holds valid UTF-8; raw bytes are written `b\"...\"`".into(),
                    notes: vec![],
                });
            }
            tokens.push(Token {
                tok: Tok::Str(value),
                span: Span::new(start, end),
            });
            i = end;
            continue;
        }
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
                "class" => Tok::KwClass,
                "init" => Tok::KwInit,
                "deinit" => Tok::KwDeinit,
                "var" => Tok::KwVar,
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
            "::" => (Tok::ColonColon, 2),
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
                        title: format!(
                            "unexpected character `{}`",
                            text[i..].chars().next().unwrap()
                        ),
                        span: Span::new(i, i + 1),
                        label: "not part of the Sable program language".into(),
                        notes: vec![],
                    });
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
