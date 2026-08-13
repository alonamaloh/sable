//! Dynamic evaluation of the *monitorable fragment* of the proof language,
//! for `sable test` (design §9). This is deliberately a best-effort dev
//! tool, not a second checker of record (ADR 0002): anything outside the
//! fragment is reported as skipped, never guessed.
//!
//! Fragment: integer arithmetic (ℤ, Euclidean division), comparisons,
//! ∧ ∨ ¬ →, True/False, `a.len` / `a.get e`, `old a`, `result`, the
//! `iN.min`/`uN.max` constants, quantifiers over ranges derivable from
//! their guards, application of in-file ghost defs (recursion allowed,
//! depth-capped; exact i128 arithmetic — an overflow reports the clause
//! as unmonitorable rather than guessing), the
//! `match result with | some i => .. | none => ..` idiom, and
//! `Sable.Seq.perm` (checked as multiset equality).

use crate::ast::{GhostItem, IntTy, ValueTy};
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub enum SpecVal {
    Int(i128),
    Bool(bool),
    Arr(SpecArray),
    /// An ordinary option's proof value. Program-derived options retain their
    /// checked payload type even when absent, because `Option.value` is
    /// `getD default` in Lean: the junk value is `0` for integers and `false`
    /// for booleans. Clause literals are polymorphic and therefore carry no
    /// payload metadata until a surrounding program value supplies it.
    Opt {
        payload: Option<ValueTy>,
        value: Option<Box<SpecVal>>,
    },
    /// A class value: field name → value.
    Obj(HashMap<String, SpecVal>),
}

/// A monitored array retains its checked payload even when it is empty.
/// Fixed integer widths remain useful for faithful snapshots, although the
/// proof language itself observes every integer element as mathematical Int.
#[derive(Debug, Clone, PartialEq)]
pub enum SpecArray {
    Int { payload: IntTy, values: Vec<i128> },
    Bool(Vec<bool>),
}

impl SpecArray {
    fn len(&self) -> usize {
        match self {
            SpecArray::Int { values, .. } => values.len(),
            SpecArray::Bool(values) => values.len(),
        }
    }

    fn get_or_default(&self, index: i128) -> SpecVal {
        let index = usize::try_from(index).ok();
        match self {
            SpecArray::Int { values, .. } => SpecVal::Int(
                index
                    .and_then(|index| values.get(index).copied())
                    .unwrap_or(0),
            ),
            SpecArray::Bool(values) => SpecVal::Bool(
                index
                    .and_then(|index| values.get(index).copied())
                    .unwrap_or(false),
            ),
        }
    }
}

/// Why a clause could not be checked dynamically.
#[derive(Debug, Clone)]
pub struct Unmonitorable(pub String);

type EResult<T> = Result<T, Unmonitorable>;

// ---------------------------------------------------------------- tokens

#[derive(Debug, Clone, PartialEq)]
enum T {
    Ident(String),
    Num(i128),
    LParen,
    RParen,
    Comma,
    Bar,
    Arrow,    // → or ->
    FatArrow, // =>
    Iff,      // ↔ or <->
    Forall,
    Exists,
    Not,
    And,
    Or,
    Le,
    Ge,
    Ne,
    Lt,
    Gt,
    Eq,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    DotField(String), // `.len` / `.get` immediately after `)`
}

fn tokenize(text: &str) -> EResult<Vec<T>> {
    let mut out = Vec::new();
    let chars: Vec<char> = text.chars().collect();
    let mut i = 0;
    let mut prev_rparen = false;
    while i < chars.len() {
        let c = chars[i];
        let was_rparen = prev_rparen;
        prev_rparen = false;
        match c {
            c if c.is_whitespace() => {
                prev_rparen = was_rparen;
                i += 1;
            }
            '(' => {
                out.push(T::LParen);
                i += 1;
            }
            ')' => {
                out.push(T::RParen);
                prev_rparen = true;
                i += 1;
            }
            ',' => {
                out.push(T::Comma);
                i += 1;
            }
            '|' if chars.get(i + 1) == Some(&'|') => {
                out.push(T::Or);
                i += 2;
            }
            '|' => {
                out.push(T::Bar);
                i += 1;
            }
            '∀' => {
                out.push(T::Forall);
                i += 1;
            }
            '∃' => {
                out.push(T::Exists);
                i += 1;
            }
            '¬' => {
                out.push(T::Not);
                i += 1;
            }
            '!' if chars.get(i + 1) == Some(&'=') => {
                out.push(T::Ne);
                i += 2;
            }
            '!' => {
                out.push(T::Not);
                i += 1;
            }
            '∧' => {
                out.push(T::And);
                i += 1;
            }
            '&' if chars.get(i + 1) == Some(&'&') => {
                out.push(T::And);
                i += 2;
            }
            '∨' => {
                out.push(T::Or);
                i += 1;
            }
            '→' => {
                out.push(T::Arrow);
                i += 1;
            }
            '≤' => {
                out.push(T::Le);
                i += 1;
            }
            '≥' => {
                out.push(T::Ge);
                i += 1;
            }
            '≠' => {
                out.push(T::Ne);
                i += 1;
            }
            '↔' => {
                out.push(T::Iff);
                i += 1;
            }
            '<' if chars.get(i + 1) == Some(&'-') && chars.get(i + 2) == Some(&'>') => {
                out.push(T::Iff);
                i += 3;
            }
            '<' if chars.get(i + 1) == Some(&'=') => {
                out.push(T::Le);
                i += 2;
            }
            '>' if chars.get(i + 1) == Some(&'=') => {
                out.push(T::Ge);
                i += 2;
            }
            '<' => {
                out.push(T::Lt);
                i += 1;
            }
            '>' => {
                out.push(T::Gt);
                i += 1;
            }
            '=' if chars.get(i + 1) == Some(&'>') => {
                out.push(T::FatArrow);
                i += 2;
            }
            '=' => {
                out.push(T::Eq);
                i += 1;
            }
            '+' => {
                out.push(T::Plus);
                i += 1;
            }
            '-' if chars.get(i + 1) == Some(&'>') => {
                out.push(T::Arrow);
                i += 2;
            }
            '-' => {
                out.push(T::Minus);
                i += 1;
            }
            '*' => {
                out.push(T::Star);
                i += 1;
            }
            '/' if chars.get(i + 1) == Some(&'\\') => {
                out.push(T::And);
                i += 2;
            }
            '/' => {
                out.push(T::Slash);
                i += 1;
            }
            '%' => {
                out.push(T::Percent);
                i += 1;
            }
            '.' if was_rparen => {
                let start = i + 1;
                let mut j = start;
                while j < chars.len() && (chars[j].is_ascii_alphanumeric() || chars[j] == '_') {
                    j += 1;
                }
                out.push(T::DotField(chars[start..j].iter().collect()));
                // Postfix projections chain: `(old self).buf.get k`.
                prev_rparen = true;
                i = j;
            }
            c if c.is_ascii_digit() => {
                let start = i;
                while i < chars.len() && chars[i].is_ascii_digit() {
                    i += 1;
                }
                let s: String = chars[start..i].iter().collect();
                out.push(T::Num(s.parse().map_err(|_| {
                    Unmonitorable("integer literal too large".into())
                })?));
            }
            c if c.is_ascii_alphabetic() || c == '_' => {
                let start = i;
                while i < chars.len()
                    && (chars[i].is_ascii_alphanumeric()
                        || chars[i] == '_'
                        || chars[i] == '.'
                        || chars[i] == '\'')
                {
                    i += 1;
                }
                out.push(T::Ident(chars[start..i].iter().collect()));
            }
            other => {
                return Err(Unmonitorable(format!(
                    "`{other}` is outside the monitorable fragment"
                )));
            }
        }
    }
    Ok(out)
}

// ------------------------------------------------------------------ AST

#[derive(Debug, Clone)]
enum S {
    Num(i128),
    Var(String),
    Old(String),
    ConstBound(i128),
    Len(Box<S>),
    Get(Box<S>, Box<S>),
    Field(Box<S>, String),
    Neg(Box<S>),
    Bin(Op, Box<S>, Box<S>),
    Not(Box<S>),
    Quant {
        forall: bool,
        vars: Vec<String>,
        body: Box<S>,
    },
    SomeLit(Box<S>),
    NoneLit,
    Ite(Box<S>, Box<S>, Box<S>),
    IsSomeE(Box<S>),
    OptValE(Box<S>),
    App(String, Vec<S>),
    MatchOpt {
        scrutinee: Box<S>,
        some_var: String,
        some_body: Box<S>,
        none_body: Box<S>,
    },
    True,
    False,
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum Op {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
    And,
    Or,
    Imp,
    Iff,
}

struct P {
    toks: Vec<T>,
    pos: usize,
}

impl P {
    fn peek(&self) -> Option<&T> {
        self.toks.get(self.pos)
    }
    fn bump(&mut self) -> Option<T> {
        let t = self.toks.get(self.pos).cloned();
        if t.is_some() {
            self.pos += 1;
        }
        t
    }
    fn eat(&mut self, t: &T) -> bool {
        if self.peek() == Some(t) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn expr(&mut self) -> EResult<S> {
        self.iff()
    }
    /// `↔` sits BELOW `→`/`∨`/`∧`, matching Lean exactly — the monitor
    /// must parse the same proposition Lean elaborates.
    fn iff(&mut self) -> EResult<S> {
        let mut lhs = self.imp()?;
        while self.eat(&T::Iff) {
            let rhs = self.imp()?;
            lhs = S::Bin(Op::Iff, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }
    fn imp(&mut self) -> EResult<S> {
        let lhs = self.or()?;
        if self.eat(&T::Arrow) {
            let rhs = self.imp()?;
            return Ok(S::Bin(Op::Imp, Box::new(lhs), Box::new(rhs)));
        }
        Ok(lhs)
    }
    fn or(&mut self) -> EResult<S> {
        let mut lhs = self.and()?;
        while self.eat(&T::Or) {
            let rhs = self.and()?;
            lhs = S::Bin(Op::Or, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }
    fn and(&mut self) -> EResult<S> {
        let mut lhs = self.not()?;
        while self.eat(&T::And) {
            let rhs = self.not()?;
            lhs = S::Bin(Op::And, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }
    fn not(&mut self) -> EResult<S> {
        if self.eat(&T::Not) {
            return Ok(S::Not(Box::new(self.not()?)));
        }
        if matches!(self.peek(), Some(T::Forall) | Some(T::Exists)) {
            let forall = matches!(self.bump(), Some(T::Forall));
            let mut vars = Vec::new();
            while let Some(T::Ident(v)) = self.peek() {
                vars.push(v.clone());
                self.pos += 1;
            }
            if vars.is_empty() || !self.eat(&T::Comma) {
                return Err(Unmonitorable("malformed quantifier".into()));
            }
            let body = self.expr()?;
            return Ok(S::Quant {
                forall,
                vars,
                body: Box::new(body),
            });
        }
        self.cmp()
    }
    fn cmp(&mut self) -> EResult<S> {
        let lhs = self.add()?;
        let op = match self.peek() {
            Some(T::Lt) => Op::Lt,
            Some(T::Le) => Op::Le,
            Some(T::Gt) => Op::Gt,
            Some(T::Ge) => Op::Ge,
            Some(T::Eq) => Op::Eq,
            Some(T::Ne) => Op::Ne,
            _ => return Ok(lhs),
        };
        self.pos += 1;
        let rhs = self.add()?;
        Ok(S::Bin(op, Box::new(lhs), Box::new(rhs)))
    }
    fn add(&mut self) -> EResult<S> {
        let mut lhs = self.mul()?;
        loop {
            let op = match self.peek() {
                Some(T::Plus) => Op::Add,
                Some(T::Minus) => Op::Sub,
                _ => break,
            };
            self.pos += 1;
            let rhs = self.mul()?;
            lhs = S::Bin(op, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }
    fn mul(&mut self) -> EResult<S> {
        let mut lhs = self.unary()?;
        loop {
            let op = match self.peek() {
                Some(T::Star) => Op::Mul,
                Some(T::Slash) => Op::Div,
                Some(T::Percent) => Op::Mod,
                _ => break,
            };
            self.pos += 1;
            let rhs = self.unary()?;
            lhs = S::Bin(op, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }
    fn unary(&mut self) -> EResult<S> {
        if self.eat(&T::Minus) {
            return Ok(S::Neg(Box::new(self.unary()?)));
        }
        self.app()
    }

    /// Lean-style application: `head a1 a2 ...` while the next token can
    /// start an atom.
    fn app(&mut self) -> EResult<S> {
        let head = self.atom()?;
        let applicable = matches!(head, S::Var(_) | S::App(..));
        if !applicable {
            return Ok(head);
        }
        let mut args = Vec::new();
        while match self.peek() {
            Some(T::Num(_)) | Some(T::LParen) => true,
            Some(T::Ident(n)) => n != "then" && n != "else",
            _ => false,
        } {
            args.push(self.atom()?);
        }
        if args.is_empty() {
            return Ok(head);
        }
        let name = match head {
            S::Var(n) => n,
            S::App(n, existing) if existing.is_empty() => n,
            _ => return Err(Unmonitorable("higher-order application".into())),
        };
        // `old a` normalizes here.
        if name == "some" {
            if args.len() == 1 {
                return Ok(S::SomeLit(Box::new(args.into_iter().next().unwrap())));
            }
            return Err(Unmonitorable("`some` takes one value".into()));
        }
        if name == "old" {
            if args.len() == 1 {
                return oldify(args.into_iter().next().unwrap());
            }
            return Err(Unmonitorable("`old` applies to one variable".into()));
        }
        Ok(S::App(name, args))
    }

    fn atom(&mut self) -> EResult<S> {
        let t = self
            .bump()
            .ok_or_else(|| Unmonitorable("unexpected end of clause".into()))?;
        let mut base = match t {
            T::Num(n) => S::Num(n),
            T::LParen => {
                let e = self.expr()?;
                if !self.eat(&T::RParen) {
                    return Err(Unmonitorable("missing `)`".into()));
                }
                e
            }
            T::Ident(name) => match name.as_str() {
                "True" => S::True,
                "False" => S::False,
                // Lean's proposition literals are capitalized, while values
                // of program type `bool` use the lowercase constructors.
                // Both are represented by `SpecVal::Bool`; their surrounding
                // expression determines whether a proposition or Bool value
                // was intended.
                "true" => S::True,
                "false" => S::False,
                "none" => S::NoneLit,
                "match" => return self.match_opt(),
                "if" => return self.ite(),
                _ => ident_to_expr(&name)?,
            },
            other => {
                return Err(Unmonitorable(format!(
                    "{other:?} is outside the monitorable fragment"
                )));
            }
        };
        // Postfix `.len` / `.get e` after a parenthesized receiver.
        while let Some(T::DotField(f)) = self.peek().cloned() {
            self.pos += 1;
            base = match f.as_str() {
                "len" => S::Len(Box::new(base)),
                "is_some" => S::IsSomeE(Box::new(base)),
                "value" => S::OptValE(Box::new(base)),
                "get" => {
                    let idx = self.atom()?;
                    S::Get(Box::new(base), Box::new(idx))
                }
                // Any other name is a class-field projection, e.g.
                // `(old self).buf.get k`.
                other => S::Field(Box::new(base), other.to_string()),
            };
        }
        Ok(base)
    }

    /// `if C then A else B` — Lean ite, needed by cyclic-index ghost
    /// defs like `probe`/`dist` (ADR 0007).
    fn ite(&mut self) -> EResult<S> {
        let cond = self.expr()?;
        if !matches!(self.bump(), Some(T::Ident(w)) if w == "then") {
            return Err(Unmonitorable("expected `then`".into()));
        }
        let then_e = self.expr()?;
        if !matches!(self.bump(), Some(T::Ident(w)) if w == "else") {
            return Err(Unmonitorable("expected `else`".into()));
        }
        let else_e = self.expr()?;
        Ok(S::Ite(Box::new(cond), Box::new(then_e), Box::new(else_e)))
    }

    /// `match result with | some i => E | none => E` (either arm order).
    fn match_opt(&mut self) -> EResult<S> {
        let Some(T::Ident(scrut)) = self.bump() else {
            return Err(Unmonitorable("match scrutinee must be a variable".into()));
        };
        let scrutinee = Box::new(ident_to_expr(&scrut)?);
        if !matches!(self.bump(), Some(T::Ident(w)) if w == "with") {
            return Err(Unmonitorable("expected `with`".into()));
        }
        let mut some_var = None;
        let mut some_body = None;
        let mut none_body = None;
        for _ in 0..2 {
            if !self.eat(&T::Bar) {
                return Err(Unmonitorable("expected `|`".into()));
            }
            match self.bump() {
                Some(T::Ident(k)) if k == "some" => {
                    let Some(T::Ident(v)) = self.bump() else {
                        return Err(Unmonitorable("expected binder after `some`".into()));
                    };
                    if !self.eat(&T::FatArrow) {
                        return Err(Unmonitorable("expected `=>`".into()));
                    }
                    some_var = Some(v);
                    some_body = Some(self.expr()?);
                }
                Some(T::Ident(k)) if k == "none" => {
                    if !self.eat(&T::FatArrow) {
                        return Err(Unmonitorable("expected `=>`".into()));
                    }
                    none_body = Some(self.expr()?);
                }
                _ => return Err(Unmonitorable("expected `some` or `none` arm".into())),
            }
        }
        match (some_var, some_body, none_body) {
            (Some(v), Some(sb), Some(nb)) => Ok(S::MatchOpt {
                scrutinee,
                some_var: v,
                some_body: Box::new(sb),
                none_body: Box::new(nb),
            }),
            _ => Err(Unmonitorable("match needs `some` and `none` arms".into())),
        }
    }
}

/// Dotted identifiers: `a.len`, `a.get`, `self.buf.get`, `iN.max`,
/// `Sable.Seq.perm`, and general field paths on class values.
fn ident_to_expr(name: &str) -> EResult<S> {
    if let Some((head, field)) = name.rsplit_once('.') {
        return match field {
            "len" => Ok(S::Len(Box::new(ident_to_expr(head)?))),
            "is_some" => Ok(S::IsSomeE(Box::new(ident_to_expr(head)?))),
            "value" => Ok(S::OptValE(Box::new(ident_to_expr(head)?))),
            "get" => Ok(S::App(name.to_string(), vec![])), // args attach in app()
            "min" | "max" => {
                let it = IntTy::from_name(head)
                    .ok_or_else(|| Unmonitorable(format!("unknown constant `{name}`")))?;
                Ok(S::ConstBound(if field == "min" {
                    it.min()
                } else {
                    it.max()
                }))
            }
            "perm" => Ok(S::App("perm".to_string(), vec![])),
            _ => Ok(S::Field(Box::new(ident_to_expr(head)?), field.to_string())),
        };
    }
    Ok(S::Var(name.to_string()))
}

/// Rewrite the base variable of a path to its entry-state lookup:
/// `old self.len` means the entry value of `self.len`.
fn oldify(s: S) -> EResult<S> {
    Ok(match s {
        S::Var(v) => S::Old(v),
        S::Len(x) => S::Len(Box::new(oldify(*x)?)),
        S::Field(x, f) => S::Field(Box::new(oldify(*x)?), f),
        S::Get(x, i) => S::Get(Box::new(oldify(*x)?), i),
        S::Ite(c, a, b) => S::Ite(
            Box::new(oldify(*c)?),
            Box::new(oldify(*a)?),
            Box::new(oldify(*b)?),
        ),
        S::IsSomeE(x) => S::IsSomeE(Box::new(oldify(*x)?)),
        S::OptValE(x) => S::OptValE(Box::new(oldify(*x)?)),
        _ => return Err(Unmonitorable("`old` applies to a variable or path".into())),
    })
}

// ---------------------------------------------------------------- ghosts

pub struct GhostDefs {
    defs: HashMap<String, (Vec<String>, S)>,
}

impl GhostDefs {
    pub fn from_items(items: &[GhostItem]) -> Self {
        let mut defs = HashMap::new();
        for item in items.iter().filter(|g| g.keyword == "def") {
            if let Some((params, name, body)) = parse_ghost_def(&item.text) {
                defs.insert(name, (params, body));
            }
            // Unparseable defs simply stay unmonitorable at use sites.
        }
        GhostDefs { defs }
    }
}

/// `name (p q : ty) (r : ty) : RetTy := body`
fn parse_ghost_def(text: &str) -> Option<(Vec<String>, String, S)> {
    let (header, body) = text.split_once(":=")?;
    // Well-founded defs carry `termination_by`/`decreasing_by` tails whose
    // tactic text is not clause language (`:=`, ascriptions) — the monitor
    // only needs the equation, so cut the tail before tokenizing.
    let body = body.split("termination_by").next().unwrap_or(body);
    let header = header.trim();
    let name_end = header
        .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .unwrap_or(header.len());
    let name = header[..name_end].to_string();
    if name.is_empty() {
        return None;
    }
    let mut params = Vec::new();
    let mut rest = header[name_end..].trim_start();
    while let Some(inner_start) = rest.strip_prefix('(') {
        let close = inner_start.find(')')?;
        let group = &inner_start[..close];
        let names_part = group.split(':').next()?;
        for p in names_part.split_whitespace() {
            params.push(p.to_string());
        }
        rest = inner_start[close + 1..].trim_start();
    }
    let toks = tokenize(body).ok()?;
    let mut parser = P { toks, pos: 0 };
    let ast = parser.expr().ok()?;
    Some((params, name, ast))
}

// ------------------------------------------------------------------ eval

pub struct SpecEnv<'a> {
    pub vars: HashMap<String, SpecVal>,
    pub olds: HashMap<String, SpecVal>,
    pub ghosts: &'a GhostDefs,
}

const QUANT_CAP: u64 = 1_000_000;
const DEPTH_CAP: u32 = 64;

/// Evaluate an Int-valued spec expression (loop variants).
pub fn eval_int_expr(text: &str, env: &SpecEnv) -> EResult<i128> {
    let toks = tokenize(text)?;
    let mut parser = P { toks, pos: 0 };
    let ast = parser.expr()?;
    if parser.pos != parser.toks.len() {
        return Err(Unmonitorable("trailing tokens in expression".into()));
    }
    int(eval(&ast, env, 0)?)
}

pub fn eval_clause(text: &str, env: &SpecEnv) -> EResult<bool> {
    let toks = tokenize(text)?;
    let mut parser = P { toks, pos: 0 };
    let ast = parser.expr()?;
    if parser.pos != parser.toks.len() {
        return Err(Unmonitorable("trailing tokens in clause".into()));
    }
    match eval(&ast, env, 0)? {
        SpecVal::Bool(b) => Ok(b),
        _ => Err(Unmonitorable("clause is not a proposition".into())),
    }
}

fn eval(s: &S, env: &SpecEnv, depth: u32) -> EResult<SpecVal> {
    if depth > DEPTH_CAP {
        return Err(Unmonitorable("ghost definition recursion too deep".into()));
    }
    match s {
        S::Num(n) => Ok(SpecVal::Int(*n)),
        S::ConstBound(n) => Ok(SpecVal::Int(*n)),
        S::True => Ok(SpecVal::Bool(true)),
        S::False => Ok(SpecVal::Bool(false)),
        S::Var(v) => env
            .vars
            .get(v)
            .cloned()
            .ok_or_else(|| Unmonitorable(format!("`{v}` is not a program value here"))),
        S::Old(v) => env
            .olds
            .get(v)
            .cloned()
            .ok_or_else(|| Unmonitorable(format!("no entry snapshot for `{v}`"))),
        S::Len(a) => match eval(a, env, depth + 1)? {
            SpecVal::Arr(array) => Ok(SpecVal::Int(array.len() as i128)),
            // A class field that happens to be named `len`.
            SpecVal::Obj(fields) => fields
                .get("len")
                .cloned()
                .ok_or_else(|| Unmonitorable("no field `len`".into())),
            _ => Err(Unmonitorable("`.len` on a non-array".into())),
        },
        S::Field(recv, field) => match eval(recv, env, depth + 1)? {
            SpecVal::Obj(fields) => fields
                .get(field)
                .cloned()
                .ok_or_else(|| Unmonitorable(format!("no field `{field}`"))),
            _ => Err(Unmonitorable(format!("`.{field}` on a non-class value"))),
        },
        S::Get(a, i) => {
            let array = match eval(a, env, depth + 1)? {
                SpecVal::Arr(array) => array,
                _ => return Err(Unmonitorable("`.get` on a non-array".into())),
            };
            let idx = int(eval(i, env, depth + 1)?)?;
            // Off-range get is typed junk in the model; guards keep real
            // specifications in range.
            Ok(array.get_or_default(idx))
        }
        S::IsSomeE(x) => match eval(x, env, depth + 1)? {
            SpecVal::Opt { value, .. } => Ok(SpecVal::Bool(value.is_some())),
            _ => Err(Unmonitorable("`.is_some` on a non-option".into())),
        },
        S::OptValE(x) => match eval(x, env, depth + 1)? {
            SpecVal::Opt {
                value: Some(value), ..
            } => Ok(*value),
            // Junk-on-none matches the typed Lean model (`Option.getD
            // default`). Keeping the payload type on an absent program value
            // is what distinguishes integer zero from Boolean false here.
            SpecVal::Opt {
                payload,
                value: None,
            } => option_default(payload),
            _ => Err(Unmonitorable("`.value` on a non-option".into())),
        },
        S::Ite(c, a, b) => {
            if boolean(eval(c, env, depth + 1)?)? {
                eval(a, env, depth + 1)
            } else {
                eval(b, env, depth + 1)
            }
        }
        S::Neg(e) => Ok(SpecVal::Int(-int(eval(e, env, depth + 1)?)?)),
        S::Not(e) => Ok(SpecVal::Bool(!boolean(eval(e, env, depth + 1)?)?)),
        S::Bin(op, l, r) => {
            // Short-circuit the propositional ops.
            match op {
                Op::And => {
                    return Ok(SpecVal::Bool(
                        boolean(eval(l, env, depth + 1)?)? && boolean(eval(r, env, depth + 1)?)?,
                    ));
                }
                Op::Or => {
                    return Ok(SpecVal::Bool(
                        boolean(eval(l, env, depth + 1)?)? || boolean(eval(r, env, depth + 1)?)?,
                    ));
                }
                Op::Imp => {
                    return Ok(SpecVal::Bool(
                        !boolean(eval(l, env, depth + 1)?)? || boolean(eval(r, env, depth + 1)?)?,
                    ));
                }
                Op::Iff => {
                    return Ok(SpecVal::Bool(
                        boolean(eval(l, env, depth + 1)?)? == boolean(eval(r, env, depth + 1)?)?,
                    ));
                }
                _ => {}
            }
            let lv = eval(l, env, depth + 1)?;
            let rv = eval(r, env, depth + 1)?;
            if matches!(op, Op::Eq | Op::Ne) {
                if let (Some(b), true) = (spec_eq(&lv, &rv), true) {
                    return Ok(SpecVal::Bool(if *op == Op::Eq { b } else { !b }));
                }
            }
            let a = int(lv)?;
            let b = int(rv)?;
            Ok(match op {
                Op::Add => SpecVal::Int(a.checked_add(b).ok_or_else(ghost_overflow)?),
                Op::Sub => SpecVal::Int(a.checked_sub(b).ok_or_else(ghost_overflow)?),
                Op::Mul => SpecVal::Int(a.checked_mul(b).ok_or_else(ghost_overflow)?),
                Op::Div => SpecVal::Int(ediv(a, b)?),
                Op::Mod => SpecVal::Int(emod(a, b)?),
                Op::Lt => SpecVal::Bool(a < b),
                Op::Le => SpecVal::Bool(a <= b),
                Op::Gt => SpecVal::Bool(a > b),
                Op::Ge => SpecVal::Bool(a >= b),
                Op::Eq => SpecVal::Bool(a == b),
                Op::Ne => SpecVal::Bool(a != b),
                Op::And | Op::Or | Op::Imp | Op::Iff => unreachable!(),
            })
        }
        S::Quant { forall, vars, body } => eval_quant(*forall, vars, body, env, depth),
        S::NoneLit => Ok(SpecVal::Opt {
            payload: None,
            value: None,
        }),
        S::SomeLit(inner) => {
            let value = eval(inner, env, depth + 1)?;
            let payload = match &value {
                SpecVal::Bool(_) => Some(ValueTy::Bool),
                // The proof language erases fixed integer widths to `Int`, so
                // a standalone `some(1)` has no honest `IntTy` metadata. It
                // does not need one while present; `.value` returns the value.
                _ => None,
            };
            Ok(SpecVal::Opt {
                payload,
                value: Some(Box::new(value)),
            })
        }
        S::App(name, args) => {
            let base = name.rsplit('.').next().unwrap_or(name);
            match base {
                "sorted" if args.len() == 1 => {
                    let a = int_array(eval(&args[0], env, depth + 1)?, "sorted")?;
                    return Ok(SpecVal::Bool(a.windows(2).all(|w| w[0] <= w[1])));
                }
                "sortedRange" if args.len() == 3 => {
                    let a = int_array(eval(&args[0], env, depth + 1)?, "sortedRange")?;
                    let lo = int(eval(&args[1], env, depth + 1)?)?.max(0) as usize;
                    let hi = (int(eval(&args[2], env, depth + 1)?)?.max(0) as usize).min(a.len());
                    return Ok(SpecVal::Bool(
                        lo >= hi || a[lo..hi].windows(2).all(|w| w[0] <= w[1]),
                    ));
                }
                "contains" if args.len() == 2 => {
                    let a = int_array(eval(&args[0], env, depth + 1)?, "contains")?;
                    let v = int(eval(&args[1], env, depth + 1)?)?;
                    return Ok(SpecVal::Bool(a.contains(&v)));
                }
                "count" if args.len() == 2 => {
                    let a = int_array(eval(&args[0], env, depth + 1)?, "count")?;
                    let v = int(eval(&args[1], env, depth + 1)?)?;
                    return Ok(SpecVal::Int(a.iter().filter(|x| **x == v).count() as i128));
                }
                _ => {}
            }
            if name == "perm" || name.ends_with(".perm") {
                if args.len() != 2 {
                    return Err(Unmonitorable("`perm` takes two sequences".into()));
                }
                let a = int_array(eval(&args[0], env, depth + 1)?, "perm")?;
                let b = int_array(eval(&args[1], env, depth + 1)?, "perm")?;
                let mut sa = a.clone();
                let mut sb = b.clone();
                sa.sort_unstable();
                sb.sort_unstable();
                return Ok(SpecVal::Bool(sa == sb));
            }
            if let Some((head, "get")) = name.rsplit_once('.') {
                if args.len() == 1 {
                    let arr = eval(&ident_to_expr(head)?, env, depth + 1)?;
                    let arr = match arr {
                        SpecVal::Arr(array) => array,
                        _ => return Err(Unmonitorable("`.get` on a non-array".into())),
                    };
                    let idx = int(eval(&args[0], env, depth + 1)?)?;
                    return Ok(arr.get_or_default(idx));
                }
            }
            let Some((params, body)) = env.ghosts.defs.get(name) else {
                return Err(Unmonitorable(format!(
                    "`{name}` is not a monitorable definition"
                )));
            };
            if params.len() != args.len() {
                return Err(Unmonitorable(format!("`{name}` arity mismatch")));
            }
            let mut inner_vars = env.vars.clone();
            for (param, arg) in params.iter().zip(args) {
                let v = eval(arg, env, depth + 1)?;
                inner_vars.insert(param.clone(), v);
            }
            let inner = SpecEnv {
                vars: inner_vars,
                olds: env.olds.clone(),
                ghosts: env.ghosts,
            };
            eval(body, &inner, depth + 1)
        }
        S::MatchOpt {
            scrutinee,
            some_var,
            some_body,
            none_body,
        } => match eval(scrutinee, env, depth + 1)? {
            SpecVal::Opt {
                value: Some(value), ..
            } => {
                let mut inner_vars = env.vars.clone();
                inner_vars.insert(some_var.clone(), *value);
                let inner = SpecEnv {
                    vars: inner_vars,
                    olds: env.olds.clone(),
                    ghosts: env.ghosts,
                };
                eval(some_body, &inner, depth + 1)
            }
            SpecVal::Opt { value: None, .. } => eval(none_body, env, depth + 1),
            _ => Err(Unmonitorable("`match` scrutinee is not an option".into())),
        },
    }
}

/// Quantifiers: bounds are mined from `lo ≤ v` / `v < hi`-shaped guards in
/// the body's implication/conjunction spine, evaluated in the outer env.
/// A variable with no usable bound borrows the widest bounds any sibling
/// found (sound for checking: out-of-range instances are vacuous under
/// their guards). No bounds anywhere → unmonitorable.
fn eval_quant(
    forall: bool,
    vars: &[String],
    body: &S,
    env: &SpecEnv,
    depth: u32,
) -> EResult<SpecVal> {
    let mut guards: Vec<&S> = Vec::new();
    collect_guards(body, &mut guards);

    let mut bounds: Vec<(Option<i128>, Option<i128>)> = vec![(None, None); vars.len()];
    for g in &guards {
        if let S::Bin(op, l, r) = g {
            for (vi, v) in vars.iter().enumerate() {
                let (lo, hi) = &mut bounds[vi];
                match (&**l, op, &**r) {
                    (S::Var(x), Op::Le, other) if x == v => {
                        if let Ok(n) = closed_int(other, env, depth) {
                            *hi = Some(hi.map_or(n, |h: i128| h.min(n)));
                        }
                    }
                    (S::Var(x), Op::Lt, other) if x == v => {
                        if let Ok(n) = closed_int(other, env, depth) {
                            *hi = Some(hi.map_or(n - 1, |h: i128| h.min(n - 1)));
                        }
                    }
                    (other, Op::Le, S::Var(x)) if x == v => {
                        if let Ok(n) = closed_int(other, env, depth) {
                            *lo = Some(lo.map_or(n, |l: i128| l.max(n)));
                        }
                    }
                    (other, Op::Lt, S::Var(x)) if x == v => {
                        if let Ok(n) = closed_int(other, env, depth) {
                            *lo = Some(lo.map_or(n + 1, |l: i128| l.max(n + 1)));
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    let widest_lo = bounds.iter().filter_map(|b| b.0).min();
    let widest_hi = bounds.iter().filter_map(|b| b.1).max();
    let ranges: Vec<(i128, i128)> = bounds
        .iter()
        .map(|(lo, hi)| {
            let lo = lo.or(widest_lo);
            let hi = hi.or(widest_hi);
            match (lo, hi) {
                (Some(l), Some(h)) => Ok((l, h)),
                _ => Err(Unmonitorable(
                    "quantifier bounds are not derivable from guards".into(),
                )),
            }
        })
        .collect::<EResult<_>>()?;

    let mut total: u64 = 1;
    for (l, h) in &ranges {
        let n = (h - l + 1).max(0) as u64;
        total = total.saturating_mul(n);
        if total > QUANT_CAP {
            return Err(Unmonitorable(format!(
                "quantifier range too large to check ({total}+ instances)"
            )));
        }
    }

    let mut idx: Vec<i128> = ranges.iter().map(|(l, _)| *l).collect();
    loop {
        if idx.iter().zip(&ranges).all(|(v, (_, h))| v <= h) {
            let mut inner_vars = env.vars.clone();
            for (v, val) in vars.iter().zip(&idx) {
                inner_vars.insert(v.clone(), SpecVal::Int(*val));
            }
            let inner = SpecEnv {
                vars: inner_vars,
                olds: env.olds.clone(),
                ghosts: env.ghosts,
            };
            let b = boolean(eval(body, &inner, depth + 1)?)?;
            if forall && !b {
                return Ok(SpecVal::Bool(false));
            }
            if !forall && b {
                return Ok(SpecVal::Bool(true));
            }
        }
        // Odometer.
        let mut k = idx.len();
        loop {
            if k == 0 {
                return Ok(SpecVal::Bool(forall));
            }
            k -= 1;
            idx[k] += 1;
            if idx[k] <= ranges[k].1 {
                break;
            }
            idx[k] = ranges[k].0;
        }
    }
}

fn collect_guards<'a>(s: &'a S, out: &mut Vec<&'a S>) {
    match s {
        S::Bin(Op::Imp, l, r) => {
            collect_guards(l, out);
            collect_guards(r, out);
        }
        S::Bin(Op::And, l, r) => {
            collect_guards(l, out);
            collect_guards(r, out);
        }
        other => out.push(other),
    }
}

/// Evaluate an expression that must not mention quantifier variables.
fn closed_int(s: &S, env: &SpecEnv, depth: u32) -> EResult<i128> {
    int(eval(s, env, depth + 1)?)
}

fn option_default(payload: Option<ValueTy>) -> EResult<SpecVal> {
    match payload {
        Some(ValueTy::Int(_)) => Ok(SpecVal::Int(0)),
        Some(ValueTy::Bool) => Ok(SpecVal::Bool(false)),
        Some(ValueTy::Record(_)) => Err(Unmonitorable(
            "the monitor has no default value for a POD-record option".into(),
        )),
        Some(ValueTy::Param(_)) => Err(Unmonitorable(
            "an unresolved option payload reached the dynamic monitor".into(),
        )),
        None => Err(Unmonitorable(
            "cannot determine the payload type of `none.value`".into(),
        )),
    }
}

fn spec_eq(a: &SpecVal, b: &SpecVal) -> Option<bool> {
    match (a, b) {
        (SpecVal::Int(x), SpecVal::Int(y)) => Some(x == y),
        (SpecVal::Bool(x), SpecVal::Bool(y)) => Some(x == y),
        (
            SpecVal::Arr(SpecArray::Int { values: x, .. }),
            SpecVal::Arr(SpecArray::Int { values: y, .. }),
        ) => Some(x == y),
        (SpecVal::Arr(SpecArray::Bool(x)), SpecVal::Arr(SpecArray::Bool(y))) => Some(x == y),
        (SpecVal::Arr(_), SpecVal::Arr(_)) => None,
        (SpecVal::Opt { value: x, .. }, SpecVal::Opt { value: y, .. }) => match (x, y) {
            (None, None) => Some(true),
            (Some(_), None) | (None, Some(_)) => Some(false),
            (Some(x), Some(y)) => spec_eq(x, y),
        },
        (SpecVal::Obj(x), SpecVal::Obj(y)) => Some(x == y),
        _ => None,
    }
}

fn ghost_overflow() -> Unmonitorable {
    Unmonitorable("ghost arithmetic exceeded i128".into())
}

fn ediv(a: i128, b: i128) -> EResult<i128> {
    if b == 0 {
        return Err(Unmonitorable("division by zero in ghost arithmetic".into()));
    }
    let q = a.div_euclid(b);
    Ok(q)
}

fn emod(a: i128, b: i128) -> EResult<i128> {
    if b == 0 {
        return Err(Unmonitorable("modulo by zero in ghost arithmetic".into()));
    }
    Ok(a.rem_euclid(b))
}

fn int(v: SpecVal) -> EResult<i128> {
    match v {
        SpecVal::Int(n) => Ok(n),
        _ => Err(Unmonitorable("expected an integer value".into())),
    }
}

fn boolean(v: SpecVal) -> EResult<bool> {
    match v {
        SpecVal::Bool(b) => Ok(b),
        _ => Err(Unmonitorable("expected a proposition".into())),
    }
}

fn int_array(v: SpecVal, operation: &str) -> EResult<Vec<i128>> {
    match v {
        SpecVal::Arr(SpecArray::Int { values, .. }) => Ok(values),
        SpecVal::Arr(SpecArray::Bool(_)) => Err(Unmonitorable(format!(
            "`{operation}` is integer-array-only; Boolean arrays are unsupported"
        ))),
        _ => Err(Unmonitorable(format!(
            "`{operation}` expected a sequence value"
        ))),
    }
}

#[cfg(test)]
mod g1_option_monitor_tests {
    use super::*;

    fn option(payload: ValueTy, value: Option<SpecVal>) -> SpecVal {
        SpecVal::Opt {
            payload: Some(payload),
            value: value.map(Box::new),
        }
    }

    #[test]
    fn typed_none_uses_the_lean_default_for_its_payload() {
        let ghosts = GhostDefs::from_items(&[]);
        let mut vars = HashMap::new();
        vars.insert("integer".into(), option(ValueTy::Int(IntTy::I32), None));
        vars.insert(
            "integer_some".into(),
            option(ValueTy::Int(IntTy::I32), Some(SpecVal::Int(7))),
        );
        vars.insert("boolean".into(), option(ValueTy::Bool, None));
        let env = SpecEnv {
            vars,
            olds: HashMap::new(),
            ghosts: &ghosts,
        };

        assert!(eval_clause("integer.value = 0", &env).unwrap());
        assert!(eval_clause("integer_some = some(7)", &env).unwrap());
        assert!(eval_clause("boolean.value = false", &env).unwrap());
        assert!(eval_clause("boolean = none", &env).unwrap());
        assert!(!eval_clause("boolean.is_some", &env).unwrap());
    }

    #[test]
    fn boolean_some_literals_access_and_match_without_integer_coercion() {
        let ghosts = GhostDefs::from_items(&[]);
        let mut vars = HashMap::new();
        vars.insert(
            "o".into(),
            option(ValueTy::Bool, Some(SpecVal::Bool(false))),
        );
        let env = SpecEnv {
            vars,
            olds: HashMap::new(),
            ghosts: &ghosts,
        };

        assert!(eval_clause("o = some(false)", &env).unwrap());
        assert!(eval_clause("o.value = false", &env).unwrap());
        assert!(eval_clause("match o with | some b => b = false | none => False", &env).unwrap());
    }

    #[test]
    fn unsupported_absent_payload_defaults_fail_closed() {
        let ghosts = GhostDefs::from_items(&[]);
        let mut vars = HashMap::new();
        vars.insert("record_option".into(), option(ValueTy::Record(0), None));
        let env = SpecEnv {
            vars,
            olds: HashMap::new(),
            ghosts: &ghosts,
        };

        let error = eval_clause("record_option.value = 0", &env).unwrap_err();
        assert!(error.0.contains("no default value for a POD-record option"));
    }

    #[test]
    fn boolean_arrays_support_length_get_equality_and_typed_junk() {
        let ghosts = GhostDefs::from_items(&[]);
        let mut vars = HashMap::new();
        vars.insert(
            "flags".into(),
            SpecVal::Arr(SpecArray::Bool(vec![true, false, true])),
        );
        vars.insert(
            "same".into(),
            SpecVal::Arr(SpecArray::Bool(vec![true, false, true])),
        );
        vars.insert("empty".into(), SpecVal::Arr(SpecArray::Bool(Vec::new())));
        vars.insert(
            "integers".into(),
            SpecVal::Arr(SpecArray::Int {
                payload: IntTy::U8,
                values: vec![1, 0, 1],
            }),
        );
        vars.insert(
            "wide_integers".into(),
            SpecVal::Arr(SpecArray::Int {
                payload: IntTy::I64,
                values: vec![1, 0, 1],
            }),
        );
        let env = SpecEnv {
            vars,
            olds: HashMap::new(),
            ghosts: &ghosts,
        };

        assert!(eval_clause("flags.len = 3", &env).unwrap());
        assert!(eval_clause("flags.get 0 = true", &env).unwrap());
        assert!(eval_clause("flags.get 1 = false", &env).unwrap());
        assert!(eval_clause("empty.get 0 = false", &env).unwrap());
        assert!(eval_clause("flags = same", &env).unwrap());
        assert!(eval_clause("flags = integers", &env).is_err());
        assert!(eval_clause("flags ≠ integers", &env).is_err());
        assert!(eval_clause("integers = wide_integers", &env).unwrap());
    }

    #[test]
    fn integer_only_sequence_helpers_reject_boolean_arrays_explicitly() {
        let ghosts = GhostDefs::from_items(&[]);
        let mut vars = HashMap::new();
        vars.insert(
            "flags".into(),
            SpecVal::Arr(SpecArray::Bool(vec![false, true])),
        );
        let env = SpecEnv {
            vars,
            olds: HashMap::new(),
            ghosts: &ghosts,
        };

        for (operation, clause) in [
            ("sorted", "sorted flags"),
            ("sortedRange", "sortedRange flags 0 2"),
            ("contains", "contains flags 1"),
            ("count", "count flags 1 = 0"),
            ("perm", "perm flags flags"),
        ] {
            let error = eval_clause(clause, &env)
                .expect_err("integer-only sequence helpers must reject Boolean arrays");
            assert!(
                error
                    .0
                    .contains(&format!("`{operation}` is integer-array-only")),
                "{clause}: {}",
                error.0
            );
        }
    }
}
