//! Handwritten recursive-descent parser for the M0 subset, plus positional
//! attachment of proof blocks to functions (design §1: a block attaches to
//! the item starting on the line right after its last `///` line; a blank
//! line detaches it).

use crate::ast::*;
use crate::diag::Diagnostic;
use crate::lexer::{Tok, Token};
use crate::scan::{ClauseKind, ProofBlock};
use crate::span::{LineMap, Span};

pub struct Parser<'a> {
    tokens: &'a [Token],
    pos: usize,
}

type PResult<T> = Result<T, Diagnostic>;

pub fn parse(
    tokens: &[Token],
    blocks: &[ProofBlock],
    lines: &LineMap,
) -> PResult<Program> {
    let mut parser = Parser { tokens, pos: 0 };
    let mut fns = Vec::new();
    let mut consumed = vec![false; blocks.len()];

    while !parser.at(&Tok::Eof) {
        let fn_line = lines.line_col(parser.peek_span().start).0;
        let mut f = parser.parse_fn()?;
        // Attach the proof block ending on the line just above `fn`.
        for (bi, block) in blocks.iter().enumerate() {
            if consumed[bi] || block.last_line + 1 != fn_line {
                continue;
            }
            consumed[bi] = true;
            for clause in &block.clauses {
                match clause.kind {
                    ClauseKind::Pre => f.pres.push(clause.clone()),
                    ClauseKind::Post => f.posts.push(clause.clone()),
                    other => {
                        return Err(Diagnostic {
                            name: "proof.bad_function_clause".into(),
                            title: format!(
                                "`{}` clause in a function contract block",
                                kind_word(other)
                            ),
                            span: clause.line_span,
                            label: "only `pre` and `post` may precede a function".into(),
                            notes: vec![(
                                "note".into(),
                                milestone_hint(other).into(),
                            )],
                        });
                    }
                }
            }
        }
        fns.push(f);
    }

    for (bi, block) in blocks.iter().enumerate() {
        if !consumed[bi] {
            return Err(Diagnostic {
                name: "proof.unattached_block".into(),
                title: "proof block is not attached to any function".into(),
                span: block.span,
                label: "no function starts on the next line".into(),
                notes: vec![(
                    "note".into(),
                    "free-floating (module-level) proof blocks and loop/statement \
                     annotations are not supported in M0; a blank line after a contract \
                     block detaches it from the function below"
                        .into(),
                )],
            });
        }
    }

    Ok(Program { fns })
}

fn kind_word(k: ClauseKind) -> &'static str {
    match k {
        ClauseKind::Pre => "pre",
        ClauseKind::Post => "post",
        ClauseKind::Invariant => "invariant",
        ClauseKind::Variant => "variant",
        ClauseKind::Assert => "assert",
        ClauseKind::Defer => "defer",
        ClauseKind::Assume => "assume",
        ClauseKind::GhostDef => "def",
        ClauseKind::Theorem => "theorem",
        ClauseKind::Discharge => "discharge",
        ClauseKind::Other => "<unrecognized>",
    }
}

fn milestone_hint(k: ClauseKind) -> &'static str {
    match k {
        ClauseKind::Invariant | ClauseKind::Variant => "loop annotations arrive in M1",
        ClauseKind::Assert | ClauseKind::Defer | ClauseKind::Assume => {
            "statement-level proof blocks arrive in M3"
        }
        ClauseKind::GhostDef | ClauseKind::Theorem | ClauseKind::Discharge => {
            "module-level proof blocks arrive with ghost definitions (M1-M2)"
        }
        _ => "unrecognized clause keyword; M0 supports `pre` and `post`",
    }
}

impl<'a> Parser<'a> {
    fn peek(&self) -> &Tok {
        &self.tokens[self.pos].tok
    }
    fn peek2(&self) -> &Tok {
        &self.tokens[(self.pos + 1).min(self.tokens.len() - 1)].tok
    }
    fn peek_span(&self) -> Span {
        self.tokens[self.pos].span
    }
    fn at(&self, t: &Tok) -> bool {
        self.peek() == t
    }
    fn bump(&mut self) -> Token {
        let t = self.tokens[self.pos].clone();
        if self.pos < self.tokens.len() - 1 {
            self.pos += 1;
        }
        t
    }
    fn expect(&mut self, t: Tok) -> PResult<Token> {
        if self.peek() == &t {
            Ok(self.bump())
        } else {
            Err(self.error_expected(&t.describe()))
        }
    }
    fn error_expected(&self, what: &str) -> Diagnostic {
        Diagnostic {
            name: "parse.expected".into(),
            title: format!("expected {what}, found {}", self.peek().describe()),
            span: self.peek_span(),
            label: format!("expected {what}"),
            notes: vec![],
        }
    }

    fn ident(&mut self) -> PResult<(String, Span)> {
        match self.peek().clone() {
            Tok::Ident(name) => {
                let span = self.peek_span();
                self.bump();
                Ok((name, span))
            }
            _ => Err(self.error_expected("an identifier")),
        }
    }

    fn ty(&mut self) -> PResult<(Ty, Span)> {
        let (name, span) = self.ident()?;
        ty_from_name(&name)
            .map(|t| (t, span))
            .ok_or_else(|| Diagnostic {
                name: "parse.unknown_type".into(),
                title: format!("unknown type `{name}`"),
                span,
                label: "expected `u8`..`u64`, `i8`..`i64`, or `bool`".into(),
                notes: vec![],
            })
    }

    fn parse_fn(&mut self) -> PResult<Fn> {
        let start = self.expect(Tok::KwFn)?.span;
        let (name, name_span) = self.ident()?;
        if is_reserved_name(&name) {
            return Err(reserved_name_error(&name, name_span, "function"));
        }
        self.expect(Tok::LParen)?;
        let mut params = Vec::new();
        if !self.at(&Tok::RParen) {
            loop {
                let (ty, tspan) = self.ty()?;
                let (pname, pspan) = self.ident()?;
                if is_reserved_name(&pname) {
                    return Err(reserved_name_error(&pname, pspan, "parameter"));
                }
                params.push(Param {
                    name: pname,
                    ty,
                    span: tspan.join(pspan),
                });
                if self.at(&Tok::Comma) {
                    self.bump();
                } else {
                    break;
                }
            }
        }
        self.expect(Tok::RParen)?;
        self.expect(Tok::Arrow)?;
        let (ret, _) = self.ty()?;
        let body = self.block()?;
        let end = self.tokens[self.pos.saturating_sub(1)].span;
        Ok(Fn {
            name,
            name_span,
            params,
            ret,
            pres: Vec::new(),
            posts: Vec::new(),
            body,
            span: start.join(end),
        })
    }

    fn block(&mut self) -> PResult<Vec<Stmt>> {
        self.expect(Tok::LBrace)?;
        let mut stmts = Vec::new();
        while !self.at(&Tok::RBrace) {
            if self.at(&Tok::Eof) {
                return Err(self.error_expected("`}`"));
            }
            stmts.push(self.stmt()?);
        }
        self.expect(Tok::RBrace)?;
        Ok(stmts)
    }

    fn stmt(&mut self) -> PResult<Stmt> {
        match self.peek().clone() {
            Tok::KwReturn => {
                let kw = self.bump().span;
                let value = self.expr()?;
                let end = self.expect(Tok::Semi)?.span;
                Ok(Stmt::Return {
                    value,
                    span: kw.join(end),
                })
            }
            Tok::KwIf => self.if_stmt(),
            Tok::Ident(first) => {
                // Two identifiers in a row: a declaration if the first names
                // a type; otherwise an assignment `x = expr;`.
                if let Tok::Ident(_) = self.peek2() {
                    let (ty, _) = self.ty()?;
                    let (name, name_span) = self.ident()?;
                    if is_reserved_name(&name) {
                        return Err(reserved_name_error(&name, name_span, "variable"));
                    }
                    let init = if self.at(&Tok::Assign) {
                        self.bump();
                        Some(self.expr()?)
                    } else {
                        None
                    };
                    self.expect(Tok::Semi)?;
                    Ok(Stmt::Decl {
                        ty,
                        name,
                        name_span,
                        init,
                    })
                } else {
                    let name_span = self.peek_span();
                    self.bump();
                    self.expect(Tok::Assign)?;
                    let value = self.expr()?;
                    self.expect(Tok::Semi)?;
                    Ok(Stmt::Assign {
                        name: first,
                        name_span,
                        value,
                    })
                }
            }
            _ => Err(self.error_expected("a statement")),
        }
    }

    fn if_stmt(&mut self) -> PResult<Stmt> {
        self.expect(Tok::KwIf)?;
        self.expect(Tok::LParen)?;
        let cond = self.expr()?;
        self.expect(Tok::RParen)?;
        let then_block = self.block()?;
        let else_block = if self.at(&Tok::KwElse) {
            self.bump();
            if self.at(&Tok::KwIf) {
                Some(vec![self.if_stmt()?])
            } else {
                Some(self.block()?)
            }
        } else {
            None
        };
        Ok(Stmt::If {
            cond,
            then_block,
            else_block,
        })
    }

    // Precedence climbing. Comparisons are non-associative by design.
    fn expr(&mut self) -> PResult<Expr> {
        self.or_expr()
    }

    fn or_expr(&mut self) -> PResult<Expr> {
        let mut lhs = self.and_expr()?;
        while self.at(&Tok::OrOr) {
            let op_span = self.bump().span;
            let rhs = self.and_expr()?;
            lhs = mk_bin(BinOp::Or, op_span, lhs, rhs);
        }
        Ok(lhs)
    }

    fn and_expr(&mut self) -> PResult<Expr> {
        let mut lhs = self.cmp_expr()?;
        while self.at(&Tok::AndAnd) {
            let op_span = self.bump().span;
            let rhs = self.cmp_expr()?;
            lhs = mk_bin(BinOp::And, op_span, lhs, rhs);
        }
        Ok(lhs)
    }

    fn cmp_expr(&mut self) -> PResult<Expr> {
        let lhs = self.add_expr()?;
        let op = match self.peek() {
            Tok::Lt => BinOp::Lt,
            Tok::Le => BinOp::Le,
            Tok::Gt => BinOp::Gt,
            Tok::Ge => BinOp::Ge,
            Tok::EqEq => BinOp::Eq,
            Tok::Ne => BinOp::Ne,
            _ => return Ok(lhs),
        };
        let op_span = self.bump().span;
        let rhs = self.add_expr()?;
        let e = mk_bin(op, op_span, lhs, rhs);
        // Non-associative: `a < b < c` is a parse error, on purpose.
        if matches!(
            self.peek(),
            Tok::Lt | Tok::Le | Tok::Gt | Tok::Ge | Tok::EqEq | Tok::Ne
        ) {
            return Err(Diagnostic {
                name: "parse.chained_comparison".into(),
                title: "comparison operators cannot be chained".into(),
                span: self.peek_span(),
                label: "use `&&` to combine comparisons".into(),
                notes: vec![],
            });
        }
        Ok(e)
    }

    fn add_expr(&mut self) -> PResult<Expr> {
        let mut lhs = self.mul_expr()?;
        loop {
            let op = match self.peek() {
                Tok::Plus => BinOp::Add,
                Tok::Minus => BinOp::Sub,
                _ => break,
            };
            let op_span = self.bump().span;
            let rhs = self.mul_expr()?;
            lhs = mk_bin(op, op_span, lhs, rhs);
        }
        Ok(lhs)
    }

    fn mul_expr(&mut self) -> PResult<Expr> {
        let mut lhs = self.unary_expr()?;
        loop {
            let op = match self.peek() {
                Tok::Star => BinOp::Mul,
                Tok::Slash => BinOp::Div,
                Tok::Percent => BinOp::Rem,
                _ => break,
            };
            let op_span = self.bump().span;
            let rhs = self.unary_expr()?;
            lhs = mk_bin(op, op_span, lhs, rhs);
        }
        Ok(lhs)
    }

    fn unary_expr(&mut self) -> PResult<Expr> {
        match self.peek() {
            Tok::Minus => {
                let span = self.bump().span;
                let operand = self.unary_expr()?;
                let full = span.join(operand.span);
                // Fold negative literals immediately so `-128` fits in i8.
                if let ExprKind::IntLit(n) = operand.kind {
                    return Ok(Expr {
                        kind: ExprKind::IntLit(-n),
                        span: full,
                        ty: None,
                    });
                }
                Ok(Expr {
                    kind: ExprKind::Unary {
                        op: UnOp::Neg,
                        operand: Box::new(operand),
                    },
                    span: full,
                    ty: None,
                })
            }
            Tok::Bang => {
                let span = self.bump().span;
                let operand = self.unary_expr()?;
                let full = span.join(operand.span);
                Ok(Expr {
                    kind: ExprKind::Unary {
                        op: UnOp::Not,
                        operand: Box::new(operand),
                    },
                    span: full,
                    ty: None,
                })
            }
            _ => self.postfix_expr(),
        }
    }

    fn postfix_expr(&mut self) -> PResult<Expr> {
        let e = self.primary_expr()?;
        if self.at(&Tok::LParen) {
            if let ExprKind::Var(name) = &e.kind {
                let callee = name.clone();
                let callee_span = e.span;
                self.bump();
                let mut args = Vec::new();
                if !self.at(&Tok::RParen) {
                    loop {
                        args.push(self.expr()?);
                        if self.at(&Tok::Comma) {
                            self.bump();
                        } else {
                            break;
                        }
                    }
                }
                let close = self.expect(Tok::RParen)?.span;
                return Ok(Expr {
                    kind: ExprKind::Call {
                        callee,
                        callee_span,
                        args,
                    },
                    span: callee_span.join(close),
                    ty: None,
                });
            }
            return Err(Diagnostic {
                name: "parse.bad_call".into(),
                title: "only named functions can be called".into(),
                span: self.peek_span(),
                label: "call target must be a function name".into(),
                notes: vec![],
            });
        }
        Ok(e)
    }

    fn primary_expr(&mut self) -> PResult<Expr> {
        let span = self.peek_span();
        match self.peek().clone() {
            Tok::Int(n) => {
                self.bump();
                Ok(Expr {
                    kind: ExprKind::IntLit(n),
                    span,
                    ty: None,
                })
            }
            Tok::KwTrue => {
                self.bump();
                Ok(Expr {
                    kind: ExprKind::BoolLit(true),
                    span,
                    ty: None,
                })
            }
            Tok::KwFalse => {
                self.bump();
                Ok(Expr {
                    kind: ExprKind::BoolLit(false),
                    span,
                    ty: None,
                })
            }
            Tok::Ident(name) => {
                self.bump();
                Ok(Expr {
                    kind: ExprKind::Var(name),
                    span,
                    ty: None,
                })
            }
            Tok::LParen => {
                self.bump();
                let mut e = self.expr()?;
                let close = self.expect(Tok::RParen)?.span;
                e.span = span.join(close);
                Ok(e)
            }
            _ => Err(self.error_expected("an expression")),
        }
    }
}

fn mk_bin(op: BinOp, op_span: Span, lhs: Expr, rhs: Expr) -> Expr {
    let span = lhs.span.join(rhs.span);
    Expr {
        kind: ExprKind::Binary {
            op,
            op_span,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        },
        span,
        ty: None,
    }
}

fn ty_from_name(name: &str) -> Option<Ty> {
    if name == "bool" {
        return Some(Ty::Bool);
    }
    IntTy::from_name(name).map(Ty::Int)
}

/// Names that would collide with the proof language or generated Lean.
fn is_reserved_name(name: &str) -> bool {
    const LEAN_KEYWORDS: &[&str] = &[
        "result", "old", "theorem", "def", "by", "fun", "match", "with", "do", "let", "have",
        "show", "from", "open", "import", "namespace", "end", "in", "at", "forall", "exists",
        "Prop", "Type", "Int", "Nat", "Bool", "True", "False",
    ];
    LEAN_KEYWORDS.contains(&name) || ty_from_name(name).is_some()
}

fn reserved_name_error(name: &str, span: Span, what: &str) -> Diagnostic {
    Diagnostic {
        name: "parse.reserved_name".into(),
        title: format!("`{name}` cannot be used as a {what} name"),
        span,
        label: "reserved by the proof language".into(),
        notes: vec![(
            "note".into(),
            "program identifiers appear verbatim in proofs, so names that collide \
             with Lean keywords or `result`/`old` are rejected"
                .into(),
        )],
    }
}
