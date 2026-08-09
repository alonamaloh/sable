//! Handwritten recursive-descent parser, plus positional attachment of
//! proof blocks (design §1): a block attaches to the item starting on the
//! line right after its last `///` line; a blank line detaches it.
//! Attachment targets in M1: functions (`pre`/`post`/`variant`), `while`
//! loops (`invariant`/`variant`), the post-signature position
//! (`variant`, design §8 style), and free-floating `discharge` blocks.

use crate::ast::*;
use crate::diag::Diagnostic;
use crate::lexer::{Tok, Token};
use crate::scan::{Clause, ClauseKind, ProofBlock};
use crate::span::{LineMap, Span};

pub struct Parser<'a> {
    tokens: &'a [Token],
    pos: usize,
    blocks: &'a [ProofBlock],
    consumed: Vec<bool>,
    lines: &'a LineMap,
    text: &'a str,
    /// Type parameters of the generic declaration being parsed.
    tparams: Vec<String>,
}

type PResult<T> = Result<T, Diagnostic>;

pub fn parse(
    tokens: &[Token],
    blocks: &[ProofBlock],
    lines: &LineMap,
    text: &str,
) -> PResult<Program> {
    let mut parser = Parser {
        tokens,
        pos: 0,
        blocks,
        consumed: vec![false; blocks.len()],
        lines,
        text,
        tparams: Vec::new(),
    };
    let mut fns = Vec::new();
    let mut classes = Vec::new();
    while !parser.at(&Tok::Eof) {
        if parser.at(&Tok::KwClass) {
            classes.push(parser.parse_class()?);
        } else {
            fns.push(parser.parse_fn()?);
        }
    }

    // Remaining blocks are module-level: ghost defs, theorems,
    // discharges, defers, assumes.
    let mut discharges = Vec::new();
    let mut ghosts = Vec::new();
    let mut defers = Vec::new();
    let mut assumes = Vec::new();
    for (bi, block) in parser.blocks.iter().enumerate() {
        if parser.consumed[bi] {
            continue;
        }
        for clause in &block.clauses {
            match clause.kind {
                ClauseKind::Discharge => discharges.push(parse_discharge(clause)?),
                ClauseKind::Defer => defers.push(parse_defer(clause)?),
                ClauseKind::Assume => assumes.push(parse_assume(clause)?),
                ClauseKind::GhostDef => ghosts.push(GhostItem {
                    keyword: "def",
                    text: clause.text.clone(),
                    span: clause.span,
                }),
                ClauseKind::Theorem => ghosts.push(GhostItem {
                    keyword: "theorem",
                    text: clause.text.clone(),
                    span: clause.span,
                }),
                other => {
                    return Err(Diagnostic {
                        name: "proof.unattached_block".into(),
                        title: format!(
                            "`{}` clause in a free-floating proof block",
                            kind_word(other)
                        ),
                        span: clause.line_span,
                        label: "module-level blocks hold `def`, `theorem`, and `discharge`"
                            .into(),
                        notes: vec![(
                            "note".into(),
                            "a blank line detaches a proof block from the item below — \
                             contracts must touch their function"
                                .into(),
                        )],
                    })
                }
            }
        }
    }

    Ok(Program {
        fns,
        classes,
        discharges,
        ghosts,
        defers,
        assumes,
    })
}

fn obligation_name(text: &str) -> (String, &str) {
    let text = text.trim_start();
    let name: String = text
        .chars()
        .take_while(|c| c.is_ascii_alphanumeric() || *c == '.' || *c == '_' || *c == ':')
        .collect();
    let rest = text[name.len()..].trim();
    (name, rest)
}

fn parse_defer(clause: &Clause) -> PResult<Defer> {
    let (name, rest) = obligation_name(&clause.text);
    if name.is_empty() || !rest.is_empty() {
        return Err(Diagnostic {
            name: "proof.malformed_defer".into(),
            title: "malformed `defer` clause".into(),
            span: clause.span,
            label: "expected `defer <obligation-name>`".into(),
            notes: vec![],
        });
    }
    Ok(Defer {
        name,
        span: clause.span,
    })
}

fn parse_assume(clause: &Clause) -> PResult<Assume> {
    // `#[audit(reason := "...")] NAME` — the audit payload is mandatory:
    // an assume is a permanent, reviewed trust statement (design §9).
    let text = clause.text.trim_start();
    let missing_audit = || Diagnostic {
        name: "proof.assume_needs_audit".into(),
        title: "`assume` without an `#[audit]` payload".into(),
        span: clause.span,
        label: "an axiom must carry its justification".into(),
        notes: vec![(
            "note".into(),
            "write `assume #[audit(reason := \"...\")] <obligation-name>` (design §9)".into(),
        )],
    };
    let Some(rest) = text.strip_prefix("#[audit(reason") else {
        return Err(missing_audit());
    };
    let rest = rest.trim_start();
    let Some(rest) = rest.strip_prefix(":=") else {
        return Err(missing_audit());
    };
    let rest = rest.trim_start();
    let Some(rest) = rest.strip_prefix('"') else {
        return Err(missing_audit());
    };
    let Some(quote_end) = rest.find('"') else {
        return Err(missing_audit());
    };
    let reason = rest[..quote_end].to_string();
    let rest = rest[quote_end + 1..].trim_start();
    let Some(rest) = rest.strip_prefix(")]") else {
        return Err(missing_audit());
    };
    let (name, tail) = obligation_name(rest);
    if name.is_empty() || !tail.is_empty() || reason.trim().is_empty() {
        return Err(Diagnostic {
            name: "proof.malformed_assume".into(),
            title: "malformed `assume` clause".into(),
            span: clause.span,
            label: "expected `assume #[audit(reason := \"...\")] <obligation-name>`".into(),
            notes: vec![],
        });
    }
    Ok(Assume {
        name,
        reason,
        span: clause.span,
    })
}

fn parse_discharge(clause: &Clause) -> PResult<Discharge> {
    // Clause text: `NAME by\n  <script>` (the keyword `discharge` is
    // already stripped by the scanner).
    let text = clause.text.trim_start();
    let name: String = text
        .chars()
        .take_while(|c| c.is_ascii_alphanumeric() || *c == '.' || *c == '_' || *c == ':')
        .collect();
    let rest = text[name.len()..].trim_start();
    let malformed = || Diagnostic {
        name: "proof.malformed_discharge".into(),
        title: "malformed `discharge` clause".into(),
        span: clause.span,
        label: "expected `discharge <obligation-name> by <tactics>`".into(),
        notes: vec![],
    };
    if name.is_empty() || !rest.starts_with("by") {
        return Err(malformed());
    }
    // Dedent by the common leading indent so the emitter's uniform
    // re-indent preserves nesting.
    let raw = &rest["by".len()..];
    let lines: Vec<&str> = raw
        .lines()
        .skip_while(|l| l.trim().is_empty())
        .collect();
    let min_indent = lines
        .iter()
        .filter(|l| !l.trim().is_empty())
        .map(|l| l.len() - l.trim_start().len())
        .min()
        .unwrap_or(0);
    let script = lines
        .iter()
        .map(|l| if l.len() >= min_indent { &l[min_indent..] } else { l.trim_end() })
        .collect::<Vec<_>>()
        .join("
")
        .trim_end()
        .to_string();
    if script.is_empty() {
        return Err(malformed());
    }
    Ok(Discharge {
        name,
        script,
        span: clause.span,
    })
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
        ClauseKind::Other => "<continuation>",
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
    fn peek_line(&self) -> usize {
        self.lines.line_col(self.peek_span().start).0
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

    /// The proof block whose last line immediately precedes `line`, if any.
    fn take_block_ending_before(&mut self, line: usize) -> Option<&'a ProofBlock> {
        for (bi, block) in self.blocks.iter().enumerate() {
            if !self.consumed[bi] && block.last_line + 1 == line {
                self.consumed[bi] = true;
                return Some(block);
            }
        }
        None
    }

    /// Disambiguate `f<i32>(...)` / `C<i32>::...` from comparisons:
    /// only a `<`-list of type names closed by `>` and followed by `(`
    /// or `::` parses as type arguments.
    fn at_generic_args(&self) -> bool {
        // Builtin angle-bracket forms have dedicated arms.
        if matches!(self.peek(), Tok::Ident(n) if n == "widen" || n == "alloc_array") {
            return false;
        }
        let mut i = self.pos + 1;
        if self.tokens.get(i).map(|t| &t.tok) != Some(&Tok::Lt) {
            return false;
        }
        i += 1;
        loop {
            match self.tokens.get(i).map(|t| &t.tok) {
                Some(Tok::Ident(n))
                    if IntTy::from_name(n).is_some()
                        || self.tparams.iter().any(|p| p == n) => {}
                _ => return false,
            }
            i += 1;
            match self.tokens.get(i).map(|t| &t.tok) {
                Some(Tok::Comma) => i += 1,
                Some(Tok::Gt) => {
                    i += 1;
                    break;
                }
                _ => return false,
            }
        }
        matches!(
            self.tokens.get(i).map(|t| &t.tok),
            Some(Tok::LParen) | Some(Tok::ColonColon)
        )
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

    fn int_ty(&mut self) -> PResult<(IntTy, Span)> {
        let (name, span) = self.ident()?;
        if let Some(i) = self.tparams.iter().position(|p| *p == name) {
            return Ok((IntTy::TParam(i as u8), span));
        }
        IntTy::from_name(&name).map(|t| (t, span)).ok_or_else(|| Diagnostic {
            name: "parse.unknown_type".into(),
            title: format!("unknown integer type `{name}`"),
            span,
            label: "expected `u8`..`u64`, `i8`..`i64`, or an in-scope type parameter"
                .into(),
            notes: vec![],
        })
    }

    /// `<T, U>` after a declaration name.
    fn type_param_list(&mut self) -> PResult<Vec<String>> {
        if !self.at(&Tok::Lt) {
            return Ok(Vec::new());
        }
        self.bump();
        let mut out = Vec::new();
        loop {
            let (name, span) = self.ident()?;
            if IntTy::from_name(&name).is_some() || is_reserved_name(&name) {
                return Err(Diagnostic {
                    name: "parse.bad_type_param".into(),
                    title: format!("`{name}` cannot be a type parameter"),
                    span,
                    label: "shadows a concrete type or reserved name".into(),
                    notes: vec![],
                });
            }
            out.push(name);
            if self.at(&Tok::Comma) {
                self.bump();
            } else {
                break;
            }
        }
        self.expect(Tok::Gt)?;
        Ok(out)
    }

    /// `<i32, u8>` at a use site (concrete or in-scope-parameter types).
    fn type_arg_list(&mut self) -> PResult<Vec<IntTy>> {
        self.expect(Tok::Lt)?;
        let mut out = Vec::new();
        loop {
            let (t, _) = self.int_ty()?;
            out.push(t);
            if self.at(&Tok::Comma) {
                self.bump();
            } else {
                break;
            }
        }
        self.expect(Tok::Gt)?;
        Ok(out)
    }

    /// A parameter type: scalar, `&[T]`, or `&mut [T]`.
    fn param_ty(&mut self) -> PResult<(Ty, Span)> {
        if self.at(&Tok::Amp) {
            let start = self.bump().span;
            let mutability = if matches!(self.peek(), Tok::Ident(m) if m == "mut") {
                self.bump();
                Mutability::Mut
            } else {
                Mutability::Shared
            };
            self.expect(Tok::LBracket)?;
            let (elem, _) = self.int_ty()?;
            let end = self.expect(Tok::RBracket)?.span;
            return Ok((Ty::Array(elem, mutability), start.join(end)));
        }
        self.scalar_ty()
    }

    fn scalar_ty(&mut self) -> PResult<(Ty, Span)> {
        let (name, span) = self.ident()?;
        if name == "bool" {
            return Ok((Ty::Bool, span));
        }
        if let Some(i) = self.tparams.iter().position(|p| *p == name) {
            return Ok((Ty::Int(IntTy::TParam(i as u8)), span));
        }
        IntTy::from_name(&name)
            .map(|t| (Ty::Int(t), span))
            .ok_or_else(|| Diagnostic {
                name: "parse.unknown_type".into(),
                title: format!("unknown type `{name}`"),
                span,
                label: "expected `u8`..`u64`, `i8`..`i64`, or `bool`".into(),
                notes: vec![],
            })
    }

    /// A return type: scalar or `option<T>`.
    fn ret_ty(&mut self) -> PResult<Ty> {
        if let Tok::Ident(name) = self.peek() {
            if name == "option" {
                self.bump();
                self.expect(Tok::Lt)?;
                let (elem, _) = self.int_ty()?;
                self.expect(Tok::Gt)?;
                return Ok(Ty::Option(elem));
            }
        }
        Ok(self.scalar_ty()?.0)
    }

    /// `class Name { fields... /// invariant ... init ... fn ... deinit }`
    /// (design §7). Blocks immediately preceding an init/method are its
    /// contract; remaining blocks inside the body are the class invariant.
    fn parse_class(&mut self) -> PResult<ClassDecl> {
        let start = self.expect(Tok::KwClass)?.span;
        let (name, name_span) = self.ident()?;
        self.tparams = self.type_param_list()?;
        let type_params = self.tparams.clone();
        self.expect(Tok::LBrace)?;
        let mut fields = Vec::new();
        let mut inits = Vec::new();
        let mut methods = Vec::new();
        let mut deinit = None;
        let body_first_line = self.peek_line();

        while !self.at(&Tok::RBrace) {
            if self.at(&Tok::Eof) {
                return Err(self.error_expected("`}`"));
            }
            let item_line = self.peek_line();
            match self.peek().clone() {
                Tok::KwInit => {
                    let mut f = self.parse_init()?;
                    self.attach_member_contract(item_line, &mut f, "an `init`")?;
                    inits.push(f);
                }
                Tok::KwFn => {
                    let mut m = self.parse_method()?;
                    self.attach_member_contract(item_line, &mut m.f, "a method")?;
                    methods.push(m);
                }
                Tok::KwDeinit => {
                    self.bump();
                    if deinit.replace(self.block()?).is_some() {
                        return Err(Diagnostic {
                            name: "parse.duplicate_deinit".into(),
                            title: "a class has at most one `deinit`".into(),
                            span: self.peek_span(),
                            label: "second `deinit`".into(),
                            notes: vec![],
                        });
                    }
                }
                Tok::LBracket => {
                    self.bump();
                    let (elem, _) = self.int_ty()?;
                    self.expect(Tok::RBracket)?;
                    let (fname, fspan) = self.ident()?;
                    self.expect(Tok::Semi)?;
                    fields.push(Field {
                        name: fname,
                        ty: Ty::Array(elem, Mutability::Owned),
                        span: fspan,
                    });
                }
                Tok::Ident(_) => {
                    let (ty, _) = self.scalar_ty()?;
                    let (fname, fspan) = self.ident()?;
                    self.expect(Tok::Semi)?;
                    fields.push(Field {
                        name: fname,
                        ty,
                        span: fspan,
                    });
                }
                _ => return Err(self.error_expected("a field, `init`, `fn`, or `deinit`")),
            }
        }
        let end = self.expect(Tok::RBrace)?.span;
        let body_last_line = self.lines.line_col(end.start).0;

        // Remaining blocks inside the body are the class invariant.
        let mut invariants = Vec::new();
        for (bi, block) in self.blocks.iter().enumerate() {
            if self.consumed[bi]
                || block.first_line < body_first_line
                || block.last_line > body_last_line
            {
                continue;
            }
            self.consumed[bi] = true;
            for clause in &block.clauses {
                if clause.kind == ClauseKind::Invariant {
                    invariants.push(clause.clone());
                } else {
                    return Err(bad_clause(
                        clause.kind,
                        clause,
                        "a class body",
                        "free blocks inside a class hold only `invariant` clauses",
                    ));
                }
            }
        }

        self.tparams.clear();
        Ok(ClassDecl {
            name,
            name_span,
            type_params,
            fields,
            invariants,
            inits,
            methods,
            deinit,
            span: start.join(end),
        })
    }

    fn attach_member_contract(
        &mut self,
        item_line: usize,
        f: &mut Fn,
        what: &str,
    ) -> PResult<()> {
        if let Some(block) = self.take_block_ending_before(item_line) {
            for clause in &block.clauses {
                match clause.kind {
                    ClauseKind::Pre => f.pres.push(clause.clone()),
                    ClauseKind::Post => f.posts.push(clause.clone()),
                    other => {
                        return Err(bad_clause(
                            other,
                            clause,
                            "a class-member contract block",
                            "only `pre` and `post` may precede an init or method",
                        ))
                    }
                }
            }
        }
        let _ = what;
        Ok(())
    }

    /// `init name(params) { ... }` — a named constructor (Unit-"returning").
    fn parse_init(&mut self) -> PResult<Fn> {
        let start = self.expect(Tok::KwInit)?.span;
        let (name, name_span) = self.ident()?;
        self.expect(Tok::LParen)?;
        let params = self.param_list()?;
        self.expect(Tok::RParen)?;
        let body = self.block()?;
        let end = self.tokens[self.pos.saturating_sub(1)].span;
        Ok(Fn {
            name,
            name_span,
            type_params: Vec::new(),
            params,
            ret: Ty::Unit,
            pres: Vec::new(),
            posts: Vec::new(),
            variant: None,
            body,
            span: start.join(end),
        })
    }

    /// `fn name(&mut self, params) -> ty { ... }`
    fn parse_method(&mut self) -> PResult<Method> {
        let start = self.expect(Tok::KwFn)?.span;
        let (name, name_span) = self.ident()?;
        self.expect(Tok::LParen)?;
        self.expect(Tok::Amp)?;
        let self_kind = if matches!(self.peek(), Tok::Ident(m) if m == "mut") {
            self.bump();
            SelfKind::Mut
        } else {
            SelfKind::Shared
        };
        match self.bump().tok {
            Tok::Ident(w) if w == "self" => {}
            _ => return Err(self.error_expected("`self`")),
        }
        let params = if self.at(&Tok::Comma) {
            self.bump();
            self.param_list()?
        } else {
            Vec::new()
        };
        self.expect(Tok::RParen)?;
        let ret = if self.at(&Tok::Arrow) {
            self.bump();
            self.ret_ty()?
        } else {
            Ty::Unit
        };
        let body = self.block()?;
        let end = self.tokens[self.pos.saturating_sub(1)].span;
        Ok(Method {
            self_kind,
            f: Fn {
                name,
                name_span,
                type_params: Vec::new(),
                params,
                ret,
                pres: Vec::new(),
                posts: Vec::new(),
                variant: None,
                body,
                span: start.join(end),
            },
        })
    }

    fn param_list(&mut self) -> PResult<Vec<Param>> {
        let mut params = Vec::new();
        if matches!(self.peek(), Tok::RParen) {
            return Ok(params);
        }
        loop {
            let (ty, tspan) = self.param_ty()?;
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
        Ok(params)
    }

    fn parse_fn(&mut self) -> PResult<Fn> {
        let fn_line = self.peek_line();
        let start = self.expect(Tok::KwFn)?.span;
        let (name, name_span) = self.ident()?;
        if is_reserved_name(&name) {
            return Err(reserved_name_error(&name, name_span, "function"));
        }
        self.tparams = self.type_param_list()?;
        let type_params = self.tparams.clone();
        self.expect(Tok::LParen)?;
        let mut params = Vec::new();
        if !self.at(&Tok::RParen) {
            loop {
                let (ty, tspan) = self.param_ty()?;
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
        let ret = if self.at(&Tok::Arrow) {
            self.bump();
            self.ret_ty()?
        } else {
            Ty::Unit
        };

        let mut f = Fn {
            name,
            name_span,
            type_params,
            params,
            ret,
            pres: Vec::new(),
            posts: Vec::new(),
            variant: None,
            body: Vec::new(),
            span: start,
        };

        // Contract block above `fn`.
        if let Some(block) = self.take_block_ending_before(fn_line) {
            for clause in &block.clauses {
                match clause.kind {
                    ClauseKind::Pre => f.pres.push(clause.clone()),
                    ClauseKind::Post => f.posts.push(clause.clone()),
                    ClauseKind::Variant => set_fn_variant(&mut f, clause)?,
                    other => return Err(bad_clause(other, clause, "a function contract block",
                        "only `pre`, `post`, and `variant` may precede a function")),
                }
            }
        }
        // Post-signature block (design §8: `fn gcd(...) -> u64` / `/// variant b` / `{`).
        let brace_line = self.peek_line();
        if !self.at(&Tok::LBrace) {
            return Err(self.error_expected("`{`"));
        }
        if let Some(block) = self.take_block_ending_before(brace_line) {
            for clause in &block.clauses {
                match clause.kind {
                    ClauseKind::Variant => set_fn_variant(&mut f, clause)?,
                    other => return Err(bad_clause(other, clause, "the post-signature position",
                        "only `variant` may sit between a signature and its body")),
                }
            }
        }

        f.body = self.block()?;
        self.tparams.clear();
        let end = self.tokens[self.pos.saturating_sub(1)].span;
        f.span = start.join(end);
        Ok(f)
    }

    fn block(&mut self) -> PResult<Vec<Stmt>> {
        self.expect(Tok::LBrace)?;
        let mut stmts = Vec::new();
        while !self.at(&Tok::RBrace) {
            if self.at(&Tok::Eof) {
                return Err(self.error_expected("`}`"));
            }
            if self.at(&Tok::KwFor) {
                stmts.extend(self.for_stmt()?);
            } else {
                stmts.push(self.stmt()?);
            }
        }
        self.expect(Tok::RBrace)?;
        Ok(stmts)
    }

    /// `for (T i : range(hi))` / `for (T i : range(lo, hi))` — pure sugar,
    /// desugared here to a declaration plus a `while` whose bounds
    /// invariant, variant, and increment are synthesized from the bounds'
    /// source text. Extra user `invariant`s above the `for` are kept; a
    /// user `variant` is rejected (the sugar provides it).
    fn for_stmt(&mut self) -> PResult<Vec<Stmt>> {
        let for_line = self.peek_line();
        let kw_span = self.expect(Tok::KwFor)?.span;

        let mut user_invariants = Vec::new();
        if let Some(block) = self.take_block_ending_before(for_line) {
            for clause in &block.clauses {
                match clause.kind {
                    ClauseKind::Invariant => user_invariants.push(clause.clone()),
                    ClauseKind::Variant => {
                        return Err(Diagnostic {
                            name: "proof.for_variant".into(),
                            title: "`for` loops provide their own `variant`".into(),
                            span: clause.line_span,
                            label: "remove this clause (the range bound is the measure)".into(),
                            notes: vec![],
                        })
                    }
                    other => {
                        return Err(bad_clause(
                            other,
                            clause,
                            "a loop annotation block",
                            "only `invariant` may precede a `for` loop",
                        ))
                    }
                }
            }
        }

        self.expect(Tok::LParen)?;
        let (ity, _) = self.int_ty()?;
        let (index, index_span) = self.ident()?;
        if is_reserved_name(&index) {
            return Err(reserved_name_error(&index, index_span, "loop index"));
        }
        self.expect(Tok::Colon)?;
        let (range_word, range_span) = self.ident()?;
        if range_word != "range" {
            return Err(Diagnostic {
                name: "parse.expected_range".into(),
                title: format!("expected `range`, found `{range_word}`"),
                span: range_span,
                label: "`for` iterates over `range(hi)` or `range(lo, hi)`".into(),
                notes: vec![],
            });
        }
        self.expect(Tok::LParen)?;
        let first_bound = self.expr()?;
        let (lo_expr, hi_expr) = if self.at(&Tok::Comma) {
            self.bump();
            let hi = self.expr()?;
            (Some(first_bound), hi)
        } else {
            (None, first_bound)
        };
        self.expect(Tok::RParen)?;
        self.expect(Tok::RParen)?;
        let body = self.block()?;

        // The synthesized invariant refers to the bounds by their source
        // text, so neither the index nor the bounds' variables may be
        // assigned by the body.
        let mut assigned = std::collections::HashSet::new();
        crate::vcgen::collect_assigned(&body, &mut assigned);
        if assigned.contains(&index) {
            return Err(Diagnostic {
                name: "parse.for_assigns_index".into(),
                title: format!("`for` body assigns the loop index `{index}`"),
                span: index_span,
                label: "the index is advanced by the loop itself".into(),
                notes: vec![],
            });
        }
        let mut bound_vars = std::collections::HashSet::new();
        expr_vars(&hi_expr, &mut bound_vars);
        if let Some(lo) = &lo_expr {
            expr_vars(lo, &mut bound_vars);
        }
        if let Some(clash) = bound_vars.iter().find(|v| assigned.contains(v.as_str())) {
            return Err(Diagnostic {
                name: "parse.for_mutates_bound".into(),
                title: format!("`for` body assigns `{clash}`, which the range bound mentions"),
                span: kw_span,
                label: "range bounds must be loop-invariant".into(),
                notes: vec![],
            });
        }

        let lo_src = lo_expr
            .as_ref()
            .map(|e| self.text[e.span.start..e.span.end].to_string())
            .unwrap_or_else(|| "0".to_string());
        let hi_src = self.text[hi_expr.span.start..hi_expr.span.end].to_string();
        let hi_span = hi_expr.span;

        let synth_clause = |text: String, kind: ClauseKind| Clause {
            kind,
            text,
            span: hi_span,
            line_span: kw_span.join(hi_span),
        };
        let mut invariants = vec![synth_clause(
            format!("({lo_src}) ≤ {index} ∧ {index} ≤ ({hi_src})"),
            ClauseKind::Invariant,
        )];
        invariants.extend(user_invariants);
        let variant = synth_clause(format!("({hi_src}) - {index}"), ClauseKind::Variant);

        let var = |name: &str| Expr {
            kind: ExprKind::Var(name.to_string()),
            span: index_span,
            ty: None,
        };
        let init = lo_expr.unwrap_or(Expr {
            kind: ExprKind::IntLit(0),
            span: kw_span,
            ty: None,
        });
        let cond = Expr {
            kind: ExprKind::Binary {
                op: BinOp::Lt,
                op_span: kw_span,
                lhs: Box::new(var(&index)),
                rhs: Box::new(hi_expr),
            },
            span: kw_span.join(hi_span),
            ty: None,
        };
        let increment = Stmt::Assign {
            name: index.clone(),
            name_span: index_span,
            value: Expr {
                kind: ExprKind::Binary {
                    op: BinOp::Add,
                    op_span: kw_span,
                    lhs: Box::new(var(&index)),
                    rhs: Box::new(Expr {
                        kind: ExprKind::IntLit(1),
                        span: kw_span,
                        ty: None,
                    }),
                },
                span: kw_span,
                ty: None,
            },
        };
        let mut while_body = body;
        while_body.push(increment);

        Ok(vec![
            Stmt::Decl {
                ty: Ty::Int(ity),
                name: index,
                name_span: index_span,
                init: Some(init),
            },
            Stmt::While {
                cond,
                invariants,
                variant: Some(variant),
                kw_span,
                body: while_body,
            },
        ])
    }

    fn stmt(&mut self) -> PResult<Stmt> {
        match self.peek().clone() {
            Tok::KwReturn => {
                let kw = self.bump().span;
                let value = if self.at(&Tok::Semi) {
                    None
                } else {
                    Some(self.expr()?)
                };
                let end = self.expect(Tok::Semi)?.span;
                Ok(Stmt::Return {
                    value,
                    span: kw.join(end),
                })
            }
            Tok::KwIf => self.if_stmt(),
            Tok::KwWhile => self.while_stmt(),
            Tok::KwVar => {
                self.bump();
                let (name, name_span) = self.ident()?;
                if is_reserved_name(&name) {
                    return Err(reserved_name_error(&name, name_span, "variable"));
                }
                self.expect(Tok::Assign)?;
                let init = self.expr()?;
                self.expect(Tok::Semi)?;
                Ok(Stmt::VarDecl {
                    name,
                    name_span,
                    init,
                    ty: None,
                })
            }
            Tok::LBracket => {
                // `[i32] a = [1, 2, 3];` — owned array local (tests only;
                // the checker enforces the context).
                self.bump();
                let (elem, _) = self.int_ty()?;
                self.expect(Tok::RBracket)?;
                let (name, name_span) = self.ident()?;
                if is_reserved_name(&name) {
                    return Err(reserved_name_error(&name, name_span, "variable"));
                }
                self.expect(Tok::Assign)?;
                let init = self.expr()?;
                self.expect(Tok::Semi)?;
                Ok(Stmt::Decl {
                    ty: Ty::Array(elem, Mutability::Owned),
                    name,
                    name_span,
                    init: Some(init),
                })
            }
            Tok::Ident(first) if first == "self" && self.peek2() == &Tok::Dot => {
                // self.f = e;   self.f[i] = e;
                self.bump();
                self.bump();
                let (field, field_span) = self.ident()?;
                if self.at(&Tok::LBracket) {
                    self.bump();
                    let index = self.expr()?;
                    self.expect(Tok::RBracket)?;
                    self.expect(Tok::Assign)?;
                    let value = self.expr()?;
                    self.expect(Tok::Semi)?;
                    return Ok(Stmt::FieldStore {
                        field,
                        field_span,
                        index,
                        value,
                    });
                }
                self.expect(Tok::Assign)?;
                let value = self.expr()?;
                self.expect(Tok::Semi)?;
                Ok(Stmt::FieldAssign {
                    field,
                    field_span,
                    value,
                })
            }
            Tok::Ident(_) if self.peek2() == &Tok::Dot => {
                // Method-call statement: `s.push(7);`
                let e = self.expr()?;
                if !matches!(e.kind, ExprKind::MethodCall { .. }) {
                    return Err(Diagnostic {
                        name: "parse.expr_stmt".into(),
                        title: "only calls can be used as statements".into(),
                        span: e.span,
                        label: "this expression has no effect".into(),
                        notes: vec![],
                    });
                }
                self.expect(Tok::Semi)?;
                Ok(Stmt::ExprStmt(e))
            }
            Tok::Ident(first) => {
                if let Tok::Ident(_) = self.peek2() {
                    let (ty, _) = self.scalar_ty()?;
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
                } else if self.peek2() == &Tok::LParen {
                    let e = self.expr()?;
                    self.expect(Tok::Semi)?;
                    Ok(Stmt::ExprStmt(e))
                } else if self.peek2() == &Tok::LBracket {
                    let array_span = self.peek_span();
                    self.bump();
                    self.bump();
                    let index = self.expr()?;
                    self.expect(Tok::RBracket)?;
                    self.expect(Tok::Assign)?;
                    let value = self.expr()?;
                    self.expect(Tok::Semi)?;
                    Ok(Stmt::Store {
                        array: first,
                        array_span,
                        index,
                        value,
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

    fn while_stmt(&mut self) -> PResult<Stmt> {
        let while_line = self.peek_line();
        let kw_span = self.expect(Tok::KwWhile)?.span;
        let mut invariants = Vec::new();
        let mut variant = None;
        if let Some(block) = self.take_block_ending_before(while_line) {
            for clause in &block.clauses {
                match clause.kind {
                    ClauseKind::Invariant => invariants.push(clause.clone()),
                    ClauseKind::Variant => {
                        if variant.replace(clause.clone()).is_some() {
                            return Err(Diagnostic {
                                name: "proof.duplicate_variant".into(),
                                title: "a loop has exactly one `variant`".into(),
                                span: clause.line_span,
                                label: "second `variant` clause".into(),
                                notes: vec![],
                            });
                        }
                    }
                    other => return Err(bad_clause(other, clause, "a loop annotation block",
                        "only `invariant` and `variant` may precede a loop")),
                }
            }
        }
        self.expect(Tok::LParen)?;
        let cond = self.expr()?;
        self.expect(Tok::RParen)?;
        let body = self.block()?;
        Ok(Stmt::While {
            cond,
            invariants,
            variant,
            kw_span,
            body,
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
        let mut e = self.primary_expr()?;
        loop {
            match self.peek() {
                Tok::LParen => {
                    let ExprKind::Var(name) = &e.kind else {
                        return Err(Diagnostic {
                            name: "parse.bad_call".into(),
                            title: "only named functions can be called".into(),
                            span: self.peek_span(),
                            label: "call target must be a function name".into(),
                            notes: vec![],
                        });
                    };
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
                    e = Expr {
                        kind: ExprKind::Call {
                            callee,
                            callee_span,
                            type_args: Vec::new(),
                            args,
                        },
                        span: callee_span.join(close),
                        ty: None,
                    };
                }
                Tok::LBracket => {
                    let ExprKind::Var(name) = &e.kind else {
                        return Err(Diagnostic {
                            name: "parse.bad_index".into(),
                            title: "only named arrays can be indexed".into(),
                            span: self.peek_span(),
                            label: "indexing applies to array parameters in M1".into(),
                            notes: vec![],
                        });
                    };
                    let array = name.clone();
                    let array_span = e.span;
                    self.bump();
                    let index = self.expr()?;
                    let close = self.expect(Tok::RBracket)?.span;
                    e = Expr {
                        kind: ExprKind::Index {
                            array,
                            array_span,
                            index: Box::new(index),
                        },
                        span: array_span.join(close),
                        ty: None,
                    };
                }
                Tok::Dot => {
                    let ExprKind::Var(name) = &e.kind else {
                        return Err(self.error_expected("nothing (`.` applies to names)"));
                    };
                    let recv = name.clone();
                    let recv_span = e.span;
                    self.bump();
                    let (field, fspan) = self.ident()?;
                    if self.at(&Tok::LParen) {
                        // recv.method(args)
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
                        e = Expr {
                            kind: ExprKind::MethodCall {
                                recv,
                                recv_span,
                                method: field,
                                method_span: fspan,
                                args,
                            },
                            span: recv_span.join(close),
                            ty: None,
                        };
                        continue;
                    }
                    if field != "len" {
                        return Err(Diagnostic {
                            name: "parse.unknown_field".into(),
                            title: format!("unknown field `.{field}`"),
                            span: fspan,
                            label: "`.len` (arrays) and `.method(...)` are the accessors".into(),
                            notes: vec![],
                        });
                    }
                    e = Expr {
                        kind: ExprKind::Len { array: recv },
                        span: recv_span.join(fspan),
                        ty: None,
                    };
                }
                _ => break,
            }
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
            Tok::Ident(name) if name == "alloc_array" => {
                self.bump();
                self.expect(Tok::Lt)?;
                let (elem, _) = self.int_ty()?;
                self.expect(Tok::Gt)?;
                self.expect(Tok::LParen)?;
                let len = self.expr()?;
                self.expect(Tok::Comma)?;
                let init = self.expr()?;
                let close = self.expect(Tok::RParen)?.span;
                Ok(Expr {
                    kind: ExprKind::AllocArray {
                        elem,
                        len: Box::new(len),
                        init: Box::new(init),
                    },
                    span: span.join(close),
                    ty: None,
                })
            }
            Tok::Ident(name) if name == "self" && self.peek2() == &Tok::Dot => {
                self.bump();
                self.bump();
                let (field, fspan) = self.ident()?;
                if self.at(&Tok::LBracket) {
                    self.bump();
                    let index = self.expr()?;
                    let close = self.expect(Tok::RBracket)?.span;
                    return Ok(Expr {
                        kind: ExprKind::SelfFieldIndex {
                            field,
                            index: Box::new(index),
                        },
                        span: span.join(close),
                        ty: None,
                    });
                }
                if self.at(&Tok::Dot) {
                    self.bump();
                    let (sub, sspan) = self.ident()?;
                    if sub != "len" {
                        return Err(Diagnostic {
                            name: "parse.unknown_field".into(),
                            title: format!("unknown field `.{sub}`"),
                            span: sspan,
                            label: "`.len` is the only array-field accessor".into(),
                            notes: vec![],
                        });
                    }
                    return Ok(Expr {
                        kind: ExprKind::SelfFieldLen { field },
                        span: span.join(sspan),
                        ty: None,
                    });
                }
                Ok(Expr {
                    kind: ExprKind::SelfField { field },
                    span: span.join(fspan),
                    ty: None,
                })
            }
            Tok::Ident(head) if self.at_generic_args() => {
                let head_span = self.peek_span();
                self.bump();
                let type_args = self.type_arg_list()?;
                if self.at(&Tok::ColonColon) {
                    self.bump();
                    let (init, _) = self.ident()?;
                    self.expect(Tok::LParen)?;
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
                        kind: ExprKind::CtorCall {
                            class: head,
                            class_span: head_span,
                            type_args,
                            init,
                            args,
                        },
                        span: span.join(close),
                        ty: None,
                    });
                }
                self.expect(Tok::LParen)?;
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
                Ok(Expr {
                    kind: ExprKind::Call {
                        callee: head,
                        callee_span: head_span,
                        type_args,
                        args,
                    },
                    span: span.join(close),
                    ty: None,
                })
            }
            Tok::Ident(class) if self.peek2() == &Tok::ColonColon => {
                let class_span = self.peek_span();
                self.bump();
                self.bump();
                let (init, _) = self.ident()?;
                self.expect(Tok::LParen)?;
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
                Ok(Expr {
                    kind: ExprKind::CtorCall {
                        class,
                        class_span,
                        type_args: Vec::new(),
                        init,
                        args,
                    },
                    span: span.join(close),
                    ty: None,
                })
            }
            Tok::Ident(name) if name == "widen" => {
                self.bump();
                self.expect(Tok::Lt)?;
                let (target, _) = self.int_ty()?;
                self.expect(Tok::Gt)?;
                self.expect(Tok::LParen)?;
                let arg = self.expr()?;
                let close = self.expect(Tok::RParen)?.span;
                Ok(Expr {
                    kind: ExprKind::Widen {
                        target,
                        arg: Box::new(arg),
                    },
                    span: span.join(close),
                    ty: None,
                })
            }
            Tok::Ident(name) if name == "some" => {
                self.bump();
                self.expect(Tok::LParen)?;
                let arg = self.expr()?;
                let close = self.expect(Tok::RParen)?.span;
                Ok(Expr {
                    kind: ExprKind::SomeE(Box::new(arg)),
                    span: span.join(close),
                    ty: None,
                })
            }
            Tok::Ident(name) if name == "none" => {
                self.bump();
                Ok(Expr {
                    kind: ExprKind::NoneE,
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
            Tok::LBracket => {
                self.bump();
                let mut elems = Vec::new();
                if !self.at(&Tok::RBracket) {
                    loop {
                        elems.push(self.expr()?);
                        if self.at(&Tok::Comma) {
                            self.bump();
                        } else {
                            break;
                        }
                    }
                }
                let close = self.expect(Tok::RBracket)?.span;
                Ok(Expr {
                    kind: ExprKind::ArrayLit(elems),
                    span: span.join(close),
                    ty: None,
                })
            }
            Tok::Amp => {
                self.bump();
                let mutable = if matches!(self.peek(), Tok::Ident(m) if m == "mut") {
                    self.bump();
                    true
                } else {
                    false
                };
                let (array, aspan) = self.ident()?;
                Ok(Expr {
                    kind: ExprKind::Borrow { array, mutable },
                    span: span.join(aspan),
                    ty: None,
                })
            }
            _ => Err(self.error_expected("an expression")),
        }
    }
}

fn set_fn_variant(f: &mut Fn, clause: &Clause) -> PResult<()> {
    if f.variant.replace(clause.clone()).is_some() {
        return Err(Diagnostic {
            name: "proof.duplicate_variant".into(),
            title: "a function has at most one `variant`".into(),
            span: clause.line_span,
            label: "second `variant` clause".into(),
            notes: vec![],
        });
    }
    Ok(())
}

fn bad_clause(
    kind: ClauseKind,
    clause: &Clause,
    where_: &str,
    rule: &str,
) -> Diagnostic {
    Diagnostic {
        name: "proof.bad_clause".into(),
        title: format!("`{}` clause in {where_}", kind_word(kind)),
        span: clause.line_span,
        label: rule.to_string(),
        notes: vec![(
            "note".into(),
            "statement-level `assert`/`defer`/`assume` land in M3; ghost \
             `def`/`theorem` land in M2; a continuation line must follow a clause"
                .into(),
        )],
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

/// Names that would collide with the proof language or generated Lean.
fn is_reserved_name(name: &str) -> bool {
    const RESERVED: &[&str] = &[
        "result", "old", "mut", "some", "none", "option", "widen", "theorem", "def", "by", "fun",
        "match", "with", "do", "let", "have", "show", "from", "open", "import", "namespace",
        "end", "in", "at", "forall", "exists", "Prop", "Type", "Int", "Nat", "Bool", "True",
        "False", "len",
    ];
    RESERVED.contains(&name)
        || IntTy::from_name(name).is_some()
        || name == "bool"
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
             with Lean keywords or Sable builtins are rejected"
                .into(),
        )],
    }
}

/// Free program identifiers of an expression (over-approximate: includes
/// array names and callees; used for `for`-bound stability checks).
fn expr_vars(e: &Expr, out: &mut std::collections::HashSet<String>) {
    match &e.kind {
        ExprKind::Var(n) => {
            out.insert(n.clone());
        }
        ExprKind::Index { array, index, .. } => {
            out.insert(array.clone());
            expr_vars(index, out);
        }
        ExprKind::Len { array } => {
            out.insert(array.clone());
        }
        ExprKind::Unary { operand, .. } => expr_vars(operand, out),
        ExprKind::Widen { arg, .. } => expr_vars(arg, out),
        ExprKind::SomeE(inner) => expr_vars(inner, out),
        ExprKind::Binary { lhs, rhs, .. } => {
            expr_vars(lhs, out);
            expr_vars(rhs, out);
        }
        ExprKind::Call { args, .. } => {
            for a in args {
                expr_vars(a, out);
            }
        }
        ExprKind::ArrayLit(elems) => {
            for el in elems {
                expr_vars(el, out);
            }
        }
        ExprKind::AllocArray { len, init, .. } => {
            expr_vars(len, out);
            expr_vars(init, out);
        }
        ExprKind::SelfField { .. } | ExprKind::SelfFieldLen { .. } => {
            out.insert("self".to_string());
        }
        ExprKind::SelfFieldIndex { index, .. } => {
            out.insert("self".to_string());
            expr_vars(index, out);
        }
        ExprKind::CtorCall { args, .. } => {
            for a in args {
                expr_vars(a, out);
            }
        }
        ExprKind::MethodCall { recv, args, .. } => {
            out.insert(recv.clone());
            for a in args {
                expr_vars(a, out);
            }
        }
        ExprKind::Borrow { array, .. } => {
            out.insert(array.clone());
        }
        ExprKind::IntLit(_) | ExprKind::BoolLit(_) | ExprKind::NoneE => {}
    }
}
