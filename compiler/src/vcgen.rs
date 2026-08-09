//! Verification-condition generation by forward symbolic execution.
//!
//! Program integer values are represented as Lean `Int` expression strings,
//! kept exact by per-operation obligations (overflow, divisor-nonzero).
//! Control flow is handled by path-splitting: `if` executes both arms
//! against the remaining statements with the branch condition (or its
//! negation) as a hypothesis. Sound and simple; fine at M0 scale.
//!
//! Contract clauses are spliced verbatim (CLAUDE.md invariant); the only
//! transformation ever applied is call-site substitution of callee
//! parameter names by parenthesized argument expressions.

use crate::ast::*;
use crate::check::FnSig;
use crate::span::Span;
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct Obligation {
    /// User-facing obligation name, e.g. `div_round_up.overflow.a_add_b`.
    pub name: String,
    /// Sanitized Lean theorem name.
    pub thm_name: String,
    /// Short description used as the caret label.
    pub kind_desc: String,
    /// Where to point in the .sable source.
    pub span: Span,
    /// Lean proposition to prove.
    pub goal: String,
    /// (name, "Int" | "Bool")
    pub binders: Vec<(String, &'static str)>,
    /// (hypothesis name, Lean proposition)
    pub hyps: Vec<(String, String)>,
    /// Human-readable summary of the context (pres, path conditions...).
    pub context: Vec<String>,
}

/// A `def ... : Prop` emitted per contract clause so that a clause that
/// fails to elaborate produces an error mapped exactly to its own span.
#[derive(Debug, Clone)]
pub struct ClauseWf {
    pub def_name: String,
    pub binders: Vec<(String, &'static str)>,
    pub text: String,
    pub span: Span,
    pub desc: String,
}

pub struct VcResult {
    pub clause_wfs: Vec<ClauseWf>,
    pub obligations: Vec<Obligation>,
}

pub fn generate(program: &Program, sigs: &HashMap<String, FnSig>, source: &str) -> VcResult {
    let fn_map: HashMap<&str, &Fn> = program.fns.iter().map(|f| (f.name.as_str(), f)).collect();
    let mut result = VcResult {
        clause_wfs: Vec::new(),
        obligations: Vec::new(),
    };
    for f in &program.fns {
        let mut generator = Generator {
            f,
            sigs,
            fn_map: &fn_map,
            source,
            binders: Vec::new(),
            hyps: Vec::new(),
            context: Vec::new(),
            env: HashMap::new(),
            fresh: 0,
            name_counts: HashMap::new(),
            out: &mut result,
        };
        generator.run();
    }
    result
}

#[derive(Debug, Clone)]
enum Val {
    /// Lean `Int` expression.
    Int(String),
    /// Lean proposition (bool-typed program values).
    Prop(String),
}

struct Generator<'a> {
    f: &'a Fn,
    sigs: &'a HashMap<String, FnSig>,
    fn_map: &'a HashMap<&'a str, &'a Fn>,
    source: &'a str,
    binders: Vec<(String, &'static str)>,
    hyps: Vec<(String, String)>,
    context: Vec<String>,
    env: HashMap<String, Val>,
    fresh: usize,
    name_counts: HashMap<String, usize>,
    out: &'a mut VcResult,
}

impl<'a> Generator<'a> {
    fn run(&mut self) {
        // Parameters become binders with range facts; bool params are
        // Bool binders used as `(p = true)` propositions.
        for p in &self.f.params {
            match p.ty {
                Ty::Int(it) => {
                    self.binders.push((p.name.clone(), "Int"));
                    self.hyps.push((
                        format!("h_{}_range", p.name),
                        range_prop(&p.name, it),
                    ));
                    self.env
                        .insert(p.name.clone(), Val::Int(p.name.clone()));
                }
                Ty::Bool => {
                    self.binders.push((p.name.clone(), "Bool"));
                    self.env
                        .insert(p.name.clone(), Val::Prop(format!("({} = true)", p.name)));
                }
            }
        }
        // Preconditions: hypotheses everywhere in the body, and a
        // well-formedness def each.
        for (i, pre) in self.f.pres.iter().enumerate() {
            self.hyps
                .push((format!("h_pre_{}", i + 1), format!("({})", pre.text)));
            self.context.push(format!("pre {}", pre.text));
            self.out.clause_wfs.push(ClauseWf {
                def_name: format!("wf_{}_pre_{}", sanitize(&self.f.name), i + 1),
                binders: self.binders.clone(),
                text: pre.text.clone(),
                span: pre.span,
                desc: format!("`pre` clause of `{}`", self.f.name),
            });
        }
        for (i, post) in self.f.posts.iter().enumerate() {
            let mut binders = self.binders.clone();
            binders.push(("result".to_string(), "Int"));
            self.out.clause_wfs.push(ClauseWf {
                def_name: format!("wf_{}_post_{}", sanitize(&self.f.name), i + 1),
                binders,
                text: post.text.clone(),
                span: post.span,
                desc: format!("`post` clause of `{}`", self.f.name),
            });
        }

        let stmts: Vec<&Stmt> = self.f.body.iter().collect();
        self.exec(&stmts);
    }

    /// Execute a statement list (continuation style: `if` re-enters with
    /// branch ++ rest).
    fn exec(&mut self, stmts: &[&'a Stmt]) {
        let Some((stmt, rest)) = stmts.split_first() else {
            return;
        };
        match stmt {
            Stmt::Decl { name, init, .. } => {
                if let Some(e) = init {
                    let v = self.eval(e);
                    self.env.insert(name.clone(), v);
                } else {
                    self.env.remove(name);
                }
                self.exec(rest);
            }
            Stmt::Assign { name, value, .. } => {
                let v = self.eval(value);
                self.env.insert(name.clone(), v);
                self.exec(rest);
            }
            Stmt::Return { value, .. } => {
                let v = self.eval(value);
                let Val::Int(ret) = v else {
                    unreachable!("bool returns rejected in M0");
                };
                for post in &self.f.posts {
                    let mut ob = self.obligation(
                        &format!("{}.post.{}", self.f.name, slug(&post.text)),
                        format!("postcondition of `{}`", self.f.name),
                        post.span,
                        post.text.clone(),
                    );
                    ob.binders.push(("result".to_string(), "Int"));
                    ob.hyps.push(("h_result".to_string(), format!("(result = {ret})")));
                    self.push_obligation(ob);
                }
                // Path ends; nothing after `return` executes.
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                let p = self.eval_prop(cond);
                let snap_env = self.env.clone();
                let snap_hyps = self.hyps.len();
                let snap_ctx = self.context.len();

                let h_then = self.fresh_hyp("h_path");
                self.hyps.push((h_then, p.clone()));
                self.context.push(format!("path {p}"));
                let then_stmts: Vec<&Stmt> =
                    then_block.iter().chain(rest.iter().copied()).collect();
                self.exec(&then_stmts);

                self.env = snap_env;
                self.hyps.truncate(snap_hyps);
                self.context.truncate(snap_ctx);

                let h_else = self.fresh_hyp("h_path");
                self.hyps.push((h_else, format!("¬{p}")));
                self.context.push(format!("path ¬{p}"));
                match else_block {
                    Some(eb) => {
                        let else_stmts: Vec<&Stmt> =
                            eb.iter().chain(rest.iter().copied()).collect();
                        self.exec(&else_stmts);
                    }
                    None => self.exec(rest),
                }
                self.hyps.truncate(snap_hyps);
                self.context.truncate(snap_ctx);
            }
        }
    }

    /// Evaluate an integer-typed expression to a Lean `Int` string,
    /// emitting obligations for every partial operation on the way.
    fn eval(&mut self, e: &Expr) -> Val {
        match &e.kind {
            ExprKind::IntLit(n) => Val::Int(if *n < 0 {
                format!("({n})")
            } else {
                format!("{n}")
            }),
            ExprKind::BoolLit(b) => Val::Prop(if *b { "True".into() } else { "False".into() }),
            ExprKind::Var(name) => self.env.get(name).cloned().expect("checked: initialized"),
            ExprKind::Unary { op, operand } => match op {
                UnOp::Neg => {
                    let Val::Int(v) = self.eval(operand) else {
                        unreachable!()
                    };
                    let value = format!("(-{v})");
                    let Ty::Int(it) = e.ty.unwrap() else {
                        unreachable!()
                    };
                    let ob = self.obligation(
                        &format!("{}.overflow.{}", self.f.name, slug(self.src(e.span))),
                        format!(
                            "result of `{}` must fit in `{}`",
                            self.src_short(e.span),
                            it.name()
                        ),
                        e.span,
                        range_prop(&value, it),
                    );
                    self.push_obligation(ob);
                    Val::Int(value)
                }
                UnOp::Not => {
                    let p = self.eval_prop(operand);
                    Val::Prop(format!("¬{p}"))
                }
            },
            ExprKind::Binary { op, lhs, rhs, .. } => {
                if op.is_arith() {
                    let Val::Int(l) = self.eval(lhs) else {
                        unreachable!()
                    };
                    let Val::Int(r) = self.eval(rhs) else {
                        unreachable!()
                    };
                    let lean_op = match op {
                        BinOp::Add => "+",
                        BinOp::Sub => "-",
                        BinOp::Mul => "*",
                        BinOp::Div => "/",
                        BinOp::Rem => "%",
                        _ => unreachable!(),
                    };
                    let value = format!("({l} {lean_op} {r})");
                    let Ty::Int(it) = e.ty.unwrap() else {
                        unreachable!()
                    };
                    match op {
                        BinOp::Add | BinOp::Sub | BinOp::Mul => {
                            let ob = self.obligation(
                                &format!(
                                    "{}.overflow.{}",
                                    self.f.name,
                                    slug(self.src(e.span))
                                ),
                                format!(
                                    "result of `{}` must fit in `{}`",
                                    self.src_short(e.span),
                                    it.name()
                                ),
                                e.span,
                                range_prop(&value, it),
                            );
                            self.push_obligation(ob);
                        }
                        BinOp::Div | BinOp::Rem => {
                            // Unsigned only in M0 (checked); Lean `/`/`%` on
                            // Int agree with C for nonneg operands, and the
                            // result stays in range without a further VC.
                            let ob = self.obligation(
                                &format!(
                                    "{}.div_zero.{}",
                                    self.f.name,
                                    slug(self.src(e.span))
                                ),
                                format!("divisor `{}` must be nonzero", self.src_short(rhs.span)),
                                rhs.span,
                                format!("{r} ≠ 0"),
                            );
                            self.push_obligation(ob);
                        }
                        _ => unreachable!(),
                    }
                    Val::Int(value)
                } else {
                    Val::Prop(self.eval_prop(e))
                }
            }
            ExprKind::Call { callee, args, .. } => {
                let arg_vals: Vec<String> = args
                    .iter()
                    .map(|a| {
                        let Val::Int(v) = self.eval(a) else {
                            unreachable!("bool args rejected in M0")
                        };
                        v
                    })
                    .collect();
                let callee_fn = self.fn_map[callee.as_str()];
                let sig = &self.sigs[callee.as_str()];
                let param_names: Vec<&str> =
                    sig.params.iter().map(|p| p.name.as_str()).collect();

                // Callee preconditions become obligations here.
                for pre in &callee_fn.pres {
                    let goal = substitute(&pre.text, &param_names, &arg_vals, None);
                    let ob = self.obligation(
                        &format!("{}.call_pre.{}.{}", self.f.name, callee, slug(&pre.text)),
                        format!("`pre {}` of `{callee}` must hold at this call", pre.text),
                        e.span,
                        goal,
                    );
                    self.push_obligation(ob);
                }

                // Fresh symbol for the returned value; callee postconditions
                // become hypotheses about it.
                self.fresh += 1;
                let ret_sym = format!("_r{}", self.fresh);
                self.binders.push((ret_sym.clone(), "Int"));
                let Ty::Int(ret_it) = sig.ret else {
                    unreachable!("bool returns rejected in M0")
                };
                self.hyps.push((
                    format!("h{ret_sym}_range"),
                    range_prop(&ret_sym, ret_it),
                ));
                for (i, post) in callee_fn.posts.iter().enumerate() {
                    let prop =
                        substitute(&post.text, &param_names, &arg_vals, Some(&ret_sym));
                    self.hyps
                        .push((format!("h{ret_sym}_post_{}", i + 1), format!("({prop})")));
                    self.context
                        .push(format!("from `{callee}` post: {}", post.text));
                }
                Val::Int(ret_sym)
            }
        }
    }

    /// Evaluate a bool-typed expression to a Lean proposition. `&&`/`||`
    /// guard their right operand's obligations with the left operand (or
    /// its negation), preserving short-circuit semantics for VCs.
    fn eval_prop(&mut self, e: &Expr) -> String {
        match &e.kind {
            ExprKind::BoolLit(b) => if *b { "True" } else { "False" }.to_string(),
            ExprKind::Var(_) => {
                let Val::Prop(p) = self.eval(e) else {
                    unreachable!()
                };
                p
            }
            ExprKind::Unary {
                op: UnOp::Not,
                operand,
            } => format!("¬{}", self.eval_prop(operand)),
            ExprKind::Binary { op, lhs, rhs, .. } if op.is_comparison() => {
                let Val::Int(l) = self.eval(lhs) else {
                    unreachable!()
                };
                let Val::Int(r) = self.eval(rhs) else {
                    unreachable!()
                };
                let sym = match op {
                    BinOp::Lt => "<",
                    BinOp::Le => "≤",
                    BinOp::Gt => ">",
                    BinOp::Ge => "≥",
                    BinOp::Eq => "=",
                    BinOp::Ne => "≠",
                    _ => unreachable!(),
                };
                format!("({l} {sym} {r})")
            }
            ExprKind::Binary {
                op: op @ (BinOp::And | BinOp::Or),
                lhs,
                rhs,
                ..
            } => {
                let pl = self.eval_prop(lhs);
                let guard = if *op == BinOp::And {
                    pl.clone()
                } else {
                    format!("¬{pl}")
                };
                let snap = self.hyps.len();
                let h_guard = self.fresh_hyp("h_guard");
                self.hyps.push((h_guard, guard));
                let pr = self.eval_prop(rhs);
                self.hyps.truncate(snap);
                let sym = if *op == BinOp::And { "∧" } else { "∨" };
                format!("({pl} {sym} {pr})")
            }
            _ => unreachable!("checked: bool-typed expression"),
        }
    }

    fn obligation(
        &mut self,
        name: &str,
        kind_desc: String,
        span: Span,
        goal: String,
    ) -> Obligation {
        let unique = self.unique_name(name);
        Obligation {
            thm_name: format!("vc_{}", sanitize(&unique)),
            name: unique,
            kind_desc,
            span,
            goal,
            binders: self.binders.clone(),
            hyps: self.hyps.clone(),
            context: self.context.clone(),
        }
    }

    fn push_obligation(&mut self, ob: Obligation) {
        self.out.obligations.push(ob);
    }

    fn unique_name(&mut self, base: &str) -> String {
        let n = self.name_counts.entry(base.to_string()).or_insert(0);
        *n += 1;
        if *n == 1 {
            base.to_string()
        } else {
            format!("{base}.{n}")
        }
    }

    fn fresh_hyp(&mut self, base: &str) -> String {
        self.fresh += 1;
        format!("{base}{}", self.fresh)
    }

    fn src(&self, span: Span) -> &str {
        &self.source[span.start..span.end]
    }

    fn src_short(&self, span: Span) -> String {
        let s = self.src(span);
        if s.len() > 40 {
            format!("{}...", &s[..37])
        } else {
            s.to_string()
        }
    }
}

fn range_prop(value: &str, it: IntTy) -> String {
    format!("{} ≤ {value} ∧ {value} ≤ {}", it.lean_min(), it.lean_max())
}

/// Replace callee parameter names (and `result`) in clause text with
/// parenthesized argument expressions. Identifier-boundary aware; skips
/// identifiers preceded by `.` (field/namespace access like `u32.max`).
fn substitute(
    text: &str,
    params: &[&str],
    args: &[String],
    result: Option<&str>,
) -> String {
    let mut out = String::with_capacity(text.len());
    let bytes = text.as_bytes();
    let mut i = 0;
    let mut prev_byte: Option<u8> = None;
    while i < bytes.len() {
        let b = bytes[i];
        if b.is_ascii_alphabetic() || b == b'_' {
            let start = i;
            while i < bytes.len()
                && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_' || bytes[i] == b'\'')
            {
                i += 1;
            }
            let word = &text[start..i];
            let after_dot = prev_byte == Some(b'.');
            let replacement = if after_dot {
                None
            } else if word == "result" {
                result.map(|r| r.to_string())
            } else {
                params
                    .iter()
                    .position(|p| *p == word)
                    .map(|idx| args[idx].clone())
            };
            match replacement {
                Some(r) => out.push_str(&format!("({r})")),
                None => out.push_str(word),
            }
            prev_byte = Some(bytes[i - 1]);
            continue;
        }
        out.push(b as char);
        prev_byte = Some(b);
        i += 1;
    }
    out
}

pub fn sanitize(name: &str) -> String {
    name.chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect()
}

pub fn slug(text: &str) -> String {
    let mut out = String::new();
    let mut last_underscore = true;
    for c in text.chars() {
        if c.is_ascii_alphanumeric() {
            out.push(c.to_ascii_lowercase());
            last_underscore = false;
        } else if !last_underscore {
            out.push('_');
            last_underscore = true;
        }
        if out.len() >= 40 {
            break;
        }
    }
    let out = out.trim_matches('_').to_string();
    if out.is_empty() {
        "e".to_string()
    } else {
        out
    }
}
