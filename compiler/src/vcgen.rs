//! Verification-condition generation by forward symbolic execution.
//!
//! Program integer values are Lean `Int` expression strings, kept exact by
//! per-operation obligations. Control flow: path-splitting at `if`;
//! `while` is handled by the standard havoc decomposition —
//!
//!   1. prove each invariant at loop entry (goal = invariant text with
//!      variables substituted by their current symbolic values);
//!   2. havoc every variable the body assigns (fresh binders under their
//!      *source names*, so invariant/variant clauses splice verbatim as
//!      hypotheses), dropping hypotheses that mention havocked names;
//!   3. body path: assume invariants + condition, execute the body, and at
//!      its end prove each invariant again (substituted) plus variant
//!      decrease against a snapshot binder;
//!   4. continuation: assume invariants + ¬condition and keep going.
//!
//! Every proven obligation's goal is then *assumed* (pushed as a
//! hypothesis) — sound, and it is what lets later obligations (e.g. a gcd
//! descent `a % b < b`) close by `assumption` instead of re-deriving
//! nonlinear facts the portfolio cannot reach.

use crate::ast::*;
use crate::check::FnSig;
use crate::scan::Clause;
use crate::span::Span;
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone)]
pub struct Obligation {
    pub name: String,
    pub thm_name: String,
    pub kind_desc: String,
    pub span: Span,
    pub goal: String,
    /// (name, Lean type)
    pub binders: Vec<(String, String)>,
    /// (hypothesis name, Lean proposition)
    pub hyps: Vec<(String, String)>,
    pub context: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct ClauseWf {
    pub def_name: String,
    pub binders: Vec<(String, String)>,
    pub text: String,
    pub span: Span,
    pub desc: String,
    /// "Prop" for logical clauses, "Int" for variant measures.
    pub result_ty: &'static str,
}

pub struct VcResult {
    pub ghosts: Vec<GhostItem>,
    pub clause_wfs: Vec<ClauseWf>,
    pub obligations: Vec<Obligation>,
}

pub fn generate(program: &Program, sigs: &HashMap<String, FnSig>, source: &str) -> VcResult {
    let fn_map: HashMap<&str, &Fn> = program.fns.iter().map(|f| (f.name.as_str(), f)).collect();
    let mut result = VcResult {
        ghosts: program.ghosts.clone(),
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
            var_tys: HashMap::new(),
            mut_arrays: HashMap::new(),
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
    Int(String),
    Prop(String),
    Opt(String),
    /// Symbolic array value: entry binder or a `.set` chain over it.
    Arr(String),
}

#[derive(Clone)]
enum Tail<'a> {
    FnEnd,
    Loop {
        invariants: &'a [Clause],
        variant: &'a Clause,
        v0: String,
    },
}

struct Generator<'a> {
    f: &'a Fn,
    sigs: &'a HashMap<String, FnSig>,
    fn_map: &'a HashMap<&'a str, &'a Fn>,
    source: &'a str,
    binders: Vec<(String, String)>,
    hyps: Vec<(String, String)>,
    context: Vec<String>,
    env: HashMap<String, Val>,
    var_tys: HashMap<String, Ty>,
    /// &mut array params: source name → entry-state binder (`_old_a`).
    mut_arrays: HashMap<String, String>,
    fresh: usize,
    name_counts: HashMap<String, usize>,
    out: &'a mut VcResult,
}

impl<'a> Generator<'a> {
    fn run(&mut self) {
        for p in &self.f.params {
            self.var_tys.insert(p.name.clone(), p.ty);
            match p.ty {
                Ty::Int(it) => {
                    self.binders.push((p.name.clone(), "Int".into()));
                    self.hyps
                        .push((format!("h_{}_range", p.name), range_prop(&p.name, it)));
                    self.env.insert(p.name.clone(), Val::Int(p.name.clone()));
                }
                Ty::Bool => {
                    self.binders.push((p.name.clone(), "Bool".into()));
                    self.env
                        .insert(p.name.clone(), Val::Prop(format!("({} = true)", p.name)));
                }
                Ty::Array(elem, mutability) => {
                    // A &mut array's binder is the *entry* state `_old_a`;
                    // the current state lives in the symbolic env (a `.set`
                    // chain), and `old a` in clauses resolves to the binder.
                    let binder = match mutability {
                        Mutability::Mut => format!("_old_{}", p.name),
                        Mutability::Shared => p.name.clone(),
                    };
                    self.binders.push((binder.clone(), "Sable.Seq Int".into()));
                    self.hyps.push((
                        format!("h_{}_len", p.name),
                        format!("0 ≤ {binder}.len ∧ {binder}.len ≤ u64.max"),
                    ));
                    self.hyps.push((
                        format!("h_{}_elems", p.name),
                        format!(
                            "∀ k, 0 ≤ k → k < {binder}.len → {} ≤ {binder}.get k ∧ {binder}.get k ≤ {}",
                            elem.lean_min(),
                            elem.lean_max()
                        ),
                    ));
                    if mutability == Mutability::Mut {
                        self.mut_arrays.insert(p.name.clone(), binder.clone());
                    }
                    self.env.insert(p.name.clone(), Val::Arr(binder));
                }
                Ty::Option(_) | Ty::Unit => unreachable!("checked: no such params"),
            }
        }
        let f = self.f;
        for (i, pre) in f.pres.iter().enumerate() {
            let text = self.preprocess(&pre.text);
            let hyp = self.subst_env(&text);
            self.hyps.push((format!("h_pre_{}", i + 1), format!("({hyp})")));
            self.context.push(format!("pre {}", pre.text));
            let binders = self.wf_binders();
            self.out.clause_wfs.push(ClauseWf {
                def_name: format!("wf_{}_pre_{}", sanitize(&f.name), i + 1),
                binders,
                text,
                span: pre.span,
                desc: format!("`pre` clause of `{}`", f.name),
                result_ty: "Prop",
            });
        }
        for (i, post) in f.posts.iter().enumerate() {
            let mut binders = self.wf_binders();
            if f.ret != Ty::Unit {
                binders.push(("result".to_string(), self.result_lean_ty()));
            }
            self.out.clause_wfs.push(ClauseWf {
                def_name: format!("wf_{}_post_{}", sanitize(&f.name), i + 1),
                binders,
                text: self.preprocess(&post.text),
                span: post.span,
                desc: format!("`post` clause of `{}`", f.name),
                result_ty: "Prop",
            });
        }
        if let Some(v) = &f.variant {
            let binders = self.wf_binders();
            self.out.clause_wfs.push(ClauseWf {
                def_name: format!("wf_{}_variant", sanitize(&f.name)),
                binders,
                text: self.preprocess(&v.text),
                span: v.span,
                desc: format!("`variant` clause of `{}`", f.name),
                result_ty: "Int",
            });
        }

        let stmts: Vec<&Stmt> = self.f.body.iter().collect();
        self.exec(&stmts, &Tail::FnEnd);
    }

    fn result_lean_ty(&self) -> String {
        match self.f.ret {
            Ty::Option(_) => "Option Int".into(),
            _ => "Int".into(),
        }
    }

    fn exec(&mut self, stmts: &[&'a Stmt], tail: &Tail<'a>) {
        let Some((stmt, rest)) = stmts.split_first() else {
            // A procedure path falling off the end is its implicit return.
            if matches!(tail, Tail::FnEnd) && self.f.ret == Ty::Unit {
                self.emit_posts(None);
            }
            // A path fell off the end of a loop body: prove preservation.
            if let Tail::Loop {
                invariants,
                variant,
                v0,
            } = tail
            {
                for inv in *invariants {
                    let goal = self.subst_env(&self.preprocess(&inv.text));
                    let ob = self.obligation(
                        &format!("{}.inv_preserved.{}", self.f.name, slug(&inv.text)),
                        "loop invariant must be preserved by the body".into(),
                        inv.span,
                        goal,
                    );
                    self.push_obligation(ob);
                }
                let goal = format!(
                    "0 ≤ {v0} ∧ ({}) < {v0}",
                    self.subst_env(&self.preprocess(&variant.text))
                );
                let ob = self.obligation(
                    &format!("{}.variant_decreases.{}", self.f.name, slug(&variant.text)),
                    "loop variant must be a nonnegative measure that strictly decreases"
                        .into(),
                    variant.span,
                    goal,
                );
                self.push_obligation(ob);
            }
            return;
        };
        match stmt {
            Stmt::Decl { name, ty, init, .. } => {
                self.var_tys.insert(name.clone(), *ty);
                if let Some(e) = init {
                    let v = self.eval(e);
                    self.env.insert(name.clone(), v);
                } else {
                    self.env.remove(name);
                }
                self.exec(rest, tail);
            }
            Stmt::Assign { name, value, .. } => {
                let v = self.eval(value);
                self.env.insert(name.clone(), v);
                self.exec(rest, tail);
            }
            Stmt::Return { value, .. } => {
                let result_eq = value.as_ref().map(|value| match &value.kind {
                    ExprKind::SomeE(inner) => {
                        let Val::Int(v) = self.eval(inner) else {
                            unreachable!()
                        };
                        format!("(result = some ({v}))")
                    }
                    ExprKind::NoneE => "(result = none)".to_string(),
                    _ => match self.eval(value) {
                        Val::Int(v) => format!("(result = {v})"),
                        Val::Opt(v) => format!("(result = {v})"),
                        _ => unreachable!("bool returns rejected"),
                    },
                });
                self.emit_posts(result_eq);
            }
            Stmt::Store {
                array,
                array_span,
                index,
                value,
            } => {
                let Val::Int(i) = self.eval(index) else {
                    unreachable!()
                };
                let Val::Int(v) = self.eval(value) else {
                    unreachable!()
                };
                let arr = self.arr_str(array);
                let goal = format!("0 ≤ {i} ∧ {i} < ({arr}.len)");
                let ob = self.obligation(
                    &format!("{}.bounds.{}", self.f.name, slug(self.src(index.span))),
                    format!(
                        "store index `{}` must be within bounds",
                        self.src_short(index.span)
                    ),
                    array_span.join(index.span),
                    goal.clone(),
                );
                self.push_obligation(ob);
                self.assume_fact(&goal);
                self.env
                    .insert(array.clone(), Val::Arr(format!("({arr}.set {i} {v})")));
                self.exec(rest, tail);
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
                self.exec(&then_stmts, tail);

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
                        self.exec(&else_stmts, tail);
                    }
                    None => self.exec(rest, tail),
                }
                self.hyps.truncate(snap_hyps);
                self.context.truncate(snap_ctx);
            }
            Stmt::While {
                cond,
                invariants,
                variant,
                body,
                ..
            } => {
                let variant = variant.as_ref().expect("checked: variant present");

                // Well-formedness defs so clause elaboration errors map to
                // the clause span. Binders: everything in scope.
                let mut scope_binders: Vec<(String, String)> = self
                    .var_tys
                    .iter()
                    .filter_map(|(name, ty)| match ty {
                        Ty::Int(_) => Some((name.clone(), "Int".to_string())),
                        Ty::Bool => Some((name.clone(), "Bool".to_string())),
                        Ty::Array(..) => Some((name.clone(), "Sable.Seq Int".to_string())),
                        Ty::Option(_) | Ty::Unit => None,
                    })
                    .collect();
                for entry in self.mut_arrays.values() {
                    scope_binders.push((entry.clone(), "Sable.Seq Int".to_string()));
                }
                for (i, clause) in invariants.iter().chain(std::iter::once(variant)).enumerate() {
                    self.fresh += 1;
                    self.out.clause_wfs.push(ClauseWf {
                        def_name: format!(
                            "wf_{}_loop{}_{}",
                            sanitize(&self.f.name),
                            self.fresh,
                            i
                        ),
                        binders: scope_binders.clone(),
                        text: self.preprocess(&clause.text),
                        span: clause.span,
                        desc: format!("loop annotation in `{}`", self.f.name),
                        result_ty: if i == invariants.len() { "Int" } else { "Prop" },
                    });
                }

                // 1. Invariants hold at entry (substituted goals).
                for inv in invariants {
                    let goal = self.subst_env(&self.preprocess(&inv.text));
                    let ob = self.obligation(
                        &format!("{}.inv_init.{}", self.f.name, slug(&inv.text)),
                        "loop invariant must hold at loop entry".into(),
                        inv.span,
                        goal,
                    );
                    self.push_obligation(ob);
                }

                // 2. Havoc assigned state (fresh source-named binders).
                self.havoc(body);

                // 3. Assume invariants; evaluate the condition once in the
                // havocked context (its VCs must follow from invariants).
                self.fresh += 1;
                let tag = self.fresh;
                for (i, inv) in invariants.iter().enumerate() {
                    let text = self.subst_env(&self.preprocess(&inv.text));
                    self.hyps
                        .push((format!("h_inv{}_{}", tag, i + 1), format!("({text})")));
                    self.context.push(format!("invariant {}", inv.text));
                }
                let p = self.eval_prop(cond);

                let snap_env = self.env.clone();
                let snap_hyps = self.hyps.len();
                let snap_ctx = self.context.len();

                // 4. Body path.
                self.fresh += 1;
                let v0 = format!("_v{}", self.fresh);
                self.binders.push((v0.clone(), "Int".into()));
                let vtext = self.subst_env(&self.preprocess(&variant.text));
                self.hyps
                    .push((format!("h{v0}"), format!("{v0} = ({vtext})")));
                let h_cond = self.fresh_hyp("h_path");
                self.hyps.push((h_cond, p.clone()));
                self.context.push(format!("path {p}"));
                let body_stmts: Vec<&Stmt> = body.iter().collect();
                let loop_tail = Tail::Loop {
                    invariants,
                    variant,
                    v0,
                };
                self.exec(&body_stmts, &loop_tail);

                self.env = snap_env;
                self.hyps.truncate(snap_hyps);
                self.context.truncate(snap_ctx);

                // 5. Continuation: invariants + ¬cond.
                let h_exit = self.fresh_hyp("h_path");
                self.hyps.push((h_exit, format!("¬{p}")));
                self.context.push(format!("path ¬{p}"));
                self.exec(rest, tail);
                self.hyps.truncate(snap_hyps);
                self.context.truncate(snap_ctx);
            }
        }
    }

    /// Fresh source-named binders for everything the loop body assigns
    /// (plus locals whose symbolic value mentions a havocked variable,
    /// transitively). Hypotheses mentioning havocked names are dropped.
    fn havoc(&mut self, body: &[Stmt]) {
        let mut havoc_set: HashSet<String> = HashSet::new();
        collect_assigned(body, &mut havoc_set);
        // Cascade: symbolic values referring to havocked names die too.
        loop {
            let mut grew = false;
            for (name, val) in &self.env {
                if havoc_set.contains(name) {
                    continue;
                }
                let s = match val {
                    Val::Int(s) | Val::Opt(s) | Val::Arr(s) => s,
                    Val::Prop(s) => s,
                };
                if havoc_set.iter().any(|h| mentions(s, h)) {
                    // Shared arrays map to their own name and never change.
                    if !matches!(
                        self.var_tys.get(name),
                        Some(Ty::Array(_, Mutability::Shared))
                    ) {
                        havoc_set.insert(name.clone());
                        grew = true;
                        break;
                    }
                }
            }
            if !grew {
                break;
            }
        }

        self.hyps
            .retain(|(_, prop)| !havoc_set.iter().any(|h| mentions(prop, h)));
        self.context
            .retain(|note| !havoc_set.iter().any(|h| mentions(note, h)));

        for name in &havoc_set {
            // Rename any existing binder occupying the source name.
            self.fresh += 1;
            let stale = format!("_old{}_{name}", self.fresh);
            for b in self.binders.iter_mut() {
                if b.0 == *name {
                    b.0 = stale.clone();
                }
            }
            match self.var_tys.get(name) {
                Some(Ty::Int(it)) => {
                    let it = *it;
                    self.binders.push((name.clone(), "Int".into()));
                    self.hyps.push((
                        format!("h_{name}_range{}", self.fresh),
                        range_prop(name, it),
                    ));
                    self.env.insert(name.clone(), Val::Int(name.clone()));
                }
                Some(Ty::Bool) => {
                    self.binders.push((name.clone(), "Bool".into()));
                    self.env
                        .insert(name.clone(), Val::Prop(format!("({name} = true)")));
                }
                Some(Ty::Array(elem, Mutability::Mut)) => {
                    // Stores are the only mutation and preserve length and
                    // element ranges by construction, so both facts are
                    // sound to assume at havoc.
                    let elem = *elem;
                    let entry = self.mut_arrays[name.as_str()].clone();
                    self.binders.push((name.clone(), "Sable.Seq Int".into()));
                    self.hyps.push((
                        format!("h_{name}_len{}", self.fresh),
                        format!("({name}.len) = ({entry}.len)"),
                    ));
                    self.hyps.push((
                        format!("h_{name}_elems{}", self.fresh),
                        format!(
                            "∀ k, 0 ≤ k → k < {name}.len → {} ≤ {name}.get k ∧ {name}.get k ≤ {}",
                            elem.lean_min(),
                            elem.lean_max()
                        ),
                    ));
                    self.env.insert(name.clone(), Val::Arr(name.clone()));
                }
                _ => {}
            }
        }
    }

    fn eval(&mut self, e: &Expr) -> Val {
        match &e.kind {
            ExprKind::IntLit(n) => Val::Int(if *n < 0 {
                format!("({n})")
            } else {
                format!("{n}")
            }),
            ExprKind::BoolLit(b) => Val::Prop(if *b { "True".into() } else { "False".into() }),
            ExprKind::Var(name) => self.env.get(name).cloned().expect("checked: initialized"),
            ExprKind::Len { array } => {
                let arr = self.arr_str(array);
                Val::Int(format!("({arr}.len)"))
            }
            ExprKind::Widen { arg, .. } => self.eval(arg),
            ExprKind::SomeE(_) | ExprKind::NoneE => {
                unreachable!("checked: options only in return position")
            }
            ExprKind::Index { array, index, .. } => {
                let Val::Int(i) = self.eval(index) else {
                    unreachable!()
                };
                let Ty::Int(elem) = e.ty.unwrap() else {
                    unreachable!()
                };
                let arr = self.arr_str(array);
                let goal = format!("0 ≤ {i} ∧ {i} < ({arr}.len)");
                let ob = self.obligation(
                    &format!("{}.bounds.{}", self.f.name, slug(self.src(e.span))),
                    format!("index `{}` must be within bounds", self.src_short(e.span)),
                    e.span,
                    goal.clone(),
                );
                self.push_obligation(ob);
                self.assume_fact(&goal);
                let value = format!("({arr}.get {i})");
                // Element range follows from the array's element fact +
                // the just-proven bounds; assuming it here saves the
                // automation a quantifier instantiation.
                self.assume_fact(&format!(
                    "{} ≤ {value} ∧ {value} ≤ {}",
                    elem.lean_min(),
                    elem.lean_max()
                ));
                Val::Int(value)
            }
            ExprKind::Unary { op, operand } => match op {
                UnOp::Neg => {
                    let Val::Int(v) = self.eval(operand) else {
                        unreachable!()
                    };
                    let value = format!("(-{v})");
                    let Ty::Int(it) = e.ty.unwrap() else {
                        unreachable!()
                    };
                    let goal = range_prop(&value, it);
                    let ob = self.obligation(
                        &format!("{}.overflow.{}", self.f.name, slug(self.src(e.span))),
                        format!(
                            "result of `{}` must fit in `{}`",
                            self.src_short(e.span),
                            it.name()
                        ),
                        e.span,
                        goal.clone(),
                    );
                    self.push_obligation(ob);
                    self.assume_fact(&goal);
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
                            let goal = range_prop(&value, it);
                            let ob = self.obligation(
                                &format!("{}.overflow.{}", self.f.name, slug(self.src(e.span))),
                                format!(
                                    "result of `{}` must fit in `{}`",
                                    self.src_short(e.span),
                                    it.name()
                                ),
                                e.span,
                                goal.clone(),
                            );
                            self.push_obligation(ob);
                            self.assume_fact(&goal);
                        }
                        BinOp::Div | BinOp::Rem => {
                            let goal = format!("{r} ≠ 0");
                            let ob = self.obligation(
                                &format!("{}.div_zero.{}", self.f.name, slug(self.src(e.span))),
                                format!(
                                    "divisor `{}` must be nonzero",
                                    self.src_short(rhs.span)
                                ),
                                rhs.span,
                                goal.clone(),
                            );
                            self.push_obligation(ob);
                            self.assume_fact(&goal);
                            if it.signed() && *op == BinOp::Div {
                                let goal = format!(
                                    "¬({l} = {} ∧ {r} = (-1))",
                                    it.lean_min()
                                );
                                let ob = self.obligation(
                                    &format!(
                                        "{}.div_overflow.{}",
                                        self.f.name,
                                        slug(self.src(e.span))
                                    ),
                                    format!(
                                        "`{}` must not be `{}.min / -1` (Euclidean quotient \
                                         overflows)",
                                        self.src_short(e.span),
                                        it.name()
                                    ),
                                    e.span,
                                    goal.clone(),
                                );
                                self.push_obligation(ob);
                                self.assume_fact(&goal);
                            }
                            if !it.signed() {
                                // Euclidean bounds; provable from r > 0,
                                // assumed to spare the portfolio nonlinear
                                // reasoning (e.g. gcd's descent VC).
                                if *op == BinOp::Rem {
                                    self.assume_fact(&format!(
                                        "0 ≤ {value} ∧ {value} < {r}"
                                    ));
                                } else {
                                    self.assume_fact(&format!(
                                        "0 ≤ {value} ∧ {value} ≤ {l}"
                                    ));
                                }
                            }
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
                            unreachable!("checked: int args only")
                        };
                        v
                    })
                    .collect();
                let callee_fn = self.fn_map[callee.as_str()];
                let sig = &self.sigs[callee.as_str()];
                let subst_map: HashMap<String, String> = sig
                    .params
                    .iter()
                    .map(|p| p.name.clone())
                    .zip(arg_vals.iter().cloned())
                    .collect();

                for pre in &callee_fn.pres {
                    let goal = substitute(&pre.text, &subst_map, None);
                    let ob = self.obligation(
                        &format!("{}.call_pre.{}.{}", self.f.name, callee, slug(&pre.text)),
                        format!("`pre {}` of `{callee}` must hold at this call", pre.text),
                        e.span,
                        goal,
                    );
                    self.push_obligation(ob);
                }

                // Self-recursion: the callee's measure, on the arguments,
                // must be a nonnegative decrease of the current measure.
                if *callee == self.f.name {
                    let variant = self.f.variant.as_ref().expect("checked");
                    let vtext = self.preprocess(&variant.text);
                    let callee_measure = substitute(&vtext, &subst_map, None);
                    let caller_measure = self.subst_env(&vtext);
                    let goal = format!(
                        "0 ≤ ({callee_measure}) ∧ ({callee_measure}) < ({caller_measure})"
                    );
                    let ob = self.obligation(
                        &format!("{}.termination.{}", self.f.name, slug(&variant.text)),
                        "recursive call must decrease the function's `variant`".into(),
                        e.span,
                        goal,
                    );
                    self.push_obligation(ob);
                }

                self.fresh += 1;
                let ret_sym = format!("_r{}", self.fresh);
                match sig.ret {
                    Ty::Int(ret_it) => {
                        self.binders.push((ret_sym.clone(), "Int".into()));
                        self.hyps
                            .push((format!("h{ret_sym}_range"), range_prop(&ret_sym, ret_it)));
                    }
                    Ty::Option(_) => {
                        self.binders.push((ret_sym.clone(), "Option Int".into()));
                    }
                    _ => unreachable!(),
                }
                for (i, post) in callee_fn.posts.iter().enumerate() {
                    let prop = substitute(&post.text, &subst_map, Some(&ret_sym));
                    self.hyps
                        .push((format!("h{ret_sym}_post_{}", i + 1), format!("({prop})")));
                    self.context
                        .push(format!("from `{callee}` post: {}", post.text));
                }
                match sig.ret {
                    Ty::Option(_) => Val::Opt(ret_sym),
                    _ => Val::Int(ret_sym),
                }
            }
        }
    }

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

    /// Substitute in-scope variables' symbolic values into clause text.
    /// Used for goals about a *specific* state (invariant entry/preservation,
    /// variant measures); hypotheses always splice verbatim against
    /// source-named binders.
    fn subst_env(&self, text: &str) -> String {
        let map: HashMap<String, String> = self
            .env
            .iter()
            .filter_map(|(name, val)| match val {
                Val::Int(s) | Val::Arr(s) if s != name => Some((name.clone(), s.clone())),
                _ => None,
            })
            .collect();
        substitute(text, &map, None)
    }

    /// Replace `old x` (x a &mut array param) with its entry-state binder.
    fn preprocess(&self, text: &str) -> String {
        let mut out = String::with_capacity(text.len());
        let mut rest = text;
        while let Some(pos) = rest.find("old") {
            let before_ok = pos == 0
                || !rest.as_bytes()[pos - 1].is_ascii_alphanumeric()
                    && rest.as_bytes()[pos - 1] != b'_'
                    && rest.as_bytes()[pos - 1] != b'.';
            let after = &rest[pos + 3..];
            let after_trim = after.trim_start();
            let ident: String = after_trim
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                .collect();
            if before_ok && !ident.is_empty() {
                if let Some(entry) = self.mut_arrays.get(&ident) {
                    out.push_str(&rest[..pos]);
                    out.push_str(entry);
                    rest = &after_trim[ident.len()..];
                    continue;
                }
            }
            out.push_str(&rest[..pos + 3]);
            rest = &rest[pos + 3..];
        }
        out.push_str(rest);
        out
    }

    /// Current symbolic array expression for an in-scope array name.
    fn arr_str(&self, name: &str) -> String {
        match self.env.get(name) {
            Some(Val::Arr(s)) => s.clone(),
            _ => unreachable!("checked: array in scope"),
        }
    }

    /// Binders for clause well-formedness defs: source names (plus the
    /// `_old_` twin for &mut arrays, so `old a` elaborates).
    fn wf_binders(&self) -> Vec<(String, String)> {
        let mut out = Vec::new();
        for p in &self.f.params {
            match p.ty {
                Ty::Int(_) => out.push((p.name.clone(), "Int".into())),
                Ty::Bool => out.push((p.name.clone(), "Bool".into())),
                Ty::Array(..) => {
                    out.push((p.name.clone(), "Sable.Seq Int".into()));
                    if let Some(entry) = self.mut_arrays.get(&p.name) {
                        out.push((entry.clone(), "Sable.Seq Int".into()));
                    }
                }
                Ty::Option(_) | Ty::Unit => {}
            }
        }
        out
    }

    /// Postcondition obligations for the current path. In post goals,
    /// by-value parameters mean their *entry* values (verbatim binders) but
    /// &mut arrays mean their *final* state — substituted here.
    fn emit_posts(&mut self, result_eq: Option<String>) {
        let f = self.f;
        let mut_map: HashMap<String, String> = self
            .mut_arrays
            .keys()
            .map(|name| (name.clone(), self.arr_str(name)))
            .collect();
        for post in &f.posts {
            let goal = substitute(&self.preprocess(&post.text), &mut_map, None);
            let mut ob = self.obligation(
                &format!("{}.post.{}", f.name, slug(&post.text)),
                format!("postcondition of `{}`", f.name),
                post.span,
                goal,
            );
            if f.ret != Ty::Unit {
                ob.binders.push(("result".to_string(), self.result_lean_ty()));
            }
            if let Some(eq) = &result_eq {
                ob.hyps.push(("h_result".to_string(), eq.clone()));
            }
            self.push_obligation(ob);
        }
    }

    fn assume_fact(&mut self, prop: &str) {
        let h = self.fresh_hyp("h_fact");
        self.hyps.push((h, prop.to_string()));
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

pub fn collect_assigned(stmts: &[Stmt], out: &mut std::collections::HashSet<String>) {
    for s in stmts {
        match s {
            Stmt::Assign { name, .. } => {
                out.insert(name.clone());
            }
            Stmt::Store { array, .. } => {
                out.insert(array.clone());
            }
            Stmt::If {
                then_block,
                else_block,
                ..
            } => {
                collect_assigned(then_block, out);
                if let Some(eb) = else_block {
                    collect_assigned(eb, out);
                }
            }
            Stmt::While { body, .. } => collect_assigned(body, out),
            _ => {}
        }
    }
}

fn range_prop(value: &str, it: IntTy) -> String {
    format!("{} ≤ {value} ∧ {value} ≤ {}", it.lean_min(), it.lean_max())
}

/// True if `text` contains `name` as a standalone identifier token
/// (not a field access like `.name`).
pub fn mentions(text: &str, name: &str) -> bool {
    scan_idents(text, |word, after_dot| !after_dot && word == name)
}

fn scan_idents(text: &str, mut pred: impl FnMut(&str, bool) -> bool) -> bool {
    let bytes = text.as_bytes();
    let mut i = 0;
    let mut prev: Option<u8> = None;
    while i < bytes.len() {
        let b = bytes[i];
        if b.is_ascii_alphabetic() || b == b'_' {
            let start = i;
            while i < bytes.len()
                && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_' || bytes[i] == b'\'')
            {
                i += 1;
            }
            if pred(&text[start..i], prev == Some(b'.')) {
                return true;
            }
            prev = Some(bytes[i - 1]);
            continue;
        }
        prev = Some(b);
        i += 1;
    }
    false
}

/// Replace identifiers per `map` (and `result`, when given) with
/// parenthesized replacements. Identifier-boundary aware; skips
/// identifiers preceded by `.` (field/namespace access like `u32.max`).
pub fn substitute(text: &str, map: &HashMap<String, String>, result: Option<&str>) -> String {
    // Byte-level scan: identifiers are pure ASCII, and non-ASCII bytes
    // (∀, ≤, → ...) are copied through untouched — pushing them as `char`
    // would mangle multi-byte UTF-8.
    let mut out: Vec<u8> = Vec::with_capacity(text.len());
    let bytes = text.as_bytes();
    let mut i = 0;
    let mut prev: Option<u8> = None;
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
            let after_dot = prev == Some(b'.');
            let replacement = if after_dot {
                None
            } else if word == "result" {
                result.map(|r| r.to_string())
            } else {
                map.get(word).cloned()
            };
            match replacement {
                Some(r) => out.extend_from_slice(format!("({r})").as_bytes()),
                None => out.extend_from_slice(word.as_bytes()),
            }
            prev = Some(bytes[i - 1]);
            continue;
        }
        out.push(b);
        prev = Some(b);
        i += 1;
    }
    String::from_utf8(out).expect("substitution preserves UTF-8")
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
