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
    pub classes: Vec<ClassEmit>,
    pub clause_wfs: Vec<ClauseWf>,
    pub obligations: Vec<Obligation>,
}

/// A class as the Lean emitter needs it: `structure name where fields`.
#[derive(Debug, Clone)]
pub struct ClassEmit {
    pub name: String,
    pub fields: Vec<(String, String)>,
    pub span: Span,
}

fn lean_field_ty(ty: Ty) -> String {
    match ty {
        Ty::Int(_) => "Int".into(),
        Ty::Bool => "Bool".into(),
        Ty::Array(..) => "Sable.Seq Int".into(),
        _ => unreachable!("checked: field types"),
    }
}

/// The class-member verification context.
#[derive(Clone, Copy)]
enum Cctx<'a> {
    None,
    Init(&'a ClassDecl),
    Method(&'a ClassDecl, SelfKind),
}

pub fn generate(program: &Program, sigs: &HashMap<String, FnSig>, source: &str) -> VcResult {
    let fn_map: HashMap<&str, &Fn> = program.fns.iter().map(|f| (f.name.as_str(), f)).collect();
    let trait_map: HashMap<&str, &TraitDecl> = program
        .traits
        .iter()
        .map(|t| (t.name.as_str(), t))
        .collect();
    let class_map: HashMap<&str, &ClassDecl> = program
        .classes
        .iter()
        .map(|c| (c.name.as_str(), c))
        .collect();
    let mut result = VcResult {
        ghosts: program.ghosts.clone(),
        classes: program
            .classes
            .iter()
            .map(|c| ClassEmit {
                name: c.name.clone(),
                fields: c
                    .fields
                    .iter()
                    .map(|f| (f.name.clone(), lean_field_ty(f.ty)))
                    .collect(),
                span: c.name_span,
            })
            .collect(),
        clause_wfs: Vec::new(),
        obligations: Vec::new(),
    };

    for c in &program.class_templates {
        result.classes.push(ClassEmit {
            name: c.name.clone(),
            fields: c
                .fields
                .iter()
                .map(|f| (f.name.clone(), lean_field_ty(f.ty)))
                .collect(),
            span: c.name_span,
        });
    }

    // Class invariant well-formedness defs: binders are the bare fields.
    for c in program.classes.iter().chain(program.class_templates.iter()) {
        let binders: Vec<(String, String)> = c
            .fields
            .iter()
            .map(|f| (f.name.clone(), lean_field_ty(f.ty)))
            .collect();
        for (i, inv) in c.invariants.iter().enumerate() {
            let mut wf_binders: Vec<(String, String)> = Vec::new();
            for (ti, t) in c.type_params.iter().enumerate() {
                wf_binders.push((t.clone(), "Sable.IntModel".to_string()));
                if let Some(Some(b)) = c.type_bounds.get(ti) {
                    if let Some(tr) = trait_map.get(b.as_str()) {
                        for sp in &tr.specs {
                            wf_binders.push((format!("{t}_{}", sp.name), sp.sig.clone()));
                        }
                    }
                }
            }
            wf_binders.extend(binders.clone());
            result.clause_wfs.push(ClauseWf {
                def_name: format!("wf_{}_invariant_{}", sanitize(&c.name), i + 1),
                binders: wf_binders,
                text: inv.text.clone(),
                span: inv.span,
                desc: format!("class invariant of `{}`", c.name),
                result_ty: "Prop",
            });
        }
    }

    let run_one = |f: &Fn, fname: String, cctx: Cctx, result: &mut VcResult| {
        let mut generator = Generator {
            f,
            fname,
            cctx,
            classes: &program.classes,
            sigs,
            fn_map: &fn_map,
            class_map: &class_map,
            source,
            binders: Vec::new(),
            hyps: Vec::new(),
            context: Vec::new(),
            env: HashMap::new(),
            var_tys: HashMap::new(),
            mut_arrays: HashMap::new(),
            fresh: 0,
            tparams: Vec::new(),
            trait_ctx: HashMap::new(),
            name_hint: None,
            name_counts: HashMap::new(),
            out: result,
        };
        generator.run();
    };

    for f in &program.fns {
        // Tests are dynamic-only (design §9): never verified.
        if f.name.starts_with("test_") {
            continue;
        }
        // Template-verified instances (ADR 0009): the template theorems
        // cover their obligations; the residue is the substituted
        // `requires` — pure numeric facts about concrete bounds.
        if let Some(tname) = &f.from_template {
            for (i, req) in f.requires.iter().enumerate() {
                let name = format!("{}.requires.{}", f.name, cslug(req));
                result.obligations.push(Obligation {
                    thm_name: format!("vc_{}_{}", sanitize(&name), i),
                    name,
                    kind_desc: format!(
                        "`requires` of template `{tname}` at this instantiation"
                    ),
                    span: req.span,
                    goal: format!("({})", req.text),
                    binders: Vec::new(),
                    hyps: Vec::new(),
                    context: vec![format!("instantiated from `{tname}`")],
                });
            }
            continue;
        }
        run_one(f, f.name.clone(), Cctx::None, &mut result);
    }

    // Fn templates (ADR 0009): verified once against the abstract
    // model — obligations bind `(T : Sable.IntModel)` with `T.wf` and
    // the declared `requires` as hypotheses.
    for f in &program.fn_templates {
        let mut generator = Generator {
            f,
            fname: f.name.clone(),
            cctx: Cctx::None,
            classes: &program.classes,
            sigs,
            fn_map: &fn_map,
            class_map: &class_map,
            source,
            binders: Vec::new(),
            hyps: Vec::new(),
            context: Vec::new(),
            env: HashMap::new(),
            var_tys: HashMap::new(),
            mut_arrays: HashMap::new(),
            fresh: 0,
            tparams: f.type_params.clone(),
            trait_ctx: HashMap::new(),
            name_hint: None,
            name_counts: HashMap::new(),
            out: &mut result,
        };
        for (i, t) in f.type_params.iter().enumerate() {
            generator.binders.push((t.clone(), "Sable.IntModel".into()));
            generator
                .hyps
                .push((format!("h_{t}_wf"), format!("{t}.wf")));
            generator.context.push(format!("type parameter {t}"));
            if let Some(Some(b)) = f.type_bounds.get(i) {
                let tr = trait_map[b.as_str()];
                for sp in &tr.specs {
                    generator
                        .binders
                        .push((format!("{t}_{}", sp.name), sp.sig.clone()));
                }
                generator.trait_ctx.insert(t.clone(), tr);
                generator.context.push(format!("bound {t}: {b}"));
            }
        }
        for req in &f.requires {
            generator
                .hyps
                .push((format!("h_req_{}", chslug(req)), format!("({})", req.text)));
            generator.context.push(format!("requires {}", req.text));
        }
        generator.run();
    }

    // Class templates (ADR 0009 slice 2): members verified once against
    // the abstract model — the acceptance test is Vec<T>'s per-instance
    // discharges collapsing to one template set.
    for c in &program.class_templates {
        let members: Vec<(&Fn, String, Cctx)> = c
            .inits
            .iter()
            .map(|i| (i, format!("{}::{}", c.name, i.name), Cctx::Init(c)))
            .chain(c.methods.iter().map(|m| {
                (
                    &m.f,
                    format!("{}::{}", c.name, m.f.name),
                    Cctx::Method(c, m.self_kind),
                )
            }))
            .collect();
        for (f, fname, cctx) in members {
            let mut generator = Generator {
                f,
                fname,
                cctx,
                classes: &program.classes,
                sigs,
                fn_map: &fn_map,
                class_map: &class_map,
                source,
                binders: Vec::new(),
                hyps: Vec::new(),
                context: Vec::new(),
                env: HashMap::new(),
                var_tys: HashMap::new(),
                mut_arrays: HashMap::new(),
                fresh: 0,
                tparams: c.type_params.clone(),
                trait_ctx: HashMap::new(),
                name_hint: None,
                name_counts: HashMap::new(),
                out: &mut result,
            };
            for (i, t) in c.type_params.iter().enumerate() {
                generator.binders.push((t.clone(), "Sable.IntModel".into()));
                generator
                    .hyps
                    .push((format!("h_{t}_wf"), format!("{t}.wf")));
                generator.context.push(format!("type parameter {t}"));
                if let Some(Some(b)) = c.type_bounds.get(i) {
                    let tr = trait_map[b.as_str()];
                    for sp in &tr.specs {
                        generator
                            .binders
                            .push((format!("{t}_{}", sp.name), sp.sig.clone()));
                    }
                    generator.trait_ctx.insert(t.clone(), tr);
                    generator.context.push(format!("bound {t}: {b}"));
                }
            }
            generator.run();
        }
    }
    for c in &program.classes {
        // Template-verified class instances (ADR 0009 slice 2): the
        // template's theorems cover their member obligations.
        if c.from_template.is_some() {
            continue;
        }
        for init in &c.inits {
            run_one(
                init,
                format!("{}::{}", c.name, init.name),
                Cctx::Init(c),
                &mut result,
            );
        }
        for m in &c.methods {
            run_one(
                &m.f,
                format!("{}::{}", c.name, m.f.name),
                Cctx::Method(c, m.self_kind),
                &mut result,
            );
        }
        // deinit bodies are empty in M5 (checked); nothing to verify.
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
    /// Symbolic class value: a binder or a `{ _ with f := v }` chain.
    Obj(String),
    Unit,
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
    /// Display name for obligations: `f` or `Class::member`.
    fname: String,
    cctx: Cctx<'a>,
    classes: &'a [ClassDecl],
    sigs: &'a HashMap<String, FnSig>,
    fn_map: &'a HashMap<&'a str, &'a Fn>,
    class_map: &'a HashMap<&'a str, &'a ClassDecl>,
    source: &'a str,
    binders: Vec<(String, String)>,
    hyps: Vec<(String, String)>,
    context: Vec<String>,
    env: HashMap<String, Val>,
    var_tys: HashMap<String, Ty>,
    /// &mut array params: source name → entry-state binder (`_old_a`).
    mut_arrays: HashMap<String, String>,
    fresh: usize,
    /// Template mode (ADR 0009): the type-parameter names; `TParam(i)`
    /// ranges render through `tparams[i]` as an `IntModel`.
    tparams: Vec<String>,
    /// Template mode, slice 3: bounded parameter → its trait (for
    /// modeling `K::m(...)` calls against the trait's contracts).
    trait_ctx: HashMap<String, &'a TraitDecl>,
    /// Source-name hint for the next call/alloc/ctor result binder:
    /// `u64 p = probe_step(...)` binds `p`, not `_r16`, so discharge
    /// scripts survive unrelated edits (same motivation as
    /// content-anchored hypothesis names).
    name_hint: Option<String>,
    name_counts: HashMap<String, usize>,
    out: &'a mut VcResult,
}

impl<'a> Generator<'a> {
    /// Substitution map for clauses about a specific self-state: bare
    /// field names and `self` map onto the given state expression.
    fn class_state_map(&self, class: &ClassDecl, state: &str) -> HashMap<String, String> {
        let mut map = HashMap::new();
        map.insert("self".to_string(), state.to_string());
        for fld in &class.fields {
            map.insert(fld.name.clone(), project_field(state, &fld.name));
        }
        map
    }

    /// In inits, fields map to their tracked symbolic values instead.
    fn init_state_map(&self, class: &ClassDecl) -> (String, HashMap<String, String>) {
        let literal = format!(
            "({}.mk {})",
            class.name,
            class
                .fields
                .iter()
                .map(|fld| {
                    match self.env.get(&format!("self.{}", fld.name)) {
                        Some(Val::Int(s)) | Some(Val::Arr(s)) => format!("{s}"),
                        Some(Val::Prop(p)) => format!("(decide {p})"),
                        _ => "0".to_string(), // unreachable: checked init
                    }
                })
                .collect::<Vec<_>>()
                .join(" ")
        );
        let mut map = HashMap::new();
        map.insert("self".to_string(), literal.clone());
        for fld in &class.fields {
            if let Some(Val::Int(s)) | Some(Val::Arr(s)) =
                self.env.get(&format!("self.{}", fld.name))
            {
                map.insert(fld.name.clone(), s.clone());
            }
        }
        (literal, map)
    }

    /// Per-field representability facts about a class-state binder —
    /// justified the same way havoc facts are: every store is checked.
    fn push_class_state_facts(&mut self, class: &ClassDecl, binder: &str) {
        for fld in &class.fields {
            match fld.ty {
                Ty::Int(it) => {
                    self.hyps.push((
                        format!("h_field_{}_range", fld.name),
                        self.r_prop(&format!("({binder}.{})", fld.name), it),
                    ));
                }
                Ty::Array(elem, _) => {
                    let path = format!("({binder}.{})", fld.name);
                    self.hyps.push((
                        format!("h_field_{}_len", fld.name),
                        format!("0 ≤ {path}.len ∧ {path}.len ≤ u64.max"),
                    ));
                    self.hyps.push((
                        format!("h_field_{}_elems", fld.name),
                        format!(
                            "∀ k, 0 ≤ k → k < {path}.len → {} ≤ {path}.get k ∧ {path}.get k ≤ {}",
                            self.t_min(elem),
                            self.t_max(elem)
                        ),
                    ));
                }
                _ => {}
            }
        }
    }

    /// Class invariant as hypotheses about a given state.
    fn push_invariant_hyps(&mut self, class: &ClassDecl, state: &str) {
        let map = self.class_state_map(class, state);
        for inv in &class.invariants {
            let prop = substitute(&inv.text, &map, None);
            // Deduped: invariants with a shared slug prefix must not
            // shadow each other (discharges cite these names).
            self.push_hyp_unique(format!("h_cinv_{}", chslug(inv)), format!("({prop})"));
            self.context.push(format!("class invariant {}", inv.text));
        }
    }

    fn run(&mut self) {
        // Class-member setup: methods get the entry-state binder
        // `_old_self` with field facts and the class invariant assumed
        // (design §7 desugaring); inits start with no self at all.
        if let Cctx::Method(class, _) = self.cctx {
            self.binders
                .push(("_old_self".to_string(), class.name.clone()));
            self.mut_arrays
                .insert("self".to_string(), "_old_self".to_string());
            self.push_class_state_facts(class, "_old_self");
            self.push_invariant_hyps(class, "_old_self");
            self.env
                .insert("self".to_string(), Val::Obj("_old_self".to_string()));
        }
        for p in &self.f.params {
            self.var_tys.insert(p.name.clone(), p.ty);
            match p.ty {
                Ty::ClassRef(ci) => {
                    // `&C` parameter (ADR 0010): the class value with its
                    // field facts and invariant — the method-entry
                    // treatment, re-aimed.
                    let cd = &self.classes[ci];
                    self.binders.push((p.name.clone(), cd.name.clone()));
                    self.push_class_state_facts(cd, &p.name);
                    self.push_invariant_hyps(cd, &p.name);
                    self.env
                        .insert(p.name.clone(), Val::Obj(p.name.clone()));
                }
                Ty::Int(it) => {
                    self.binders.push((p.name.clone(), "Int".into()));
                    self.hyps
                        .push((format!("h_{}_range", p.name), self.r_prop(&p.name, it)));
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
                        Mutability::Owned => unreachable!("owned arrays are test-only locals"),
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
                            self.t_min(elem),
                            self.t_max(elem)
                        ),
                    ));
                    if mutability == Mutability::Mut {
                        self.mut_arrays.insert(p.name.clone(), binder.clone());
                    }
                    self.env.insert(p.name.clone(), Val::Arr(binder));
                }
                Ty::Option(_) | Ty::Unit | Ty::Class(_) => {
                    unreachable!("checked: no such params")
                }
            }
        }
        let f = self.f;
        for (i, pre) in f.pres.iter().enumerate() {
            let text = self.preprocess(&pre.text);
            let hyp = self.subst_env(&text);
            let _ = i;
            self.hyps
                .push((format!("h_pre_{}", chslug(pre)), format!("({hyp})")));
            self.context.push(format!("pre {}", pre.text));
            let binders = self.wf_binders();
            self.out.clause_wfs.push(ClauseWf {
                def_name: format!("wf_{}_pre_{}", sanitize(&self.fname), i + 1),
                binders,
                text,
                span: pre.span,
                desc: format!("`pre` clause of `{}`", self.fname),
                result_ty: "Prop",
            });
        }
        for (i, post) in f.posts.iter().enumerate() {
            let mut binders = self.wf_binders();
            if f.ret != Ty::Unit {
                binders.push(("result".to_string(), self.result_lean_ty()));
            }
            self.out.clause_wfs.push(ClauseWf {
                def_name: format!("wf_{}_post_{}", sanitize(&self.fname), i + 1),
                binders,
                text: self.preprocess(&post.text),
                span: post.span,
                desc: format!("`post` clause of `{}`", self.fname),
                result_ty: "Prop",
            });
        }
        if let Some(v) = &f.variant {
            let binders = self.wf_binders();
            self.out.clause_wfs.push(ClauseWf {
                def_name: format!("wf_{}_variant", sanitize(&self.fname)),
                binders,
                text: self.preprocess(&v.text),
                span: v.span,
                desc: format!("`variant` clause of `{}`", self.fname),
                result_ty: "Int",
            });
        }

        let stmts: Vec<&Stmt> = self.f.body.iter().collect();
        self.exec(&stmts, &Tail::FnEnd);
    }

    fn result_lean_ty(&self) -> String {
        match self.f.ret {
            Ty::Option(_) => "Option Int".into(),
            // Bool results are Prop-valued in the logic: posts like
            // `result → P` splice with no coercion noise.
            Ty::Bool => "Prop".into(),
            // A returned class value is its structure (ADR 0010).
            Ty::Class(ci) => self.classes[ci].name.clone(),
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
                        &format!("{}.inv_preserved.{}", self.fname, cslug(inv)),
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
                    &format!("{}.variant_decreases.{}", self.fname, cslug(variant)),
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
                    if matches!(
                        e.kind,
                        ExprKind::Call { .. }
                            | ExprKind::MethodCall { .. }
                            | ExprKind::CtorCall { .. }
                            | ExprKind::TraitCall { .. }
                            | ExprKind::AllocArray { .. }
                    ) {
                        self.name_hint = Some(name.clone());
                    }
                    let v = self.eval(e);
                    self.name_hint = None;
                    self.env.insert(name.clone(), v);
                } else {
                    self.env.remove(name);
                }
                self.exec(rest, tail);
            }
            Stmt::Assign { name, value, .. } => {
                if matches!(
                    value.kind,
                    ExprKind::Call { .. }
                        | ExprKind::MethodCall { .. }
                        | ExprKind::CtorCall { .. }
                        | ExprKind::TraitCall { .. }
                        | ExprKind::AllocArray { .. }
                ) {
                    self.name_hint = Some(name.clone());
                }
                let v = self.eval(value);
                self.name_hint = None;
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
                        Val::Prop(p) => format!("(result ↔ ({p}))"),
                        Val::Obj(chain) => {
                            // Returning a class value: the invariant must
                            // hold of the returned state (ADR 0010's
                            // ret_inv — closes by assumption, but it is
                            // an obligation, not a trust step).
                            if let Ty::Class(ci) = self.f.ret {
                                let cd = &self.classes[ci];
                                let map = self.class_state_map(cd, &chain);
                                for inv in &cd.invariants {
                                    let goal = substitute(&inv.text, &map, None);
                                    let ob = self.obligation(
                                        &format!(
                                            "{}.ret_inv.{}",
                                            self.fname,
                                            cslug(inv)
                                        ),
                                        "invariant of the returned class value"
                                            .to_string(),
                                        value.span,
                                        goal,
                                    );
                                    self.push_obligation(ob);
                                }
                            }
                            format!("(result = {chain})")
                        }
                        _ => unreachable!("unit values cannot be returned"),
                    },
                });
                self.emit_posts(result_eq);
            }
            Stmt::ExprStmt(e) => {
                // Evaluated for obligations/assumptions only.
                let _ = self.eval(e);
                self.exec(rest, tail);
            }
            Stmt::VarDecl { name, init, ty, .. } => {
                if matches!(
                    init.kind,
                    ExprKind::Call { .. }
                        | ExprKind::MethodCall { .. }
                        | ExprKind::CtorCall { .. }
                        | ExprKind::TraitCall { .. }
                        | ExprKind::AllocArray { .. }
                ) {
                    self.name_hint = Some(name.clone());
                }
                let v = self.eval(init);
                self.name_hint = None;
                self.var_tys
                    .insert(name.clone(), ty.expect("checked: var type"));
                self.env.insert(name.clone(), v);
                self.exec(rest, tail);
            }
            Stmt::FieldAssign { field, value, .. } => {
                let v = self.eval(value);
                match self.cctx {
                    Cctx::Init(_) => {
                        self.env.insert(format!("self.{field}"), v);
                    }
                    Cctx::Method(..) => {
                        let vs = match v {
                            Val::Int(s) | Val::Arr(s) => s,
                            _ => unreachable!("checked: field value"),
                        };
                        let chain = self.self_chain();
                        self.env.insert(
                            "self".to_string(),
                            Val::Obj(format!("{{ {chain} with {field} := {vs} }}")),
                        );
                    }
                    Cctx::None => unreachable!("checked: fields only in members"),
                }
                self.exec(rest, tail);
            }
            Stmt::FieldStore {
                field,
                field_span,
                index,
                value,
            } => {
                let Val::Int(i) = self.eval(index) else {
                    unreachable!()
                };
                let Val::Int(v) = self.eval(value) else {
                    unreachable!()
                };
                let arr = self.self_field_str(field);
                let goal = format!("0 ≤ {i} ∧ {i} < ({arr}.len)");
                let ob = self.obligation(
                    &format!("{}.bounds.{}", self.fname, slug(self.src(index.span))),
                    format!(
                        "store index `{}` must be within bounds",
                        self.src_short(index.span)
                    ),
                    field_span.join(index.span),
                    goal.clone(),
                );
                self.push_obligation(ob);
                self.assume_fact(&goal);
                let updated = format!("({arr}.set {i} {v})");
                match self.cctx {
                    Cctx::Init(_) => {
                        self.env
                            .insert(format!("self.{field}"), Val::Arr(updated));
                    }
                    Cctx::Method(..) => {
                        let chain = self.self_chain();
                        self.env.insert(
                            "self".to_string(),
                            Val::Obj(format!("{{ {chain} with {field} := {updated} }}")),
                        );
                    }
                    Cctx::None => unreachable!("checked: fields only in members"),
                }
                self.exec(rest, tail);
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
                    &format!("{}.bounds.{}", self.fname, slug(self.src(index.span))),
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
                // Full clones, not length-truncation: a havoc in a
                // nested loop REWRITES earlier hypotheses in place
                // (SSA versioning), which truncation cannot undo.
                let snap_env = self.env.clone();
                let snap_hyps = self.hyps.clone();
                let snap_ctx = self.context.clone();

                self.hyps
                    .push((format!("h_path_{}", hslug(&p)), p.clone()));
                self.context.push(format!("path {p}"));
                let then_stmts: Vec<&Stmt> =
                    then_block.iter().chain(rest.iter().copied()).collect();
                self.exec(&then_stmts, tail);

                self.env = snap_env;
                self.hyps = snap_hyps.clone();
                self.context = snap_ctx.clone();

                self.hyps
                    .push((format!("h_path_not_{}", hslug(&p)), format!("¬{p}")));
                self.context.push(format!("path ¬{p}"));
                match else_block {
                    Some(eb) => {
                        let else_stmts: Vec<&Stmt> =
                            eb.iter().chain(rest.iter().copied()).collect();
                        self.exec(&else_stmts, tail);
                    }
                    None => self.exec(rest, tail),
                }
                self.hyps = snap_hyps;
                self.context = snap_ctx;
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
                let mut scope_binders: Vec<(String, String)> = Vec::new();
                for t in &self.tparams {
                    scope_binders.push((t.clone(), "Sable.IntModel".to_string()));
                    if let Some(tr) = self.trait_ctx.get(t.as_str()) {
                        for sp in &tr.specs {
                            scope_binders
                                .push((format!("{t}_{}", sp.name), sp.sig.clone()));
                        }
                    }
                }
                scope_binders.extend(self
                    .var_tys
                    .iter()
                    .filter_map(|(name, ty)| match ty {
                        Ty::Int(_) => Some((name.clone(), "Int".to_string())),
                        Ty::Bool => Some((name.clone(), "Bool".to_string())),
                        Ty::Array(..) => Some((name.clone(), "Sable.Seq Int".to_string())),
                        Ty::Class(ci) | Ty::ClassRef(ci) => {
                            Some((name.clone(), self.classes[*ci].name.clone()))
                        }
                        Ty::Option(_) | Ty::Unit => None,
                    }));
                for (name, entry) in self.mut_arrays.iter() {
                    if name == "self" {
                        continue; // handled below with the class type
                    }
                    scope_binders.push((entry.clone(), "Sable.Seq Int".to_string()));
                }
                match self.cctx {
                    Cctx::Init(c) => scope_binders.push(("self".to_string(), c.name.clone())),
                    Cctx::Method(c, _) => {
                        scope_binders.push(("self".to_string(), c.name.clone()));
                        scope_binders.push(("_old_self".to_string(), c.name.clone()));
                    }
                    Cctx::None => {}
                }
                for (i, clause) in invariants.iter().chain(std::iter::once(variant)).enumerate() {
                    self.fresh += 1;
                    self.out.clause_wfs.push(ClauseWf {
                        def_name: format!(
                            "wf_{}_loop{}_{}",
                            sanitize(&self.fname),
                            self.fresh,
                            i
                        ),
                        binders: scope_binders.clone(),
                        text: self.preprocess(&clause.text),
                        span: clause.span,
                        desc: format!("loop annotation in `{}`", self.fname),
                        result_ty: if i == invariants.len() { "Int" } else { "Prop" },
                    });
                }

                // 1. Invariants hold at entry (substituted goals).
                for inv in invariants {
                    let goal = self.subst_env(&self.preprocess(&inv.text));
                    let ob = self.obligation(
                        &format!("{}.inv_init.{}", self.fname, cslug(inv)),
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
                for inv in invariants.iter() {
                    let text = self.subst_env(&self.preprocess(&inv.text));
                    // Deduped: same-slug invariants must not shadow.
                    self.push_hyp_unique(
                        format!("h_inv_{}", chslug(inv)),
                        format!("({text})"),
                    );
                    self.context.push(format!("invariant {}", inv.text));
                }
                let p = self.eval_prop(cond);

                // Full clones — see the If arm.
                let snap_env = self.env.clone();
                let snap_hyps = self.hyps.clone();
                let snap_ctx = self.context.clone();

                // 4. Body path.
                self.fresh += 1;
                let v0 = format!("_v{}", self.fresh);
                self.binders.push((v0.clone(), "Int".into()));
                let vtext = self.subst_env(&self.preprocess(&variant.text));
                self.hyps.push((
                    format!("h_variant_{}", chslug(variant)),
                    format!("{v0} = ({vtext})"),
                ));
                self.hyps
                    .push((format!("h_path_{}", hslug(&p)), p.clone()));
                self.context.push(format!("path {p}"));
                let body_stmts: Vec<&Stmt> = body.iter().collect();
                let loop_tail = Tail::Loop {
                    invariants,
                    variant,
                    v0,
                };
                self.exec(&body_stmts, &loop_tail);

                self.env = snap_env;
                self.hyps = snap_hyps.clone();
                self.context = snap_ctx.clone();

                // 5. Continuation: invariants + ¬cond.
                self.hyps
                    .push((format!("h_path_not_{}", hslug(&p)), format!("¬{p}")));
                self.context.push(format!("path ¬{p}"));
                self.exec(rest, tail);
                self.hyps = snap_hyps;
                self.context = snap_ctx;
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
                    Val::Int(s) | Val::Opt(s) | Val::Arr(s) | Val::Obj(s) => s,
                    Val::Prop(s) => s,
                    Val::Unit => continue,
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

        // SSA-style versioning: binders occupying havocked source names
        // are renamed, and surviving hypotheses are REWRITTEN to the
        // stale names — facts about the pre-havoc value stay true of the
        // renamed binder. (Dropping them instead loses e.g. the alloc
        // facts of an array the loop mutates.) Hypotheses mentioning a
        // havocked name with no binder to rename (body-local decls) are
        // dropped as before.
        // Sorted iteration: fresh-number assignment must not depend on
        // hash order — the M8 CI failure was local-vs-CI divergence in
        // positional binder numbering.
        let mut havoc_names: Vec<&String> = havoc_set.iter().collect();
        havoc_names.sort();
        let mut stale_map: HashMap<String, String> = HashMap::new();
        for name in &havoc_names {
            let name = *name;
            if self.binders.iter().any(|(b, _)| b == name) {
                self.fresh += 1;
                let stale = format!("_old{}_{name}", self.fresh);
                for b in self.binders.iter_mut() {
                    if b.0 == *name {
                        b.0 = stale.clone();
                    }
                }
                stale_map.insert(name.clone(), stale);
            }
        }
        self.hyps.retain(|(_, prop)| {
            !havoc_set
                .iter()
                .any(|h| !stale_map.contains_key(h) && mentions(prop, h))
        });
        // Rewritten hypotheses get a `h_stale_` name so the fresh
        // invariant hypotheses keep their content-anchored names —
        // discharges cite the live facts, not the archived ones.
        let mut seen: HashSet<String> = self.hyps.iter().map(|(n, _)| n.clone()).collect();
        for idx in 0..self.hyps.len() {
            if stale_map.keys().any(|h| mentions(&self.hyps[idx].1, h)) {
                self.hyps[idx].1 = substitute(&self.hyps[idx].1, &stale_map, None);
                let old_name = self.hyps[idx].0.clone();
                let base = if old_name.starts_with("h_stale_") {
                    old_name.clone()
                } else {
                    format!("h_stale_{}", old_name.trim_start_matches("h_"))
                };
                let mut name = base.clone();
                let mut n = 1;
                while seen.contains(&name) {
                    n += 1;
                    name = format!("{base}_{n}");
                }
                seen.remove(&old_name);
                seen.insert(name.clone());
                self.hyps[idx].0 = name;
            }
        }
        self.context
            .retain(|note| !havoc_set.iter().any(|h| mentions(note, h)));

        for name in &havoc_names {
            let name = *name;
            // Mid-method self-mutation in a loop: fresh state binder,
            // field facts only (the class invariant is NOT in force
            // mid-method, design §7).
            if name == "self" {
                if let Cctx::Method(class, _) = self.cctx {
                    let b = self.hinted_sym("_self", Some("_self_loop".to_string()));
                    self.binders.push((b.clone(), class.name.clone()));
                    self.push_class_state_facts(class, &b);
                    self.env.insert("self".to_string(), Val::Obj(b));
                    continue;
                }
            }
            match self.var_tys.get(name) {
                Some(Ty::Int(it)) => {
                    let it = *it;
                    self.binders.push((name.clone(), "Int".into()));
                    self.hyps
                        .push((format!("h_{name}_range"), self.r_prop(name, it)));
                    self.env.insert(name.clone(), Val::Int(name.clone()));
                }
                Some(Ty::Bool) => {
                    self.binders.push((name.clone(), "Bool".into()));
                    self.env
                        .insert(name.clone(), Val::Prop(format!("({name} = true)")));
                }
                Some(Ty::Option(_)) => {
                    self.binders.push((name.clone(), "Option Int".into()));
                    self.env.insert(name.clone(), Val::Opt(name.clone()));
                }
                Some(Ty::Class(ci)) => {
                    // A loop body called &mut methods on this local: fresh
                    // state; the invariant held at each method exit, so it
                    // is sound to assume at the havoc point.
                    let cd = &self.classes[*ci];
                    self.binders.push((name.clone(), cd.name.clone()));
                    self.push_class_state_facts(cd, name);
                    self.push_invariant_hyps(cd, name);
                    self.env.insert(name.clone(), Val::Obj(name.clone()));
                }
                Some(Ty::Array(elem, Mutability::Owned)) => {
                    // Owned local mutated by the loop body: fresh state.
                    // Stores preserve length, so equate to the pre-havoc
                    // chain — but only when that chain does not itself
                    // mention a havocked name (else drop to range facts).
                    let elem = *elem;
                    // The prior chain may reference renamed binders
                    // (alloc binders carry the source name): rewrite to
                    // the stale names rather than dropping.
                    let prior = match self.env.get(name) {
                        Some(Val::Arr(s)) => Some(substitute(s, &stale_map, None)),
                        _ => None,
                    };
                    self.binders.push((name.clone(), "Sable.Seq Int".into()));
                    if let Some(prior) = prior {
                        if !havoc_set
                            .iter()
                            .any(|h| !stale_map.contains_key(h) && mentions(&prior, h))
                        {
                            self.hyps.push((
                                format!("h_{name}_len"),
                                format!("({name}.len) = ({prior}.len)"),
                            ));
                        }
                    }
                    self.hyps.push((
                        format!("h_{name}_elems"),
                        format!(
                            "∀ k, 0 ≤ k → k < {name}.len → {} ≤ {name}.get k ∧ {name}.get k ≤ {}",
                            self.t_min(elem),
                            self.t_max(elem)
                        ),
                    ));
                    self.env.insert(name.clone(), Val::Arr(name.clone()));
                }
                Some(Ty::Array(elem, Mutability::Mut)) => {
                    // Stores are the only mutation and preserve length and
                    // element ranges by construction, so both facts are
                    // sound to assume at havoc.
                    let elem = *elem;
                    let entry = self.mut_arrays[name.as_str()].clone();
                    self.binders.push((name.clone(), "Sable.Seq Int".into()));
                    self.hyps.push((
                        format!("h_{name}_len"),
                        format!("({name}.len) = ({entry}.len)"),
                    ));
                    self.hyps.push((
                        format!("h_{name}_elems"),
                        format!(
                            "∀ k, 0 ≤ k → k < {name}.len → {} ≤ {name}.get k ∧ {name}.get k ≤ {}",
                            self.t_min(elem),
                            self.t_max(elem)
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
            ExprKind::IntLit(n) => {
                let v = if *n < 0 {
                    format!("({n})")
                } else {
                    format!("{n}")
                };
                // A literal at type `T` cannot be range-checked
                // statically: emit a fits-VC against the model
                // (ADR 0009); dischargeable from `wf`/`requires`.
                if let Some(Ty::Int(it @ IntTy::TParam(_))) = e.ty {
                    let goal = self.r_prop(&v, it);
                    let ob = self.obligation(
                        &format!("{}.lit.{}", self.fname, slug(&v)),
                        format!("literal `{n}` must fit the type parameter"),
                        e.span,
                        goal.clone(),
                    );
                    self.push_obligation(ob);
                    self.assume_fact(&goal);
                }
                Val::Int(v)
            }
            ExprKind::BoolLit(b) => Val::Prop(if *b { "True".into() } else { "False".into() }),
            ExprKind::Var(name) => self.env.get(name).cloned().expect("checked: initialized"),
            ExprKind::Len { array } => {
                let arr = self.arr_str(array);
                Val::Int(format!("({arr}.len)"))
            }
            ExprKind::IsSome { operand } => {
                let Val::Opt(o) = self.eval(operand) else {
                    unreachable!()
                };
                Val::Prop(format!("({o} ≠ none)"))
            }
            ExprKind::OptValue { operand } => {
                // Junk-on-none like `Seq.get` off-range; the someness VC
                // keeps verified code away from the junk (ADR 0008).
                let Val::Opt(o) = self.eval(operand) else {
                    unreachable!()
                };
                let goal = format!("({o}) ≠ none");
                let ob = self.obligation(
                    &format!("{}.option.{}", self.fname, slug(self.src(e.span))),
                    format!(
                        "`{}` must hold a value here",
                        self.src_short(e.span)
                    ),
                    e.span,
                    goal.clone(),
                );
                self.push_obligation(ob);
                self.assume_fact(&goal);
                Val::Int(format!("(({o}).value)"))
            }
            ExprKind::Widen { arg, .. } => self.eval(arg),
            ExprKind::Narrow { target, arg } => {
                let Val::Int(v) = self.eval(arg) else {
                    unreachable!()
                };
                let goal = self.r_prop(&v, *target);
                let ob = self.obligation(
                    &format!("{}.narrow.{}", self.fname, slug(self.src(e.span))),
                    format!(
                        "`{}` must fit in `{}`",
                        self.src_short(e.span),
                        target.name()
                    ),
                    e.span,
                    goal.clone(),
                );
                self.push_obligation(ob);
                self.assume_fact(&goal);
                Val::Int(v)
            }
            ExprKind::SomeE(_) | ExprKind::NoneE => {
                unreachable!("checked: options only in return position")
            }
            ExprKind::Borrow { array, .. } => match self.env.get(array.as_str()) {
                Some(Val::Obj(chain)) => Val::Obj(chain.clone()),
                _ => Val::Arr(self.arr_str(array)),
            },
            ExprKind::ArrayLit(_) => {
                unreachable!("checked: test-only expression")
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
                    &format!("{}.bounds.{}", self.fname, slug(self.src(e.span))),
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
                    self.t_min(elem),
                    self.t_max(elem)
                ));
                Val::Int(value)
            }
            ExprKind::AllocArray { len, init, .. } => {
                let hint = self.name_hint.take();
                let Val::Int(n) = self.eval(len) else {
                    unreachable!()
                };
                let Val::Int(v0) = self.eval(init) else {
                    unreachable!()
                };
                // Allocation succeeds symbolically: failure is the named
                // OOM trap (design §10), not a proof obligation.
                let b = self.hinted_sym("_alloc", hint);
                self.binders.push((b.clone(), "Sable.Seq Int".into()));
                let h1 = self.fresh_hyp("h_alloc");
                self.hyps.push((h1, format!("({b}.len) = {n}")));
                let h2 = self.fresh_hyp("h_alloc");
                self.hyps.push((
                    h2,
                    format!("∀ k, 0 ≤ k → k < {b}.len → {b}.get k = {v0}"),
                ));
                Val::Arr(b)
            }
            ExprKind::ClassField { obj, field, .. } => {
                let Val::Obj(chain) = self.env[obj.as_str()].clone() else {
                    unreachable!("checked: class-typed receiver")
                };
                Val::Int(project_field(&chain, field))
            }
            ExprKind::ClassFieldLen { obj, field } => {
                let Val::Obj(chain) = self.env[obj.as_str()].clone() else {
                    unreachable!("checked: class-typed receiver")
                };
                Val::Int(format!("({}.len)", project_field(&chain, field)))
            }
            ExprKind::ClassFieldIndex {
                obj, field, index, ..
            } => {
                let Val::Obj(chain) = self.env[obj.as_str()].clone() else {
                    unreachable!("checked: class-typed receiver")
                };
                let Val::Int(i) = self.eval(index) else {
                    unreachable!()
                };
                let arr = project_field(&chain, field);
                let goal = format!("0 ≤ {i} ∧ {i} < ({arr}.len)");
                let ob = self.obligation(
                    &format!("{}.bounds.{}", self.fname, slug(self.src(index.span))),
                    format!(
                        "index `{}` must be within bounds",
                        self.src_short(index.span)
                    ),
                    e.span,
                    goal.clone(),
                );
                self.push_obligation(ob);
                self.assume_fact(&goal);
                Val::Int(format!("({arr}.get {i})"))
            }
            ExprKind::SelfField { field } => match self.cctx {
                Cctx::Init(_) => self
                    .env
                    .get(&format!("self.{field}"))
                    .cloned()
                    .expect("checked: field initialized"),
                Cctx::Method(..) => {
                    Val::Int(project_field(&self.self_chain(), field))
                }
                Cctx::None => unreachable!("checked: fields only in members"),
            },
            ExprKind::SelfFieldLen { field } => {
                let arr = self.self_field_str(field);
                Val::Int(format!("({arr}.len)"))
            }
            ExprKind::SelfFieldIndex { field, index } => {
                let Val::Int(i) = self.eval(index) else {
                    unreachable!()
                };
                let Ty::Int(elem) = e.ty.unwrap() else {
                    unreachable!()
                };
                let arr = self.self_field_str(field);
                let goal = format!("0 ≤ {i} ∧ {i} < ({arr}.len)");
                let ob = self.obligation(
                    &format!("{}.bounds.{}", self.fname, slug(self.src(e.span))),
                    format!("index `{}` must be within bounds", self.src_short(e.span)),
                    e.span,
                    goal.clone(),
                );
                self.push_obligation(ob);
                self.assume_fact(&goal);
                let value = format!("({arr}.get {i})");
                self.assume_fact(&format!(
                    "{} ≤ {value} ∧ {value} ≤ {}",
                    self.t_min(elem),
                    self.t_max(elem)
                ));
                Val::Int(value)
            }
            ExprKind::CtorCall {
                class, init, args, ..
            } => {
                let hint = self.name_hint.take();
                let arg_vals: Vec<String> = args
                    .iter()
                    .map(|a| {
                        let Val::Int(v) = self.eval(a) else {
                            unreachable!("checked: int args")
                        };
                        v
                    })
                    .collect();
                let cd: &ClassDecl = self.class_map[class.as_str()];
                let ifn = cd
                    .inits
                    .iter()
                    .find(|i| i.name == *init)
                    .expect("checked: init exists");
                let subst_map: HashMap<String, String> = ifn
                    .params
                    .iter()
                    .map(|p| p.name.clone())
                    .zip(arg_vals.iter().cloned())
                    .collect();
                for pre in &ifn.pres {
                    let goal = substitute(&pre.text, &subst_map, None);
                    let ob = self.obligation(
                        &format!(
                            "{}.call_pre.{}_{}.{}",
                            self.fname,
                            class,
                            init,
                            cslug(pre)
                        ),
                        format!(
                            "`pre {}` of `{class}::{init}` must hold at this call",
                            pre.text
                        ),
                        e.span,
                        goal,
                    );
                    self.push_obligation(ob);
                }
                // Fresh post-construction state: the class invariant holds
                // (proved at every init exit) and the init's posts describe it.
                let b = self.hinted_sym("_obj", hint);
                self.binders.push((b.clone(), cd.name.clone()));
                self.push_class_state_facts(cd, &b);
                self.push_invariant_hyps(cd, &b);
                let mut post_map = self.class_state_map(cd, &b);
                post_map.extend(subst_map);
                for post in ifn.posts.iter() {
                    let prop = substitute(&post.text, &post_map, None);
                    self.push_hyp_unique(
                        format!(
                            "h_{}_{}_post_{}",
                            sanitize(class),
                            sanitize(init),
                            chslug(post)
                        ),
                        format!("({prop})"),
                    );
                }
                Val::Obj(b)
            }
            ExprKind::TraitCall {
                param, method, args, ..
            } => {
                let hint = self.name_hint.take();
                let arg_vals: Vec<String> = args
                    .iter()
                    .map(|a| {
                        let Val::Int(v) = self.eval(a) else {
                            unreachable!("checked: int args")
                        };
                        v
                    })
                    .collect();
                let tr = self.trait_ctx[param.as_str()];
                let m = tr
                    .methods
                    .iter()
                    .find(|mm| mm.name == *method)
                    .expect("checked: trait method exists");
                // Substitution: trait-method params → arguments;
                // `Self::spec` → the abstract binder; `Self` → the model.
                let mut qual: HashMap<String, String> = HashMap::new();
                for sp in &tr.specs {
                    qual.insert(
                        format!("Self::{}", sp.name),
                        format!("{param}_{}", sp.name),
                    );
                }
                qual.insert("Self".to_string(), param.clone());
                let mut argmap: HashMap<String, String> = HashMap::new();
                for (p, v) in m.params.iter().zip(&arg_vals) {
                    argmap.insert(p.name.clone(), v.clone());
                }
                for pre in &m.pres {
                    let text = crate::mono::subst_clause_text(&pre.text, &qual);
                    let goal = substitute(&text, &argmap, None);
                    let ob = self.obligation(
                        &format!(
                            "{}.call_pre.{param}_{method}.{}",
                            self.fname,
                            cslug(pre)
                        ),
                        format!("`pre {}` of `{param}::{method}` must hold", pre.text),
                        e.span,
                        goal,
                    );
                    self.push_obligation(ob);
                }
                let ret_sym = self.hinted_sym("_r", hint);
                match m.ret {
                    Ty::Int(it) => {
                        self.binders.push((ret_sym.clone(), "Int".into()));
                        let range = if let IntTy::TParam(0) = it {
                            format!("{param}.min ≤ {ret_sym} ∧ {ret_sym} ≤ {param}.max")
                        } else {
                            self.r_prop(&ret_sym, it)
                        };
                        self.hyps.push((
                            format!("h_{}_range", ret_sym.trim_start_matches('_')),
                            range,
                        ));
                    }
                    _ => unreachable!("trait methods return integers for now"),
                }
                for post in &m.posts {
                    let text = crate::mono::subst_clause_text(&post.text, &qual);
                    let prop = substitute(&text, &argmap, Some(&ret_sym));
                    self.push_hyp_unique(
                        format!("h_{param}_{method}_post_{}", chslug(post)),
                        format!("({prop})"),
                    );
                    self.context
                        .push(format!("from `{param}::{method}` post: {}", post.text));
                }
                Val::Int(ret_sym)
            }
            ExprKind::MethodCall {
                recv, method, args, ..
            } => {
                let hint = self.name_hint.take();
                let arg_vals: Vec<String> = args
                    .iter()
                    .map(|a| {
                        let Val::Int(v) = self.eval(a) else {
                            unreachable!("checked: int args")
                        };
                        v
                    })
                    .collect();
                let Some(Ty::Class(ci)) = self.var_tys.get(recv.as_str()).copied() else {
                    unreachable!("checked: class receiver")
                };
                let cd = &self.classes[ci];
                let m = cd
                    .methods
                    .iter()
                    .find(|m| m.f.name == *method)
                    .expect("checked: method exists");
                let cur = match self.env.get(recv.as_str()) {
                    Some(Val::Obj(s)) => s.clone(),
                    _ => unreachable!("checked: class value"),
                };
                let mut entry_map = self.class_state_map(cd, &cur);
                for (p, a) in m.f.params.iter().zip(arg_vals.iter()) {
                    entry_map.insert(p.name.clone(), a.clone());
                }
                for pre in &m.f.pres {
                    let goal = substitute(&pre.text, &entry_map, None);
                    let ob = self.obligation(
                        &format!(
                            "{}.call_pre.{}_{}.{}",
                            self.fname,
                            cd.name,
                            method,
                            cslug(pre)
                        ),
                        format!(
                            "`pre {}` of `{}::{method}` must hold at this call",
                            pre.text, cd.name
                        ),
                        e.span,
                        goal,
                    );
                    self.push_obligation(ob);
                }
                // Post-state: fresh for &mut self (invariant re-established),
                // unchanged for &self.
                let final_state = if m.self_kind == SelfKind::Mut {
                    // Post-call state named after the receiver (`m_2`,
                    // `m_3`, ...) — stable and readable in discharges.
                    let b = self.hinted_sym("_obj", Some(recv.clone()));
                    self.binders.push((b.clone(), cd.name.clone()));
                    self.push_class_state_facts(cd, &b);
                    self.push_invariant_hyps(cd, &b);
                    self.env.insert(recv.clone(), Val::Obj(b.clone()));
                    b
                } else {
                    cur.clone()
                };
                // Result symbol.
                let ret_sym = self.hinted_sym("_r", hint);
                match m.f.ret {
                    Ty::Int(it) => {
                        self.binders.push((ret_sym.clone(), "Int".into()));
                        let h = format!("h_{}_range", ret_sym.trim_start_matches('_'));
                        self.hyps.push((h, self.r_prop(&ret_sym, it)));
                    }
                    Ty::Option(_) => {
                        self.binders.push((ret_sym.clone(), "Option Int".into()));
                    }
                    Ty::Bool => {
                        self.binders.push((ret_sym.clone(), "Prop".into()));
                    }
                    Ty::Unit => {}
                    _ => unreachable!(),
                }
                let mut post_map = self.class_state_map(cd, &final_state);
                for (p, a) in m.f.params.iter().zip(arg_vals.iter()) {
                    post_map.insert(p.name.clone(), a.clone());
                }
                // `old self` in the callee's posts is the receiver's
                // pre-call state.
                post_map.insert("_old_self".to_string(), cur.clone());
                for post in m.f.posts.iter() {
                    let text = preprocess_old_self(&post.text);
                    let ret_ref = if m.f.ret == Ty::Unit {
                        None
                    } else {
                        Some(ret_sym.as_str())
                    };
                    let prop = substitute(&text, &post_map, ret_ref);
                    self.push_hyp_unique(
                        format!(
                            "h_{}_{}_post_{}",
                            sanitize(&cd.name),
                            sanitize(method),
                            chslug(post)
                        ),
                        format!("({prop})"),
                    );
                    self.context
                        .push(format!("from `{}::{method}` post: {}", cd.name, post.text));
                }
                match m.f.ret {
                    Ty::Option(_) => Val::Opt(ret_sym),
                    Ty::Unit => Val::Unit,
                    Ty::Bool => Val::Prop(ret_sym),
                    _ => Val::Int(ret_sym),
                }
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
                    let goal = self.r_prop(&value, it);
                    let ob = self.obligation(
                        &format!("{}.overflow.{}", self.fname, slug(self.src(e.span))),
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
                            let goal = self.r_prop(&value, it);
                            let ob = self.obligation(
                                &format!("{}.overflow.{}", self.fname, slug(self.src(e.span))),
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
                                &format!("{}.div_zero.{}", self.fname, slug(self.src(e.span))),
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
                                        self.fname,
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
                let hint = self.name_hint.take();
                let arg_vals: Vec<String> = args
                    .iter()
                    .map(|a| match self.eval(a) {
                        Val::Int(v) | Val::Arr(v) | Val::Obj(v) => v,
                        _ => unreachable!("checked: int/array/class args only"),
                    })
                    .collect();
                let callee_fn = self.fn_map[callee.as_str()];
                let sig = &self.sigs[callee.as_str()];
                // `&C` arguments: the callee assumes the class invariant;
                // the caller owes it here (closes by assumption — class
                // locals are init/method post-states — but it is an
                // obligation, not a trust step; ADR 0010).
                for (p, aval) in sig.params.iter().zip(&arg_vals) {
                    if let Ty::ClassRef(ci) = p.ty {
                        let cd = &self.classes[ci];
                        let map = self.class_state_map(cd, aval);
                        for inv in &cd.invariants {
                            let goal = substitute(&inv.text, &map, None);
                            let ob = self.obligation(
                                &format!(
                                    "{}.borrow_inv.{}.{}",
                                    self.fname,
                                    p.name,
                                    cslug(inv)
                                ),
                                format!(
                                    "invariant of the borrowed `{}` argument",
                                    cd.name
                                ),
                                e.span,
                                goal,
                            );
                            self.push_obligation(ob);
                        }
                    }
                }
                let mut subst_map: HashMap<String, String> = sig
                    .params
                    .iter()
                    .map(|p| p.name.clone())
                    .zip(arg_vals.iter().cloned())
                    .collect();
                // `old p` in the callee's contracts means the argument's
                // pre-call state.
                for p in &sig.params {
                    if matches!(p.ty, Ty::Array(_, Mutability::Mut)) {
                        subst_map.insert(
                            format!("_old_{}", p.name),
                            subst_map[&p.name].clone(),
                        );
                    }
                }

                for pre in &callee_fn.pres {
                    let goal = substitute(&pre.text, &subst_map, None);
                    let ob = self.obligation(
                        &format!("{}.call_pre.{}.{}", self.fname, callee, cslug(pre)),
                        format!("`pre {}` of `{callee}` must hold at this call", pre.text),
                        e.span,
                        goal,
                    );
                    self.push_obligation(ob);
                }

                // Self-recursion: the callee's measure, on the arguments,
                // must be a nonnegative decrease of the current measure.
                if *callee == self.fname {
                    let variant = self.f.variant.as_ref().expect("checked");
                    let vtext = self.preprocess(&variant.text);
                    let callee_measure = substitute(&vtext, &subst_map, None);
                    let caller_measure = self.subst_env(&vtext);
                    let goal = format!(
                        "0 ≤ ({callee_measure}) ∧ ({callee_measure}) < ({caller_measure})"
                    );
                    let ob = self.obligation(
                        &format!("{}.termination.{}", self.fname, cslug(variant)),
                        "recursive call must decrease the function's `variant`".into(),
                        e.span,
                        goal,
                    );
                    self.push_obligation(ob);
                }

                // &mut array arguments come back in a FRESH state — the
                // callee may have mutated them arbitrarily (within its
                // posts). Length and element ranges are preserved by
                // construction (stores are the only mutation); the callee's
                // posts, substituted over the fresh symbol, say the rest.
                // Omitting this havoc asserts posts over the pre-call state
                // and yields inconsistent hypotheses — the soundness bug
                // caught by the quicksort agent on 2026-08-09.
                for (p, arg) in sig.params.iter().zip(args.iter()) {
                    let Ty::Array(elem, Mutability::Mut) = p.ty else {
                        continue;
                    };
                    let ExprKind::Borrow { array, .. } = &arg.kind else {
                        unreachable!("checked: borrow args")
                    };
                    let old_chain = subst_map[&p.name].clone();
                    self.fresh += 1;
                    let b = format!("_arr{}", self.fresh);
                    self.binders.push((b.clone(), "Sable.Seq Int".into()));
                    self.hyps.push((
                        format!("h_{array}_len"),
                        format!("({b}.len) = ({old_chain}.len)"),
                    ));
                    self.hyps.push((
                        format!("h_{array}_elems"),
                        format!(
                            "∀ k, 0 ≤ k → k < {b}.len → {} ≤ {b}.get k ∧ {b}.get k ≤ {}",
                            self.t_min(elem),
                            self.t_max(elem)
                        ),
                    ));
                    self.env.insert(array.clone(), Val::Arr(b.clone()));
                    subst_map.insert(p.name.clone(), b);
                }

                let ret_sym = self.hinted_sym("_r", hint);
                match sig.ret {
                    Ty::Int(ret_it) => {
                        self.binders.push((ret_sym.clone(), "Int".into()));
                        self.hyps.push((
                            format!("h_{}_range", ret_sym.trim_start_matches('_')),
                            self.r_prop(&ret_sym, ret_it),
                        ));
                    }
                    Ty::Option(_) => {
                        self.binders.push((ret_sym.clone(), "Option Int".into()));
                    }
                    Ty::Bool => {
                        self.binders.push((ret_sym.clone(), "Prop".into()));
                    }
                    Ty::Class(ci) => {
                        // A returned class: fresh state with field facts
                        // and the invariant (the callee proved ret_inv;
                        // ADR 0010).
                        let cd = &self.classes[ci];
                        self.binders.push((ret_sym.clone(), cd.name.clone()));
                        self.push_class_state_facts(cd, &ret_sym);
                        self.push_invariant_hyps(cd, &ret_sym);
                    }
                    Ty::Unit => {}
                    _ => unreachable!(),
                }
                for post in callee_fn.posts.iter() {
                    let ret_ref = if sig.ret == Ty::Unit {
                        None
                    } else {
                        Some(ret_sym.as_str())
                    };
                    let text = preprocess_old_params(&post.text, &sig.params);
                    let prop = substitute(&text, &subst_map, ret_ref);
                    self.push_hyp_unique(
                        format!("h_{}_post_{}", sanitize(callee), chslug(post)),
                        format!("({prop})"),
                    );
                    self.context
                        .push(format!("from `{callee}` post: {}", post.text));
                }
                match sig.ret {
                    Ty::Option(_) => Val::Opt(ret_sym),
                    Ty::Unit => Val::Unit,
                    Ty::Bool => Val::Prop(ret_sym),
                    Ty::Class(_) => Val::Obj(ret_sym),
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
                let hname = format!("h_guard_{}", hslug(&guard));
                self.hyps.push((hname, guard));
                let pr = self.eval_prop(rhs);
                self.hyps.truncate(snap);
                let sym = if *op == BinOp::And { "∧" } else { "∨" };
                format!("({pl} {sym} {pr})")
            }
            // Bool-typed calls (and anything else the checker typed Bool).
            _ => match self.eval(e) {
                Val::Prop(p) => p,
                _ => unreachable!("checked: bool-typed expression"),
            },
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
                Val::Int(s) | Val::Arr(s) | Val::Obj(s) if s != name => {
                    Some((name.clone(), s.clone()))
                }
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
                // `old self` in any method clause (posts, but also loop
                // invariants — the frame invariant a self-havocking loop
                // needs) is the entry state.
                if ident == "self" && matches!(self.cctx, Cctx::Method(..)) {
                    out.push_str(&rest[..pos]);
                    out.push_str("_old_self");
                    rest = &after_trim[ident.len()..];
                    continue;
                }
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

    /// Current symbolic self-state (methods only).
    fn self_chain(&self) -> String {
        match self.env.get("self") {
            Some(Val::Obj(s)) => s.clone(),
            _ => unreachable!("checked: self in scope"),
        }
    }

    /// Current symbolic expression for an array field of self.
    fn self_field_str(&self, field: &str) -> String {
        match self.cctx {
            Cctx::Init(_) => match self.env.get(&format!("self.{field}")) {
                Some(Val::Arr(s)) => s.clone(),
                _ => unreachable!("checked: field initialized"),
            },
            Cctx::Method(..) => project_field(&self.self_chain(), field),
            Cctx::None => unreachable!("checked: fields only in members"),
        }
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
        // Template clauses reference `T.min`/`T.max` — and, for
        // bounded parameters, the abstract spec functions (ADR 0009).
        for t in &self.tparams {
            out.push((t.clone(), "Sable.IntModel".into()));
            if let Some(tr) = self.trait_ctx.get(t.as_str()) {
                for sp in &tr.specs {
                    out.push((format!("{t}_{}", sp.name), sp.sig.clone()));
                }
            }
        }
        for p in &self.f.params {
            match p.ty {
                Ty::Int(_) => out.push((p.name.clone(), "Int".into())),
                Ty::Bool => out.push((p.name.clone(), "Bool".into())),
                Ty::ClassRef(ci) => {
                    out.push((p.name.clone(), self.classes[ci].name.clone()))
                }
                Ty::Array(..) => {
                    out.push((p.name.clone(), "Sable.Seq Int".into()));
                    if let Some(entry) = self.mut_arrays.get(&p.name) {
                        out.push((entry.clone(), "Sable.Seq Int".into()));
                    }
                }
                Ty::Option(_) | Ty::Unit | Ty::Class(_) => {}
            }
        }
        match self.cctx {
            Cctx::Init(c) => out.push(("self".to_string(), c.name.clone())),
            Cctx::Method(c, _) => {
                out.push(("self".to_string(), c.name.clone()));
                out.push(("_old_self".to_string(), c.name.clone()));
            }
            Cctx::None => {}
        }
        out
    }

    /// Postcondition obligations for the current path. In post goals,
    /// by-value parameters mean their *entry* values (verbatim binders) but
    /// &mut arrays mean their *final* state — substituted here.
    fn emit_posts(&mut self, result_eq: Option<String>) {
        let f = self.f;
        let mut mut_map: HashMap<String, String> = self
            .mut_arrays
            .keys()
            .filter(|n| n.as_str() != "self")
            .map(|name| (name.clone(), self.arr_str(name)))
            .collect();
        // Class-member exits: the invariant is an obligation at every exit
        // of an init or &mut-self method (design §7 desugaring), and posts
        // speak about the final self-state.
        match self.cctx {
            Cctx::Init(class) => {
                let (_lit, map) = self.init_state_map(class);
                for inv in &class.invariants {
                    let goal = substitute(&inv.text, &map, None);
                    let ob = self.obligation(
                        &format!("{}.inv_exit.{}", self.fname, cslug(inv)),
                        "class invariant must hold when the init returns".into(),
                        inv.span,
                        goal,
                    );
                    self.push_obligation(ob);
                }
                mut_map.extend(map);
            }
            Cctx::Method(class, kind) => {
                let chain = self.self_chain();
                let map = self.class_state_map(class, &chain);
                if kind == SelfKind::Mut {
                    for inv in &class.invariants {
                        let goal = substitute(&inv.text, &map, None);
                        let ob = self.obligation(
                            &format!("{}.inv_exit.{}", self.fname, cslug(inv)),
                            "class invariant must hold when the method returns".into(),
                            inv.span,
                            goal,
                        );
                        self.push_obligation(ob);
                    }
                }
                mut_map.extend(map);
            }
            Cctx::None => {}
        }
        for post in &f.posts {
            let goal = substitute(&self.preprocess(&post.text), &mut_map, None);

            let mut ob = self.obligation(
                &format!("{}.post.{}", self.fname, cslug(post)),
                format!("postcondition of `{}`", self.fname),
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

    /// Push a hypothesis whose name must not shadow an existing one:
    /// on collision, suffix _2, _3, ... (stable: program order).
    /// Model-aware range fact: `T.min ≤ v ∧ v ≤ T.max` for a type
    /// parameter, the concrete bounds otherwise (ADR 0009).
    fn r_prop(&self, value: &str, it: IntTy) -> String {
        if let IntTy::TParam(i) = it {
            let t = &self.tparams[i as usize];
            return format!("{t}.min ≤ {value} ∧ {value} ≤ {t}.max");
        }
        range_prop(value, it)
    }
    fn t_min(&self, it: IntTy) -> String {
        if let IntTy::TParam(i) = it {
            return format!("{}.min", self.tparams[i as usize]);
        }
        it.lean_min()
    }
    fn t_max(&self, it: IntTy) -> String {
        if let IntTy::TParam(i) = it {
            return format!("{}.max", self.tparams[i as usize]);
        }
        it.lean_max()
    }

    /// A binder name for a call/alloc result: the hinted source local
    /// when the result is directly bound (deduped against live binders),
    /// else `{fallback}{fresh}`.
    fn hinted_sym(&mut self, fallback: &str, hint: Option<String>) -> String {
        self.fresh += 1;
        let Some(base) = hint else {
            return format!("{fallback}{}", self.fresh);
        };
        let mut name = base.clone();
        let mut k = 1;
        while self.binders.iter().any(|(b, _)| *b == name) {
            k += 1;
            name = format!("{base}_{k}");
        }
        name
    }

    fn push_hyp_unique(&mut self, base: String, prop: String) {
        let mut name = base.clone();
        let mut n = 1;
        while self.hyps.iter().any(|(h, _)| *h == name) {
            n += 1;
            name = format!("{base}_{n}");
        }
        self.hyps.push((name, prop));
    }

    fn assume_fact(&mut self, prop: &str) {
        self.hyps
            .push((format!("h_fact_{}", hslug(prop)), prop.to_string()));
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
            Stmt::Assign { name, value, .. } => {
                out.insert(name.clone());
                collect_mut_borrows(value, out);
            }
            Stmt::Store { array, .. } => {
                out.insert(array.clone());
            }
            Stmt::FieldAssign { .. } | Stmt::FieldStore { .. } => {
                out.insert("self".to_string());
            }
            Stmt::VarDecl { .. } => {}
            Stmt::ExprStmt(e) => {
                if let ExprKind::MethodCall { recv, .. } = &e.kind {
                    out.insert(recv.clone());
                }
                collect_mut_borrows(e, out);
            }
            Stmt::Decl { init: Some(e), .. } => {
                collect_mut_borrows(e, out);
            }
            Stmt::Return { value: Some(e), .. } => {
                collect_mut_borrows(e, out);
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

/// `&mut a` anywhere inside an expression means `a` may be mutated by a
/// call — conservative marking for loop havoc.
fn collect_mut_borrows(e: &Expr, out: &mut std::collections::HashSet<String>) {
    match &e.kind {
        ExprKind::Borrow { array, mutable } => {
            if *mutable {
                out.insert(array.clone());
            }
        }
        ExprKind::Unary { operand, .. }
        | ExprKind::Widen { arg: operand, .. }
        | ExprKind::Narrow { arg: operand, .. }
        | ExprKind::IsSome { operand }
        | ExprKind::OptValue { operand } => collect_mut_borrows(operand, out),
        ExprKind::TraitCall { args, .. } => {
            for a in args {
                collect_mut_borrows(a, out);
            }
        }
        ExprKind::ClassField { .. } | ExprKind::ClassFieldLen { .. } => {}
        ExprKind::ClassFieldIndex { index, .. } => collect_mut_borrows(index, out),
        ExprKind::SomeE(inner) => collect_mut_borrows(inner, out),
        ExprKind::Binary { lhs, rhs, .. } => {
            collect_mut_borrows(lhs, out);
            collect_mut_borrows(rhs, out);
        }
        ExprKind::Call { args, .. }
        | ExprKind::CtorCall { args, .. }
        | ExprKind::MethodCall { args, .. } => {
            for a in args {
                collect_mut_borrows(a, out);
            }
        }
        ExprKind::AllocArray { len, init, .. } => {
            collect_mut_borrows(len, out);
            collect_mut_borrows(init, out);
        }
        ExprKind::Index { index, .. } | ExprKind::SelfFieldIndex { index, .. } => {
            collect_mut_borrows(index, out)
        }
        ExprKind::ArrayLit(elems) => {
            for el in elems {
                collect_mut_borrows(el, out);
            }
        }
        _ => {}
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

/// Replace `old p` with `_old_p` for each named parameter (caller-side
/// use of a callee's posts about its &mut array params).
fn preprocess_old_params(text: &str, params: &[Param]) -> String {
    let mut out = text.to_string();
    for p in params {
        if !matches!(p.ty, Ty::Array(_, Mutability::Mut)) {
            continue;
        }
        // Token-aware replace of the two-token sequence `old <name>`.
        let needle_variants = [format!("old {}", p.name), format!("old  {}", p.name)];
        for needle in &needle_variants {
            out = out.replace(needle.as_str(), &format!("_old_{}", p.name));
        }
    }
    out
}

/// Replace `old self` with the `_old_self` token (caller-side use of a
/// callee's posts; the Generator's own preprocess handles the member side).
/// `{ X with f := v }.g` — the projection our chains force omega and
/// simp to chew through unless we reduce it here: `v` when `f = g`,
/// `X.g` (recursively) otherwise. Keeps VC goals over stable atoms.
fn project_field(state: &str, field: &str) -> String {
    let mut cur = state.trim();
    loop {
        let Some(body) = cur
            .strip_prefix("{ ")
            .and_then(|s| s.strip_suffix(" }"))
        else {
            break;
        };
        // The ` with ` belonging to THIS level is at brace/paren depth 0.
        let bytes = body.as_bytes();
        let mut depth = 0usize;
        let mut with_at = None;
        for i in 0..bytes.len() {
            match bytes[i] {
                b'{' | b'(' => depth += 1,
                b'}' | b')' => depth = depth.saturating_sub(1),
                b' ' if depth == 0 && body[i..].starts_with(" with ") => {
                    with_at = Some(i);
                    break;
                }
                _ => {}
            }
        }
        let Some(w) = with_at else { break };
        let inner = &body[..w];
        let rest = &body[w + " with ".len()..];
        let Some((fname, value)) = rest.split_once(" := ") else {
            break;
        };
        if fname == field {
            return value.to_string();
        }
        cur = inner.trim();
    }
    format!("({cur}.{field})")
}

/// Obligation-name fragment for a clause: its `#[label]` when present,
/// else the content slug.
fn cslug(c: &crate::scan::Clause) -> String {
    c.label.clone().unwrap_or_else(|| slug(&c.text))
}

/// Hypothesis-name fragment for a clause: label or content hslug.
fn chslug(c: &crate::scan::Clause) -> String {
    c.label.clone().unwrap_or_else(|| hslug(&c.text))
}

fn preprocess_old_self(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(pos) = rest.find("old") {
        let before_ok = pos == 0
            || !rest.as_bytes()[pos - 1].is_ascii_alphanumeric()
                && rest.as_bytes()[pos - 1] != b'_'
                && rest.as_bytes()[pos - 1] != b'.';
        let after = &rest[pos + 3..];
        let after_trim = after.trim_start();
        if before_ok && after_trim.starts_with("self") {
            let after_self = &after_trim[4..];
            let boundary = after_self
                .bytes()
                .next()
                .map_or(true, |b| !b.is_ascii_alphanumeric() && b != b'_');
            if boundary {
                out.push_str(&rest[..pos]);
                out.push_str("_old_self");
                rest = after_self;
                continue;
            }
        }
        out.push_str(&rest[..pos + 3]);
        rest = &rest[pos + 3..];
    }
    out.push_str(rest);
    out
}

pub fn sanitize(name: &str) -> String {
    name.chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect()
}

/// Short content-anchored slug for hypothesis names (design §6: names
/// derive from clause content, never from positional counters, so
/// discharge scripts survive unrelated edits). Lean allows shadowing,
/// so repeated content simply shadows — no counters needed.
fn hslug(text: &str) -> String {
    let full = slug(text);
    full.chars().take(24).collect::<String>().trim_end_matches('_').to_string()
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
