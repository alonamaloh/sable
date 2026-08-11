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
    /// Human context entries with their source spans (span (0,0) when
    /// no source location applies, e.g. template facts).
    pub context: Vec<(String, Span)>,
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

fn lean_field_ty(ty: Ty, classes: &[ClassDecl]) -> String {
    match ty {
        Ty::Int(_) => "Int".into(),
        Ty::Bool => "Bool".into(),
        Ty::Array(..) => "Sable.Seq Int".into(),
        // A class-valued field is a nested structure (ADR 0020).
        Ty::Class(ci) => lean_class_name(&classes[ci].name),
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
                    .map(|f| (f.name.clone(), lean_field_ty(f.ty, &program.classes)))
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
                .map(|f| (f.name.clone(), lean_field_ty(f.ty, &program.classes)))
                .collect(),
            span: c.name_span,
        });
    }

    // Class invariant well-formedness defs: binders are the bare fields.
    for c in program.classes.iter().chain(program.class_templates.iter()) {
        let binders: Vec<(String, String)> = c
            .fields
            .iter()
            .map(|f| (f.name.clone(), lean_field_ty(f.ty, &program.classes)))
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
            entry_states: HashMap::new(),
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
                    kind_desc: format!("`requires` of template `{tname}` at this instantiation"),
                    span: req.span,
                    goal: format!("({})", req.text),
                    binders: Vec::new(),
                    hyps: Vec::new(),
                    context: vec![(format!("instantiated from `{tname}`"), Span::new(0, 0))],
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
            entry_states: HashMap::new(),
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
            generator
                .context
                .push((format!("type parameter {t}"), Span::new(0, 0)));
            if let Some(Some(b)) = f.type_bounds.get(i) {
                let tr = trait_map[b.as_str()];
                for sp in &tr.specs {
                    generator
                        .binders
                        .push((format!("{t}_{}", sp.name), sp.sig.clone()));
                }
                generator.trait_ctx.insert(t.clone(), tr);
                generator
                    .context
                    .push((format!("bound {t}: {b}"), Span::new(0, 0)));
            }
        }
        for req in &f.requires {
            generator
                .hyps
                .push((format!("h_req_{}", chslug(req)), format!("({})", req.text)));
            generator
                .context
                .push((format!("requires {}", req.text), req.line_span));
        }
        generator.run();
    }

    // Class templates (ADR 0009): members verified once against
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
                entry_states: HashMap::new(),
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
                generator
                    .context
                    .push((format!("type parameter {t}"), Span::new(0, 0)));
                if let Some(Some(b)) = c.type_bounds.get(i) {
                    let tr = trait_map[b.as_str()];
                    for sp in &tr.specs {
                        generator
                            .binders
                            .push((format!("{t}_{}", sp.name), sp.sig.clone()));
                    }
                    generator.trait_ctx.insert(t.clone(), tr);
                    generator
                        .context
                        .push((format!("bound {t}: {b}"), Span::new(0, 0)));
                }
            }
            generator.run();
        }
    }
    for c in &program.classes {
        // Template-verified class instances (ADR 0009): the
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
        // deinit bodies are empty (checked); nothing to verify.
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
    /// Symbolic resource *view*: a binder or a transformation of one.
    /// The token it belongs to is not represented — that is the point.
    View(String),
    /// Symbolic raw pointer: a `Sable.RawPtr` expression. It carries no
    /// authority, so it is data like any other (ADR 0026).
    Ptr(String),
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
    /// The body of a lexical exposure. Falling off its end is where the
    /// array is reconstructed, which is why an exposure body may not
    /// `return`: leaving any other way would skip the reconstruction.
    Expose {
        array: &'a str,
        res: &'a str,
        ptr: &'a str,
        mutable: bool,
        kw_span: Span,
        loan: String,
        entry_arr: String,
        rest: Vec<&'a Stmt>,
        outer: Box<Tail<'a>>,
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
    context: Vec<(String, Span)>,
    env: HashMap<String, Val>,
    var_tys: HashMap<String, Ty>,
    /// Params whose clauses have an `old` twin: source name → entry-state
    /// binder (`_old_a`). `&mut [T]` arrays, `&mut C` classes, and the
    /// `self` of a `&mut self` method all live here.
    entry_states: HashMap<String, String>,
    fresh: usize,
    /// Template mode (ADR 0009): the type-parameter names; `TParam(i)`
    /// ranges render through `tparams[i]` as an `IntModel`.
    tparams: Vec<String>,
    /// Template mode: bounded parameter → its trait (for
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
            lean_class_name(&class.name),
            class
                .fields
                .iter()
                .map(|fld| {
                    match self.env.get(&format!("self.{}", fld.name)) {
                        Some(Val::Int(s)) | Some(Val::Arr(s)) | Some(Val::Obj(s)) => {
                            format!("{s}")
                        }
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
            if let Some(Val::Int(s)) | Some(Val::Arr(s)) | Some(Val::Obj(s)) =
                self.env.get(&format!("self.{}", fld.name))
            {
                map.insert(fld.name.clone(), s.clone());
            }
        }
        (literal, map)
    }

    /// The Lean binder type of a local or parameter.
    fn lean_ty_of(&self, name: &str) -> String {
        match self.var_tys.get(name) {
            Some(Ty::Class(ci)) | Some(Ty::ClassRef(ci, _)) => {
                lean_class_name(&self.classes[*ci].name)
            }
            Some(Ty::Res(k)) | Some(Ty::ResRef(k, _)) => k.view_ty().to_string(),
            Some(Ty::Raw(_)) => "Sable.RawPtr".to_string(),
            Some(Ty::Int(_)) => "Int".to_string(),
            Some(Ty::Bool) => "Bool".to_string(),
            _ => "Sable.Seq Int".to_string(),
        }
    }

    /// Everything in scope, as Lean binders — the environment for clause
    /// well-formedness defs (loop annotations, inline asserts).
    fn scope_binders(&self) -> Vec<(String, String)> {
        let mut scope_binders: Vec<(String, String)> = Vec::new();
        for t in &self.tparams {
            scope_binders.push((t.clone(), "Sable.IntModel".to_string()));
            if let Some(tr) = self.trait_ctx.get(t.as_str()) {
                for sp in &tr.specs {
                    scope_binders.push((format!("{t}_{}", sp.name), sp.sig.clone()));
                }
            }
        }
        // Name-sorted: the maps iterate in hash order, and generated
        // files must be byte-stable for content-addressed caching.
        let mut vars: Vec<(String, String)> = self
            .var_tys
            .iter()
            .filter_map(|(name, ty)| match ty {
                Ty::Int(_) => Some((name.clone(), "Int".to_string())),
                Ty::Bool => Some((name.clone(), "Bool".to_string())),
                Ty::Array(..) => Some((name.clone(), "Sable.Seq Int".to_string())),
                Ty::Class(ci) | Ty::ClassRef(ci, _) => {
                    Some((name.clone(), lean_class_name(&self.classes[*ci].name)))
                }
                // A resource binds its *view*; the authority it names is
                // a checker property and appears nowhere in Lean.
                Ty::Res(k) | Ty::ResRef(k, _) => {
                    Some((name.clone(), k.view_ty().to_string()))
                }
                Ty::Raw(_) => Some((name.clone(), "Sable.RawPtr".to_string())),
                Ty::Option(_) | Ty::Unit => None,
            })
            .collect();
        vars.sort();
        scope_binders.extend(vars);
        let mut olds: Vec<(String, String)> = self
            .entry_states
            .iter()
            .filter(|(name, _)| *name != "self") // handled below with the class type
            .map(|(name, entry)| (entry.clone(), self.lean_ty_of(name)))
            .collect();
        olds.sort();
        scope_binders.extend(olds);
        match self.cctx {
            Cctx::Init(c) => scope_binders.push(("self".to_string(), lean_class_name(&c.name))),
            Cctx::Method(c, _) => {
                scope_binders.push(("self".to_string(), lean_class_name(&c.name)));
                scope_binders.push(("_old_self".to_string(), lean_class_name(&c.name)));
            }
            Cctx::None => {}
        }
        scope_binders
    }

    /// Per-field representability facts about a class-state binder —
    /// justified the same way havoc facts are: every store is checked.
    fn push_class_state_facts(&mut self, class: &ClassDecl, binder: &str) {
        // Deduped (`_2` suffixes) like class invariants: two borrowed
        // arguments of the same class must not shadow each other's facts
        // (`cmp(&Nat a, &Nat b)` needs both).
        for fld in &class.fields {
            match fld.ty {
                Ty::Int(it) => {
                    self.push_hyp_unique(
                        format!("h_field_{}_range", fld.name),
                        self.r_prop(&format!("({binder}.{})", fld.name), it),
                    );
                }
                Ty::Array(elem, _) => {
                    let path = format!("({binder}.{})", fld.name);
                    self.push_hyp_unique(
                        format!("h_field_{}_len", fld.name),
                        format!("0 ≤ {path}.len ∧ {path}.len ≤ u64.max"),
                    );
                    self.push_hyp_unique(
                        format!("h_field_{}_elems", fld.name),
                        format!(
                            "∀ k, 0 ≤ k → k < {path}.len → {} ≤ {path}.get k ∧ {path}.get k ≤ {}",
                            self.t_min(elem),
                            self.t_max(elem)
                        ),
                    );
                }
                // A class-valued field carries its own class's facts and
                // invariant, one level down (ADR 0020).
                Ty::Class(ci) => {
                    let inner = self.classes[ci].clone();
                    let path = format!("{binder}.{}", fld.name);
                    self.push_class_state_facts(&inner, &path);
                    self.push_invariant_hyps(&inner, &path);
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
            self.context
                .push((format!("class invariant {}", inv.text), inv.line_span));
        }
    }

    /// A borrowed class argument carries its invariant into the callee, so
    /// the caller owes it here (ADR 0010). Closes by assumption — class
    /// values are init/method post-states — but it is an obligation, not
    /// a trust step.
    fn push_borrow_invs(&mut self, params: &[Param], arg_vals: &[String], span: Span) {
        let borrowed: Vec<(String, usize, String)> = params
            .iter()
            .zip(arg_vals.iter())
            .filter_map(|(p, aval)| match p.ty {
                Ty::ClassRef(aci, _) => Some((p.name.clone(), aci, aval.clone())),
                _ => None,
            })
            .collect();
        for (pname, aci, aval) in borrowed {
            let acd = &self.classes[aci];
            let aname = acd.name.clone();
            let map = self.class_state_map(acd, &aval);
            let goals: Vec<(String, String)> = acd
                .invariants
                .iter()
                .map(|inv| (cslug(inv), substitute(&inv.text, &map, None)))
                .collect();
            for (slug, goal) in goals {
                let ob = self.obligation(
                    &format!("{}.borrow_inv.{pname}.{slug}", self.fname),
                    format!("invariant of the borrowed `{aname}` argument"),
                    span,
                    goal,
                );
                self.push_obligation(ob);
            }
        }
    }

    /// `&mut C` arguments come back in a fresh state — the callee may have
    /// mutated them within its posts, and keeping the pre-call symbol
    /// would assert those posts over storage the callee changed. Assuming
    /// the class invariant of the fresh state is sound for the reason the
    /// `&mut self` receiver rule gives: a callee can only mutate through
    /// the class's own methods, each of which re-establishes it (ADR 0023).
    ///
    /// A `resource &mut R` argument is the same move with a view instead
    /// of a class state, and one difference that matters: what comes back
    /// fresh is the *view*. The token is the same token — that is what
    /// the caller still owns after the call, and what a loop's shape check
    /// preserves across a backedge (ADR 0024).
    ///
    /// Returns param name → post-call state, for the callee's posts.
    fn havoc_mut_borrow_args(&mut self, params: &[Param], args: &[Expr]) -> Vec<(String, String)> {
        enum Target {
            Class(usize),
            View(ResKind),
        }
        let targets: Vec<(String, String, Target)> = params
            .iter()
            .zip(args.iter())
            .filter_map(|(p, arg)| {
                let ExprKind::Borrow { array, .. } = &arg.kind else {
                    return None;
                };
                match p.ty {
                    Ty::ClassRef(aci, Mutability::Mut) => {
                        Some((p.name.clone(), array.clone(), Target::Class(aci)))
                    }
                    Ty::ResRef(k, Mutability::Mut) => {
                        Some((p.name.clone(), array.clone(), Target::View(k)))
                    }
                    _ => None,
                }
            })
            .collect();
        let mut out = Vec::new();
        for (pname, array, target) in targets {
            match target {
                Target::Class(aci) => {
                    let aname = self.classes[aci].name.clone();
                    let b = self.hinted_sym("_obj", Some(array.clone()));
                    self.binders.push((b.clone(), lean_class_name(&aname)));
                    let acd = &self.classes[aci];
                    self.push_class_state_facts(acd, &b);
                    self.push_invariant_hyps(acd, &b);
                    self.env.insert(array, Val::Obj(b.clone()));
                    out.push((pname, b));
                }
                Target::View(k) => {
                    let b = self.hinted_sym("_view", Some(array.clone()));
                    self.binders.push((b.clone(), k.view_ty().into()));
                    for (h, prop) in view_wf_hyps(k, &array, &b) {
                        self.push_hyp_unique(h, prop);
                    }
                    self.env.insert(array, Val::View(b.clone()));
                    out.push((pname, b));
                }
            }
        }
        out
    }

    fn run(&mut self) {
        // Class-member setup: methods get the entry-state binder
        // `_old_self` with field facts and the class invariant assumed
        // (design §7 desugaring); inits start with no self at all.
        if let Cctx::Method(class, _) = self.cctx {
            self.binders
                .push(("_old_self".to_string(), lean_class_name(&class.name)));
            self.entry_states
                .insert("self".to_string(), "_old_self".to_string());
            self.push_class_state_facts(class, "_old_self");
            self.push_invariant_hyps(class, "_old_self");
            self.env
                .insert("self".to_string(), Val::Obj("_old_self".to_string()));
        }
        for p in &self.f.params {
            self.var_tys.insert(p.name.clone(), p.ty);
            match p.ty {
                Ty::Class(ci) | Ty::ClassRef(ci, _) => {
                    // A class borrow (ADR 0010, ADR 0023) or a class
                    // taken by value (ADR 0020): the class value with its
                    // field facts and invariant — the method-entry
                    // treatment, re-aimed. A move and a borrow differ in
                    // the affine discipline and at runtime, not in the
                    // logic.
                    //
                    // A `&mut C`'s binder is the *entry* state `_old_p`,
                    // exactly as a `&mut` array's is: the current state
                    // lives in the symbolic env and is replaced whenever
                    // a `&mut self` method is called on it, and `old p`
                    // in clauses resolves to the binder.
                    let cd = &self.classes[ci];
                    let binder = if p.ty == Ty::ClassRef(ci, Mutability::Mut) {
                        let b = format!("_old_{}", p.name);
                        self.entry_states.insert(p.name.clone(), b.clone());
                        b
                    } else {
                        p.name.clone()
                    };
                    self.binders
                        .push((binder.clone(), lean_class_name(&cd.name)));
                    self.push_class_state_facts(cd, &binder);
                    self.push_invariant_hyps(cd, &binder);
                    self.env.insert(p.name.clone(), Val::Obj(binder));
                }
                // A resource parameter binds its *view* and nothing
                // else: the authority it carries is a checker property,
                // and no generated VC ever mentions it (ADR 0022/0024).
                // A `resource &mut R` follows the `&mut` array rule —
                // entry state as the binder, current state in the env.
                Ty::Res(k) | Ty::ResRef(k, _) => {
                    let binder = if matches!(p.ty, Ty::ResRef(_, Mutability::Mut)) {
                        let b = format!("_old_{}", p.name);
                        self.entry_states.insert(p.name.clone(), b.clone());
                        b
                    } else {
                        p.name.clone()
                    };
                    self.binders.push((binder.clone(), k.view_ty().into()));
                    for (h, prop) in view_wf_hyps(k, &p.name, &binder) {
                        self.hyps.push((h, prop));
                    }
                    self.env.insert(p.name.clone(), Val::View(binder));
                }
                Ty::Raw(_) => {
                    self.binders.push((p.name.clone(), "Sable.RawPtr".into()));
                    self.env.insert(p.name.clone(), Val::Ptr(p.name.clone()));
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
                        self.entry_states.insert(p.name.clone(), binder.clone());
                    }
                    self.env.insert(p.name.clone(), Val::Arr(binder));
                }
                Ty::Option(_) | Ty::Unit => {
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
            self.context
                .push((format!("pre {}", pre.text), pre.line_span));
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
            Ty::Class(ci) => lean_class_name(&self.classes[ci].name),
            // A returned resource is its view: the authority moves, and
            // the logic sees only what the view says (ADR 0024).
            Ty::Res(k) | Ty::ResRef(k, _) => k.view_ty().into(),
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
                    "loop variant must be a nonnegative measure that strictly decreases".into(),
                    variant.span,
                    goal,
                );
                self.push_obligation(ob);
            }
            // A path fell off the end of an exposure body: reconstruct.
            if let Tail::Expose {
                array,
                res,
                ptr,
                mutable,
                kw_span,
                loan,
                entry_arr,
                rest,
                outer,
            } = tail
            {
                let view = self.view_str(res);
                // What "the safe world owns this again" means, stated as
                // obligations rather than assumed: the whole extent came
                // back, and every byte the array needs is present. A
                // split descendant that was never rejoined fails the
                // first; a byte left `uninit` fails the second.
                let ob = self.obligation(
                    &format!("{}.expose.{array}.extent", self.fname),
                    format!("the whole of `{array}` must be owned again here"),
                    *kw_span,
                    format!(
                        "({view}).len = ({entry_arr}).len ∧ ({view}).off = 0 \
                         ∧ ({view}).alloc = {loan}"
                    ),
                );
                self.push_obligation(ob);
                let ob = self.obligation(
                    &format!("{}.expose.{array}.bytes", self.fname),
                    format!(
                        "every byte of `{array}` must be present and in `u8` range here"
                    ),
                    *kw_span,
                    format!("Sable.SpanView.reconstructible ({view})"),
                );
                self.push_obligation(ob);
                if *mutable {
                    // The array becomes what the bytes say. Its element
                    // range is not a separate obligation: it is the other
                    // half of reconstructibility, which the one obligation
                    // above already asked for.
                    let a2 = self.hinted_sym("_arr", Some((*array).to_string()));
                    self.binders.push((a2.clone(), "Sable.Seq Int".into()));
                    self.push_hyp_unique(
                        format!("h_{array}_bytes"),
                        format!("{a2} = Sable.SpanView.toSeq ({view})"),
                    );
                    // Both of these were just proved above; restating them
                    // in the shape every other array fact has is what
                    // keeps downstream automation on familiar ground.
                    self.push_hyp_unique(
                        format!("h_{array}_len"),
                        format!("({a2}.len) = ({entry_arr}.len)"),
                    );
                    self.push_hyp_unique(
                        format!("h_{array}_elems"),
                        format!(
                            "∀ k, 0 ≤ k → k < {a2}.len → 0 ≤ {a2}.get k ∧ {a2}.get k ≤ u8.max"
                        ),
                    );
                    self.env.insert((*array).to_string(), Val::Arr(a2));
                }
                // The loan is over: the bindings go out of scope, which is
                // what the brand rules already guarantee nothing survived.
                self.env.remove(*res);
                self.env.remove(*ptr);
                self.var_tys.remove(*res);
                self.var_tys.remove(*ptr);
                let rest = rest.clone();
                let outer = (**outer).clone();
                self.exec(&rest, &outer);
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
                            | ExprKind::ArrayLit(_)
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
                        | ExprKind::ArrayLit(_)
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
                                        &format!("{}.ret_inv.{}", self.fname, cslug(inv)),
                                        "invariant of the returned class value".to_string(),
                                        value.span,
                                        goal,
                                    );
                                    self.push_obligation(ob);
                                }
                            }
                            format!("(result = {chain})")
                        }
                        // Returning a resource returns its authority; in
                        // the logic that is just its view. There is no
                        // `ret_inv` analogue — a view carries its own
                        // well-formedness, not a user invariant.
                        Val::View(chain) => format!("(result = {chain})"),
                        _ => unreachable!("unit values cannot be returned"),
                    },
                });
                self.emit_posts(result_eq);
            }
            // `unsafe { ... }`: a marker with no verification content of
            // its own. Splice the body into the continuation, which is
            // also why locals declared inside outlive it.
            Stmt::Unsafe { body, .. } => {
                let mut inner: Vec<&Stmt> = body.iter().collect();
                inner.extend_from_slice(rest);
                self.exec(&inner, tail);
            }
            // Lexical exposure. Entry hands the body a span whose bytes
            // are the array's elements, all initialized, at offset 0 of a
            // fresh loan allocation. Exit takes it back: the array becomes
            // what the bytes say, under three obligations that together
            // are what "the safe world owns this again" means (ADR 0026).
            Stmt::Expose {
                kw_span,
                array,
                mutable,
                ptr,
                res,
                body,
                ..
            } => {
                let entry_arr = self.arr_str(array);
                let loan = {
                    self.fresh += 1;
                    format!("_loan{}", self.fresh)
                };
                self.binders.push((loan.clone(), "Int".into()));
                let view = self.hinted_sym("_view", Some(res.clone()));
                self.binders
                    .push((view.clone(), ResKind::RawSpan.view_ty().into()));
                self.push_hyp_unique(
                    format!("h_{res}_entry"),
                    format!("{view} = Sable.SpanView.ofSeq {loan} {entry_arr}"),
                );
                // Reconstructibility is tracked the way array length and
                // element ranges are tracked across a store: assumed
                // because the *operation* establishes it, with the reason
                // recorded. Here the array is a `[u8]`, so every byte
                // starts present and in range — `ofSeq_reconstructible`
                // is the theorem, and the array's own element facts are
                // its premise (ADR 0026).
                self.push_hyp_unique(
                    format!("h_{res}_recon"),
                    format!("Sable.SpanView.reconstructible {view}"),
                );
                self.env.insert(res.clone(), Val::View(view.clone()));
                self.var_tys
                    .insert(res.clone(), Ty::Res(ResKind::RawSpan));
                let p = self.hinted_sym("_ptr", Some(ptr.clone()));
                self.binders.push((p.clone(), "Sable.RawPtr".into()));
                self.push_hyp_unique(
                    format!("h_{ptr}_entry"),
                    format!("{p} = Sable.SpanView.start {view}"),
                );
                self.env.insert(ptr.clone(), Val::Ptr(p));
                self.var_tys.insert(ptr.clone(), Ty::Raw(IntTy::U8));
                // The body runs, then the array is reconstructed. The
                // exposure is a *statement*, so the body's tail is the
                // reconstruction, not the function's continuation — which
                // is why a `return` inside is a checker error.
                let inner: Vec<&Stmt> = body.iter().collect();
                let etail = Tail::Expose {
                    array,
                    res,
                    ptr,
                    mutable: *mutable,
                    kw_span: *kw_span,
                    loan,
                    entry_arr,
                    rest: rest.to_vec(),
                    outer: Box::new(tail.clone()),
                };
                self.exec(&inner, &etail);
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
                        | ExprKind::ArrayLit(_)
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
                            Val::Int(s) | Val::Arr(s) | Val::Obj(s) => s,
                            Val::Prop(p) => format!("(decide {p})"),
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
                        self.env.insert(format!("self.{field}"), Val::Arr(updated));
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

                self.hyps.push((format!("h_path_{}", hslug(&p)), p.clone()));
                self.context.push((format!("path {p}"), cond.span));
                let then_stmts: Vec<&Stmt> =
                    then_block.iter().chain(rest.iter().copied()).collect();
                self.exec(&then_stmts, tail);

                self.env = snap_env;
                self.hyps = snap_hyps.clone();
                self.context = snap_ctx.clone();

                self.hyps
                    .push((format!("h_path_not_{}", hslug(&p)), format!("¬{p}")));
                self.context.push((format!("path ¬{p}"), cond.span));
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
            Stmt::Assert(clause) => {
                // Well-formedness def so a clause that fails to elaborate
                // maps to its own span.
                self.fresh += 1;
                self.out.clause_wfs.push(ClauseWf {
                    def_name: format!("wf_{}_assert{}", sanitize(&self.fname), self.fresh),
                    binders: self.scope_binders(),
                    text: self.preprocess(&clause.text),
                    span: clause.line_span,
                    desc: format!("`assert` in `{}`", self.fname),
                    result_ty: "Prop",
                });
                // The obligation at this point, then the fact downstream —
                // an inline stepping-stone lemma: prove once (automation or
                // a `discharge`), use everywhere after.
                let goal = self.subst_env(&self.preprocess(&clause.text));
                let ob = self.obligation(
                    &format!("{}.assert.{}", self.fname, cslug(clause)),
                    "inline `assert` must hold at this point".into(),
                    clause.line_span,
                    goal.clone(),
                );
                self.push_obligation(ob);
                self.push_hyp_unique(format!("h_assert_{}", chslug(clause)), format!("({goal})"));
                self.context
                    .push((format!("assert {}", clause.text), clause.line_span));
                self.exec(rest, tail);
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
                let scope_binders = self.scope_binders();
                for (i, clause) in invariants
                    .iter()
                    .chain(std::iter::once(variant))
                    .enumerate()
                {
                    self.fresh += 1;
                    self.out.clause_wfs.push(ClauseWf {
                        def_name: format!("wf_{}_loop{}_{}", sanitize(&self.fname), self.fresh, i),
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
                    self.push_hyp_unique(format!("h_inv_{}", chslug(inv)), format!("({text})"));
                    self.context
                        .push((format!("invariant {}", inv.text), inv.line_span));
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
                self.hyps.push((format!("h_path_{}", hslug(&p)), p.clone()));
                self.context.push((format!("path {p}"), cond.span));
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
                self.context.push((format!("path ¬{p}"), cond.span));
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
        {
            // `c.m()` havocs `c` only when `m` takes `&mut self`; a
            // shared-receiver call cannot write, so keeping its facts is
            // both sound and what framing across a loop depends on.
            let classes = self.classes;
            let var_tys = &self.var_tys;
            let cctx_class = match self.cctx {
                Cctx::Init(c) | Cctx::Method(c, _) => Some(c),
                Cctx::None => None,
            };
            let resolver = |recv: &str, method: &str| {
                let cd = match var_tys.get(recv) {
                    Some(Ty::Class(ci)) | Some(Ty::ClassRef(ci, _)) => Some(&classes[*ci]),
                    _ if recv == "self" => cctx_class,
                    _ => None,
                };
                match cd.and_then(|cd| cd.methods.iter().find(|m| m.f.name == method)) {
                    Some(m) => m.self_kind == SelfKind::Mut,
                    // Unresolvable receiver: over-approximate.
                    None => true,
                }
            };
            collect_assigned(body, &mut havoc_set, &resolver);
        }
        // Cascade: symbolic values referring to havocked names die too.
        loop {
            let mut grew = false;
            for (name, val) in &self.env {
                if havoc_set.contains(name) {
                    continue;
                }
                let s = match val {
                    Val::Int(s) | Val::Opt(s) | Val::Arr(s) | Val::Obj(s) | Val::View(s)
                    | Val::Ptr(s) => s,
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
        // hash order (it would diverge between machines in positional
        // binder numbering).
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
            .retain(|note| !havoc_set.iter().any(|h| mentions(&note.0, h)));

        for name in &havoc_names {
            let name = *name;
            // Mid-method self-mutation in a loop: fresh state binder,
            // field facts only (the class invariant is NOT in force
            // mid-method, design §7).
            if name == "self" {
                if let Cctx::Method(class, _) = self.cctx {
                    let b = self.hinted_sym("_self", Some("_self_loop".to_string()));
                    self.binders.push((b.clone(), lean_class_name(&class.name)));
                    self.push_class_state_facts(class, &b);
                    self.env.insert("self".to_string(), Val::Obj(b));
                    continue;
                }
                if let Cctx::Init(class) = self.cctx {
                    // Init loops mutate fields through `self.<field>` env
                    // entries (there is no whole-object state yet): version
                    // each mutated field individually — stores preserve
                    // length and element ranges, mirroring the owned-array
                    // treatment. Leaving the chains in place would let the
                    // pre-loop field value survive the loop (same class of
                    // bug as must-fail/owned_loop_stale).
                    for fld in &class.fields {
                        let key = format!("self.{}", fld.name);
                        match (fld.ty, self.env.get(&key).cloned()) {
                            (Ty::Array(elem, _), Some(Val::Arr(chain))) => {
                                let prior = substitute(&chain, &stale_map, None);
                                self.fresh += 1;
                                let b = format!("_self{}_{}", self.fresh, fld.name);
                                self.binders.push((b.clone(), "Sable.Seq Int".into()));
                                if !havoc_set
                                    .iter()
                                    .any(|h| !stale_map.contains_key(h) && mentions(&prior, h))
                                {
                                    self.push_hyp_unique(
                                        format!("h_self_{}_len", fld.name),
                                        format!("({b}.len) = ({prior}.len)"),
                                    );
                                }
                                self.push_hyp_unique(
                                    format!("h_self_{}_elems", fld.name),
                                    format!(
                                        "∀ k, 0 ≤ k → k < {b}.len → {} ≤ {b}.get k ∧ {b}.get k ≤ {}",
                                        self.t_min(elem),
                                        self.t_max(elem)
                                    ),
                                );
                                self.env.insert(key, Val::Arr(b));
                            }
                            (Ty::Int(it), Some(Val::Int(_))) => {
                                self.fresh += 1;
                                let b = format!("_self{}_{}", self.fresh, fld.name);
                                self.binders.push((b.clone(), "Int".into()));
                                self.push_hyp_unique(
                                    format!("h_self_{}_range", fld.name),
                                    self.r_prop(&b, it),
                                );
                                self.env.insert(key, Val::Int(b));
                            }
                            _ => {}
                        }
                    }
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
                // A loop body called &mut methods on this class value (or,
                // for a local, reassigned it from a call result): fresh
                // state. The invariant held at each method exit (and
                // ret_inv at each returning call), so it is sound to
                // assume at the havoc point. A `&mut C` parameter is the
                // same story: the loop may only rebind its *view*, never
                // the borrow itself.
                Some(Ty::Class(ci)) | Some(Ty::ClassRef(ci, Mutability::Mut)) => {
                    let cd = &self.classes[*ci];
                    self.binders.push((name.clone(), lean_class_name(&cd.name)));
                    self.push_class_state_facts(cd, name);
                    self.push_invariant_hyps(cd, name);
                    self.env.insert(name.clone(), Val::Obj(name.clone()));
                }
                // A loop body transformed this resource's view. The
                // *token* is what the backedge shape check preserves; the
                // view is havocked like any other mutated state, and the
                // loop invariant is what carries it across. Confusing the
                // two would make every loop drop the authority it carries.
                Some(Ty::Res(k)) | Some(Ty::ResRef(k, Mutability::Mut)) => {
                    let k = *k;
                    self.binders.push((name.clone(), k.view_ty().into()));
                    for (h, prop) in view_wf_hyps(k, name, name) {
                        self.hyps.push((h, prop));
                    }
                    self.env.insert(name.clone(), Val::View(name.clone()));
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
                    let entry = self.entry_states[name.as_str()].clone();
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
                    format!("`{}` must hold a value here", self.src_short(e.span)),
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
            // The raw operations. Every one carries a *pointer-names-byte*
            // premise instead of a global provenance predicate: same
            // allocation, offset lands inside the span. The resource
            // borrow beside it is what says the caller may touch it, and
            // that is a checker fact with no VC (ADR 0026).
            ExprKind::RawOp { op, args, .. } => {
                let hint = self.name_hint.take();
                match op {
                    RawOp::Offset => {
                        let Val::Ptr(p) = self.eval(&args[0]) else {
                            unreachable!("checked: raw<u8>")
                        };
                        let Val::Int(d) = self.eval(&args[1]) else {
                            unreachable!("checked: u64")
                        };
                        Val::Ptr(format!("(Sable.RawPtr.add {p} {d})"))
                    }
                    RawOp::Load8 => {
                        let Val::Ptr(p) = self.eval(&args[0]) else {
                            unreachable!("checked: raw<u8>")
                        };
                        let Val::View(m) = self.eval(&args[1]) else {
                            unreachable!("checked: span borrow")
                        };
                        let k = format!("(({p}).off - ({m}).off)");
                        let ob = self.obligation(
                            &format!("{}.load8.{}", self.fname, slug(self.src(e.span))),
                            "`raw_load8` must name a byte of the borrowed span".into(),
                            e.span,
                            format!("Sable.SpanView.namesByte ({m}) ({p}) {k}"),
                        );
                        self.push_obligation(ob);
                        let ob = self.obligation(
                            &format!("{}.load8_init.{}", self.fname, slug(self.src(e.span))),
                            "`raw_load8` must read an initialized byte".into(),
                            e.span,
                            format!("(({m}).bytes.get {k}) ≠ Sable.ByteState.uninit"),
                        );
                        self.push_obligation(ob);
                        let b = self.hinted_sym("_b", hint);
                        self.binders.push((b.clone(), "Int".into()));
                        self.push_hyp_unique(
                            format!("h_{}_byte", b.trim_start_matches('_')),
                            format!(
                                "Sable.ByteState.init {b} = (({m}).bytes.get {k}) \
                                 ∧ 0 ≤ {b} ∧ {b} ≤ u8.max"
                            ),
                        );
                        Val::Int(b)
                    }
                    RawOp::Store8 => {
                        let Val::Ptr(p) = self.eval(&args[0]) else {
                            unreachable!("checked: raw<u8>")
                        };
                        let Val::Int(w) = self.eval(&args[1]) else {
                            unreachable!("checked: u8")
                        };
                        let Val::View(m) = self.eval(&args[2]) else {
                            unreachable!("checked: span borrow")
                        };
                        let k = format!("(({p}).off - ({m}).off)");
                        let ob = self.obligation(
                            &format!("{}.store8.{}", self.fname, slug(self.src(e.span))),
                            "`raw_store8` must name a byte of the borrowed span".into(),
                            e.span,
                            format!("Sable.SpanView.namesByte ({m}) ({p}) {k}"),
                        );
                        self.push_obligation(ob);
                        let ExprKind::Borrow { array: mname, .. } = &args[2].kind else {
                            unreachable!("checked: borrow arg")
                        };
                        let m2 = self.hinted_sym("_view", Some(mname.clone()));
                        self.binders
                            .push((m2.clone(), ResKind::RawSpan.view_ty().into()));
                        // Functional, not axiomatic: the composition
                        // lemmas in the prelude fire on `write`'s shape,
                        // where a conjunction of facts would leave
                        // automation doing case analysis at every store.
                        self.push_hyp_unique(
                            format!("h_{mname}_store"),
                            format!(
                                "{m2} = Sable.SpanView.write ({m}) {k} \
                                 (Sable.ByteState.init {w})"
                            ),
                        );
                        // `write_reconstructible`: the stored value is
                        // `u8`-typed, so its range is already a hypothesis
                        // and the write preserves reconstructibility.
                        self.push_hyp_unique(
                            format!("h_{mname}_recon"),
                            format!("Sable.SpanView.reconstructible {m2}"),
                        );
                        self.env.insert(mname.clone(), Val::View(m2));
                        Val::Unit
                    }
                    RawOp::Copy => {
                        let Val::Ptr(sp) = self.eval(&args[0]) else {
                            unreachable!("checked: raw<u8>")
                        };
                        let Val::Ptr(dp) = self.eval(&args[1]) else {
                            unreachable!("checked: raw<u8>")
                        };
                        let Val::Int(n) = self.eval(&args[2]) else {
                            unreachable!("checked: u64")
                        };
                        let Val::View(sm) = self.eval(&args[3]) else {
                            unreachable!("checked: span borrow")
                        };
                        let Val::View(dm) = self.eval(&args[4]) else {
                            unreachable!("checked: span borrow")
                        };
                        // Both pointers must sit at their span's start and
                        // the range must fit. There is deliberately **no
                        // nonoverlap premise**: the two spans are distinct
                        // affine tokens, and that is what separation is.
                        let ob = self.obligation(
                            &format!("{}.copy.range", self.fname),
                            "`raw_copy_nonoverlapping` must stay inside both spans".into(),
                            e.span,
                            format!(
                                "({sp}).alloc = ({sm}).alloc ∧ ({sp}).off = ({sm}).off \
                                 ∧ ({dp}).alloc = ({dm}).alloc ∧ ({dp}).off = ({dm}).off \
                                 ∧ 0 ≤ {n} ∧ {n} ≤ ({sm}).len ∧ {n} ≤ ({dm}).len"
                            ),
                        );
                        self.push_obligation(ob);
                        let ob = self.obligation(
                            &format!("{}.copy.init", self.fname),
                            "`raw_copy_nonoverlapping` must read initialized bytes".into(),
                            e.span,
                            format!(
                                "∀ k, 0 ≤ k → k < {n} → \
                                 (({sm}).bytes.get k) ≠ Sable.ByteState.uninit"
                            ),
                        );
                        self.push_obligation(ob);
                        let ExprKind::Borrow { array: dname, .. } = &args[4].kind else {
                            unreachable!("checked: borrow arg")
                        };
                        let d2 = self.hinted_sym("_view", Some(dname.clone()));
                        self.binders
                            .push((d2.clone(), ResKind::RawSpan.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{dname}_copy"),
                            format!(
                                "({d2}).alloc = ({dm}).alloc ∧ ({d2}).off = ({dm}).off \
                                 ∧ ({d2}).len = ({dm}).len \
                                 ∧ (∀ k, 0 ≤ k → k < {n} → \
                                     ({d2}).bytes.get k = ({sm}).bytes.get k) \
                                 ∧ (∀ k, {n} ≤ k → ({d2}).bytes.get k = ({dm}).bytes.get k)"
                            ),
                        );
                        // The copied prefix comes from a reconstructible
                        // source and the tail is untouched, so both halves
                        // of the destination stay reconstructible.
                        self.push_hyp_unique(
                            format!("h_{dname}_recon"),
                            format!("Sable.SpanView.reconstructible {d2}"),
                        );
                        self.env.insert(dname.clone(), Val::View(d2));
                        Val::Unit
                    }
                }
            }
            // The sealed resource transformations. Their contracts are
            // generated here rather than written in a prelude, because
            // each states a rule about who owns what and the rules are
            // the compiler's (ADR 0024). Neither touches memory: they
            // redistribute authority, and in the logic that is a fact
            // about how views relate.
            ExprKind::ResOp { op, args, .. } => {
                let hint = self.name_hint.take();
                match op {
                    // `split_off(&mut whole, n)`: the prefix stays, the
                    // suffix leaves. `whole` is rebound to the prefix
                    // view, exactly as any `&mut` argument is rebound.
                    ResOp::SplitOff => {
                        let Val::View(whole) = self.eval(&args[0]) else {
                            unreachable!("checked: span borrow")
                        };
                        let Val::Int(n) = self.eval(&args[1]) else {
                            unreachable!("checked: u64 count")
                        };
                        let goal = format!("0 ≤ {n} ∧ {n} ≤ ({whole}).len");
                        let ob = self.obligation(
                            &format!("{}.split_off.{}", self.fname, slug(&n)),
                            "`split_off` must not carve past the end of the span".into(),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        let ExprKind::Borrow { array, .. } = &args[0].kind else {
                            unreachable!("checked: borrow arg")
                        };
                        let prefix = self.hinted_sym("_view", Some(array.clone()));
                        self.binders
                            .push((prefix.clone(), ResKind::RawSpan.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{array}_prefix"),
                            format!("{prefix} = ({whole}).take {n}"),
                        );
                        self.env.insert(array.clone(), Val::View(prefix.clone()));
                        let suffix = self.hinted_sym("_view", hint);
                        self.binders
                            .push((suffix.clone(), ResKind::RawSpan.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{}_suffix", suffix.trim_start_matches('_')),
                            format!("{suffix} = ({whole}).drop {n}"),
                        );
                        // Carving preserves reconstructibility on both
                        // sides — a sub-span's bytes are a subrange of the
                        // whole's (`take_reconstructible`,
                        // `drop_reconstructible`). Tracking it here is what
                        // keeps a split inside an exposure from turning
                        // into hand proof at the exit (ADR 0026).
                        self.push_hyp_unique(
                            format!("h_{array}_recon"),
                            format!("Sable.SpanView.reconstructible {}", prefix.clone()),
                        );
                        self.push_hyp_unique(
                            format!("h_{}_recon", suffix.trim_start_matches('_')),
                            format!("Sable.SpanView.reconstructible {suffix}"),
                        );
                        Val::View(suffix)
                    }
                    // `join(a, b)`: both tokens are consumed. Adjacency
                    // is a precondition, so a nonadjacent join is a
                    // failed VC and not a checker error — the checker has
                    // no idea where a span sits.
                    ResOp::Join => {
                        let Val::View(a) = self.eval(&args[0]) else {
                            unreachable!("checked: span value")
                        };
                        let Val::View(b) = self.eval(&args[1]) else {
                            unreachable!("checked: span value")
                        };
                        let goal =
                            format!("({a}).alloc = ({b}).alloc ∧ ({a}).off + ({a}).len = ({b}).off");
                        let ob = self.obligation(
                            &format!("{}.join.{}", self.fname, slug(&format!("{a}_{b}"))),
                            "`join` needs two adjacent spans of one allocation".into(),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        let whole = self.hinted_sym("_view", hint);
                        self.binders
                            .push((whole.clone(), ResKind::RawSpan.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{}_join", whole.trim_start_matches('_')),
                            format!("{whole} = ({a}).cat ({b})"),
                        );
                        self.push_hyp_unique(
                            format!("h_{}_recon", whole.trim_start_matches('_')),
                            format!("Sable.SpanView.reconstructible {whole}"),
                        );
                        Val::View(whole)
                    }
                }
            }
            ExprKind::Borrow { array, field, .. } => {
                // Borrowing a resource passes its view along unchanged;
                // what the borrow transfers is authority, and authority
                // is not in the logic (ADR 0024).
                if let Some(Val::View(v)) = self.env.get(array.as_str()) {
                    return Val::View(v.clone());
                }
                let base = match self.env.get(array.as_str()) {
                    Some(Val::Obj(chain)) => Some(chain.clone()),
                    _ => None,
                };
                // A field borrow names the field's own place; whether
                // that place is an object or an array is what the
                // checker recorded on the expression (ADR 0020).
                let place = |v: String| match e.ty {
                    Some(Ty::Array(..)) => Val::Arr(v),
                    _ => Val::Obj(v),
                };
                match (base, field) {
                    // `&x.f` — the borrowed place is the field, not the
                    // base object.
                    (Some(chain), Some(f)) => place(project_field(&chain, f)),
                    (Some(chain), None) => Val::Obj(chain),
                    (None, Some(f)) => {
                        // `&self.f` inside a member.
                        let selfv = match self.env.get("self") {
                            Some(Val::Obj(chain)) => chain.clone(),
                            _ => "self".to_string(),
                        };
                        place(project_field(&selfv, f))
                    }
                    (None, None) => Val::Arr(self.arr_str(array)),
                }
            }
            ExprKind::ArrayLit(elems) => {
                let hint = self.name_hint.take();
                let b = self.hinted_sym("_lit", hint);
                self.binders.push((b.clone(), "Sable.Seq Int".into()));
                let h1 = self.fresh_hyp("h_lit");
                self.hyps.push((h1, format!("({b}.len) = {}", elems.len())));
                for (i, el) in elems.iter().enumerate() {
                    let Val::Int(v) = self.eval(el) else {
                        unreachable!()
                    };
                    let h = self.fresh_hyp("h_lit");
                    self.hyps.push((h, format!("{b}.get {i} = {v}")));
                }
                Val::Arr(b)
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
                self.hyps
                    .push((h2, format!("∀ k, 0 ≤ k → k < {b}.len → {b}.get k = {v0}")));
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
                Cctx::Method(..) => Val::Int(project_field(&self.self_chain(), field)),
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
                // Int args and `&[T]` borrows (shared only — no havoc to
                // apply): the seq chain substitutes for the param name in
                // the init's pres/posts exactly like fn-call array args.
                let arg_vals: Vec<String> = args
                    .iter()
                    .map(|a| match self.eval(a) {
                        // Class args (by value or borrowed) substitute
                        // as their symbolic structure value (ADR 0020).
                        Val::Int(v) | Val::Arr(v) | Val::Obj(v) | Val::View(v) => v,
                        Val::Prop(p) => format!("(decide {p})"),
                        _ => unreachable!("checked: ctor args"),
                    })
                    .collect();
                let cd: &ClassDecl = self.class_map[class.as_str()];
                let ifn = cd
                    .inits
                    .iter()
                    .find(|i| i.name == *init)
                    .expect("checked: init exists");
                let iparams = ifn.params.clone();
                let mut subst_map: HashMap<String, String> = iparams
                    .iter()
                    .map(|p| p.name.clone())
                    .zip(arg_vals.iter().cloned())
                    .collect();
                for p in &iparams {
                    if matches!(
                        p.ty,
                        Ty::ClassRef(_, Mutability::Mut) | Ty::ResRef(_, Mutability::Mut)
                    ) {
                        subst_map.insert(format!("_old_{}", p.name), subst_map[&p.name].clone());
                    }
                }
                self.push_borrow_invs(&iparams, &arg_vals, e.span);
                let cd: &ClassDecl = self.class_map[class.as_str()];
                let ifn = cd
                    .inits
                    .iter()
                    .find(|i| i.name == *init)
                    .expect("checked: init exists");
                for pre in &ifn.pres {
                    let goal = substitute(&pre.text, &subst_map, None);
                    let ob = self.obligation(
                        &format!("{}.call_pre.{}_{}.{}", self.fname, class, init, cslug(pre)),
                        format!(
                            "`pre {}` of `{class}::{init}` must hold at this call",
                            pre.text
                        ),
                        e.span,
                        goal,
                    );
                    self.push_obligation(ob);
                }
                for (pname, fresh) in self.havoc_mut_borrow_args(&iparams, args) {
                    subst_map.insert(pname, fresh);
                }
                let cd: &ClassDecl = self.class_map[class.as_str()];
                let ifn = cd
                    .inits
                    .iter()
                    .find(|i| i.name == *init)
                    .expect("checked: init exists");
                // Fresh post-construction state: the class invariant holds
                // (proved at every init exit) and the init's posts describe it.
                let b = self.hinted_sym("_obj", hint);
                self.binders.push((b.clone(), lean_class_name(&cd.name)));
                self.push_class_state_facts(cd, &b);
                self.push_invariant_hyps(cd, &b);
                let mut post_map = self.class_state_map(cd, &b);
                post_map.extend(subst_map);
                for post in ifn.posts.iter() {
                    let text = preprocess_old_params(&post.text, &iparams);
                    let prop = substitute(&text, &post_map, None);
                    self.push_hyp_unique(
                        format!(
                            "h_{}_{}_post_{}",
                            sanitize(class),
                            sanitize(init),
                            chslug(post)
                        ),
                        format!("({prop})"),
                    );
                    self.context.push((
                        format!("from `{class}::{init}` post: {}", post.text),
                        post.line_span,
                    ));
                }
                Val::Obj(b)
            }
            ExprKind::TraitCall {
                param,
                method,
                args,
                ..
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
                    qual.insert(format!("Self::{}", sp.name), format!("{param}_{}", sp.name));
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
                        &format!("{}.call_pre.{param}_{method}.{}", self.fname, cslug(pre)),
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
                    self.context.push((
                        format!("from `{param}::{method}` post: {}", post.text),
                        post.line_span,
                    ));
                }
                Val::Int(ret_sym)
            }
            ExprKind::MethodCall {
                recv, method, args, ..
            } => {
                let hint = self.name_hint.take();
                let arg_vals: Vec<String> = args
                    .iter()
                    .map(|a| match self.eval(a) {
                        Val::Int(v) | Val::Arr(v) | Val::Obj(v) | Val::View(v) => v,
                        _ => unreachable!("checked: int/array/class/resource args only"),
                    })
                    .collect();
                let Some(Ty::Class(ci) | Ty::ClassRef(ci, _)) =
                    self.var_tys.get(recv.as_str()).copied()
                else {
                    unreachable!("checked: class receiver")
                };
                let cd = &self.classes[ci];
                let m = cd
                    .methods
                    .iter()
                    .find(|m| m.f.name == *method)
                    .expect("checked: method exists");
                let mparams = m.f.params.clone();
                self.push_borrow_invs(&mparams, &arg_vals, e.span);
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
                    self.binders.push((b.clone(), lean_class_name(&cd.name)));
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
                let fresh_args = self.havoc_mut_borrow_args(&mparams, args);
                let cd = &self.classes[ci];
                let m = cd
                    .methods
                    .iter()
                    .find(|m| m.f.name == *method)
                    .expect("checked: method exists");
                let mut post_map = self.class_state_map(cd, &final_state);
                for (p, a) in m.f.params.iter().zip(arg_vals.iter()) {
                    post_map.insert(p.name.clone(), a.clone());
                    // `old p` of a `&mut` argument is its pre-call state.
                    if matches!(
                        p.ty,
                        Ty::ClassRef(_, Mutability::Mut) | Ty::ResRef(_, Mutability::Mut)
                    ) {
                        post_map.insert(format!("_old_{}", p.name), a.clone());
                    }
                }
                for (pname, fresh) in fresh_args {
                    post_map.insert(pname, fresh);
                }
                // `old self` in the callee's posts is the receiver's
                // pre-call state.
                post_map.insert("_old_self".to_string(), cur.clone());
                for post in m.f.posts.iter() {
                    let text =
                        preprocess_old_params(&preprocess_old_self(&post.text), &m.f.params);
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
                    self.context.push((
                        format!("from `{}::{method}` post: {}", cd.name, post.text),
                        post.line_span,
                    ));
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
                                format!("divisor `{}` must be nonzero", self.src_short(rhs.span)),
                                rhs.span,
                                goal.clone(),
                            );
                            self.push_obligation(ob);
                            self.assume_fact(&goal);
                            if it.signed() && *op == BinOp::Div {
                                let goal = format!("¬({l} = {} ∧ {r} = (-1))", it.lean_min());
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
                                    self.assume_fact(&format!("0 ≤ {value} ∧ {value} < {r}"));
                                } else {
                                    self.assume_fact(&format!("0 ≤ {value} ∧ {value} ≤ {l}"));
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
                        Val::Int(v) | Val::Arr(v) | Val::Obj(v) | Val::View(v) => v,
                        _ => unreachable!("checked: int/array/class/resource args only"),
                    })
                    .collect();
                let callee_fn = self.fn_map[callee.as_str()];
                let sig = &self.sigs[callee.as_str()];
                let params = sig.params.clone();
                self.push_borrow_invs(&params, &arg_vals, e.span);
                let sig = &self.sigs[callee.as_str()];
                let mut subst_map: HashMap<String, String> = sig
                    .params
                    .iter()
                    .map(|p| p.name.clone())
                    .zip(arg_vals.iter().cloned())
                    .collect();
                // `old p` in the callee's contracts means the argument's
                // pre-call state.
                for p in &sig.params {
                    if matches!(
                        p.ty,
                        Ty::Array(_, Mutability::Mut)
                            | Ty::ClassRef(_, Mutability::Mut)
                            | Ty::ResRef(_, Mutability::Mut)
                    ) {
                        subst_map.insert(format!("_old_{}", p.name), subst_map[&p.name].clone());
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
                    let goal =
                        format!("0 ≤ ({callee_measure}) ∧ ({callee_measure}) < ({caller_measure})");
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

                for (pname, fresh) in self.havoc_mut_borrow_args(&params, args) {
                    subst_map.insert(pname, fresh);
                }
                let sig = &self.sigs[callee.as_str()];

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
                        self.binders
                            .push((ret_sym.clone(), lean_class_name(&cd.name)));
                        self.push_class_state_facts(cd, &ret_sym);
                        self.push_invariant_hyps(cd, &ret_sym);
                    }
                    // A returned resource: a fresh view binder. The
                    // authority that came with it is the checker's
                    // business, and appears nowhere here (ADR 0024).
                    Ty::Res(k) | Ty::ResRef(k, _) => {
                        self.binders.push((ret_sym.clone(), k.view_ty().into()));
                        for (h, prop) in view_wf_hyps(k, &ret_sym, &ret_sym) {
                            self.push_hyp_unique(h, prop);
                        }
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
                    self.context.push((
                        format!("from `{callee}` post: {}", post.text),
                        post.line_span,
                    ));
                }
                match sig.ret {
                    Ty::Option(_) => Val::Opt(ret_sym),
                    Ty::Unit => Val::Unit,
                    Ty::Bool => Val::Prop(ret_sym),
                    Ty::Class(_) => Val::Obj(ret_sym),
                    Ty::Res(_) | Ty::ResRef(..) => Val::View(ret_sym),
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
                Val::Int(s) | Val::Arr(s) | Val::Obj(s) | Val::View(s) | Val::Ptr(s)
                    if s != name =>
                {
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
                if let Some(entry) = self.entry_states.get(&ident) {
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

    /// Current symbolic view of a resource in scope.
    fn view_str(&self, name: &str) -> String {
        match self.env.get(name) {
            Some(Val::View(s)) => s.clone(),
            _ => unreachable!("checked: resource in scope"),
        }
    }

    /// Current symbolic state of a `&mut` param — an array chain or a
    /// class-state symbol.
    fn state_str(&self, name: &str) -> String {
        match self.env.get(name) {
            Some(Val::Arr(s)) | Some(Val::Obj(s)) | Some(Val::View(s)) => s.clone(),
            _ => unreachable!("checked: &mut param in scope"),
        }
    }

    /// Binders for clause well-formedness defs: source names (plus the
    /// `_old_` twin for `&mut` params, so `old a` elaborates).
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
                Ty::Class(ci) | Ty::ClassRef(ci, _) => {
                    let lean = lean_class_name(&self.classes[ci].name);
                    out.push((p.name.clone(), lean.clone()));
                    if let Some(entry) = self.entry_states.get(&p.name) {
                        out.push((entry.clone(), lean));
                    }
                }
                Ty::Array(..) => {
                    out.push((p.name.clone(), "Sable.Seq Int".into()));
                    if let Some(entry) = self.entry_states.get(&p.name) {
                        out.push((entry.clone(), "Sable.Seq Int".into()));
                    }
                }
                Ty::Raw(_) => out.push((p.name.clone(), "Sable.RawPtr".into())),
                Ty::Res(k) | Ty::ResRef(k, _) => {
                    out.push((p.name.clone(), k.view_ty().into()));
                    if let Some(entry) = self.entry_states.get(&p.name) {
                        out.push((entry.clone(), k.view_ty().into()));
                    }
                }
                Ty::Option(_) | Ty::Unit => {}
            }
        }
        match self.cctx {
            Cctx::Init(c) => out.push(("self".to_string(), lean_class_name(&c.name))),
            Cctx::Method(c, _) => {
                out.push(("self".to_string(), lean_class_name(&c.name)));
                out.push(("_old_self".to_string(), lean_class_name(&c.name)));
            }
            Cctx::None => {}
        }
        out
    }

    /// Postcondition obligations for the current path. In post goals,
    /// by-value parameters mean their *entry* values (verbatim binders) but
    /// `&mut` params mean their *final* state — substituted here.
    fn emit_posts(&mut self, result_eq: Option<String>) {
        let f = self.f;
        let mut mut_map: HashMap<String, String> = self
            .entry_states
            .keys()
            .filter(|n| n.as_str() != "self")
            .map(|name| (name.clone(), self.state_str(name)))
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
                ob.binders
                    .push(("result".to_string(), self.result_lean_ty()));
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

/// Whether a method call mutates its receiver. Answering this needs the
/// class table, which not every caller of `collect_assigned` has; those
/// that do not pass [`ANY_RECV_MUTATES`] and over-approximate.
pub type MutRecv<'a> = &'a dyn std::ops::Fn(&str, &str) -> bool;

/// Conservative resolver: every method call may mutate its receiver.
pub const ANY_RECV_MUTATES: MutRecv<'static> = &|_, _| true;

pub fn collect_assigned(
    stmts: &[Stmt],
    out: &mut std::collections::HashSet<String>,
    mut_recv: MutRecv,
) {
    for s in stmts {
        match s {
            Stmt::Assign { name, value, .. } => {
                out.insert(name.clone());
                collect_mut_borrows(value, out, mut_recv);
            }
            Stmt::Store { array, .. } => {
                out.insert(array.clone());
            }
            Stmt::FieldAssign { .. } | Stmt::FieldStore { .. } => {
                out.insert("self".to_string());
            }
            Stmt::Assert(_) => {}
            Stmt::ExprStmt(e) => {
                collect_mut_borrows(e, out, mut_recv);
            }
            // The initializer of a declaration mutates just as much as
            // the same call in statement position: `u64 t = c.bump();`
            // and `var d = f(&mut b);` both write through their
            // receiver/argument, and omitting them leaves the loop head
            // asserting pre-loop facts about storage the body changed.
            Stmt::Decl { init: Some(e), .. } | Stmt::VarDecl { init: e, .. } => {
                collect_mut_borrows(e, out, mut_recv);
            }
            Stmt::Return { value: Some(e), .. } => {
                collect_mut_borrows(e, out, mut_recv);
            }
            Stmt::If {
                then_block,
                else_block,
                ..
            } => {
                collect_assigned(then_block, out, mut_recv);
                if let Some(eb) = else_block {
                    collect_assigned(eb, out, mut_recv);
                }
            }
            Stmt::While { body, .. } => collect_assigned(body, out, mut_recv),
            _ => {}
        }
    }
}

/// `&mut a` anywhere inside an expression means `a` may be mutated by a
/// call — conservative marking for loop havoc. A `&mut self` method call
/// marks its receiver for the same reason.
fn collect_mut_borrows(e: &Expr, out: &mut std::collections::HashSet<String>, mut_recv: MutRecv) {
    match &e.kind {
        ExprKind::Borrow { array, mutable, .. } => {
            if *mutable {
                out.insert(array.clone());
            }
        }
        ExprKind::Unary { operand, .. }
        | ExprKind::Widen { arg: operand, .. }
        | ExprKind::Narrow { arg: operand, .. }
        | ExprKind::IsSome { operand }
        | ExprKind::OptValue { operand } => collect_mut_borrows(operand, out, mut_recv),
        ExprKind::TraitCall { args, .. } => {
            for a in args {
                collect_mut_borrows(a, out, mut_recv);
            }
        }
        ExprKind::ClassField { .. } | ExprKind::ClassFieldLen { .. } => {}
        ExprKind::ClassFieldIndex { index, .. } => collect_mut_borrows(index, out, mut_recv),
        ExprKind::SomeE(inner) => collect_mut_borrows(inner, out, mut_recv),
        ExprKind::Binary { lhs, rhs, .. } => {
            collect_mut_borrows(lhs, out, mut_recv);
            collect_mut_borrows(rhs, out, mut_recv);
        }
        ExprKind::MethodCall {
            recv, method, args, ..
        } => {
            if mut_recv(recv, method) {
                out.insert(recv.clone());
            }
            for a in args {
                collect_mut_borrows(a, out, mut_recv);
            }
        }
        ExprKind::Call { args, .. } | ExprKind::CtorCall { args, .. } => {
            for a in args {
                collect_mut_borrows(a, out, mut_recv);
            }
        }
        ExprKind::AllocArray { len, init, .. } => {
            collect_mut_borrows(len, out, mut_recv);
            collect_mut_borrows(init, out, mut_recv);
        }
        ExprKind::Index { index, .. } | ExprKind::SelfFieldIndex { index, .. } => {
            collect_mut_borrows(index, out, mut_recv)
        }
        ExprKind::ArrayLit(elems) => {
            for el in elems {
                collect_mut_borrows(el, out, mut_recv);
            }
        }
        _ => {}
    }
}

/// The well-formedness a resource view carries at every binding site.
/// This is the shape of the *value*, not a claim about authority: a span
/// has a nonnegative length its byte sequence covers.
fn view_wf_hyps(kind: ResKind, name: &str, binder: &str) -> Vec<(String, String)> {
    match kind {
        ResKind::RawSpan => vec![(
            format!("h_{name}_wf"),
            format!("0 ≤ {binder}.len ∧ {binder}.len ≤ {binder}.bytes.len"),
        )],
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
            let after_dot = prev == Some(b'.');
            // Dotted keys: init contexts track fields as `self.limbs`
            // env entries, and clauses write `self.limbs.get k` — match
            // the longest dotted name present in the map so the field
            // path substitutes as a unit (atoms then align with the
            // tracked chain, not an unreduced record projection).
            let mut key_end = i;
            if !after_dot {
                let mut j = i;
                while j < bytes.len()
                    && bytes[j] == b'.'
                    && j + 1 < bytes.len()
                    && (bytes[j + 1].is_ascii_alphabetic() || bytes[j + 1] == b'_')
                {
                    let mut k2 = j + 1;
                    while k2 < bytes.len()
                        && (bytes[k2].is_ascii_alphanumeric()
                            || bytes[k2] == b'_'
                            || bytes[k2] == b'\'')
                    {
                        k2 += 1;
                    }
                    if map.contains_key(&text[start..k2]) {
                        key_end = k2;
                    }
                    j = k2;
                }
            }
            let word = if key_end > i {
                &text[start..key_end]
            } else {
                &text[start..i]
            };
            let replacement = if after_dot {
                None
            } else if word == "result" {
                result.map(|r| r.to_string())
            } else {
                map.get(word).cloned()
            };
            match replacement {
                Some(r) => {
                    out.extend_from_slice(format!("({r})").as_bytes());
                    i = key_end.max(i);
                }
                None => out.extend_from_slice(&bytes[start..i]),
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
        if !matches!(
            p.ty,
            Ty::Array(_, Mutability::Mut)
                | Ty::ClassRef(_, Mutability::Mut)
                | Ty::ResRef(_, Mutability::Mut)
        ) {
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
/// The Lean name of a class's structure. Mangled with a fixed prefix so
/// user class names can never collide with Lean root-namespace names
/// (`class Nat` vs core `Nat`). Clauses
/// never name the class, only values, so the verbatim-splice invariant
/// is untouched; the prefix shows up only in compiler-built binder types
/// and `.mk` literals.
pub fn lean_class_name(name: &str) -> String {
    format!("SableC_{name}")
}

fn project_field(state: &str, field: &str) -> String {
    let mut cur = state.trim();
    loop {
        let Some(body) = cur.strip_prefix("{ ").and_then(|s| s.strip_suffix(" }")) else {
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
    full.chars()
        .take(24)
        .collect::<String>()
        .trim_end_matches('_')
        .to_string()
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
    if out.is_empty() { "e".to_string() } else { out }
}
