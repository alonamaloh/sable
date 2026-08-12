//! Verification-condition generation by forward symbolic execution.
//!
//! Program integer values are Lean `Int` expression strings, kept exact by
//! per-operation obligations. Control flow: path-splitting at `if`;
//! `while` is handled by the standard havoc decomposition —
//!
//!   1. prove each invariant at loop entry (goal = invariant text with
//!      variables substituted by their current symbolic values);
//!   2. havoc every variable the condition or body may mutate (fresh binders under their
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
use std::path::Path;

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
    pub records: Vec<RecordEmit>,
    pub clause_wfs: Vec<ClauseWf>,
    pub obligations: Vec<Obligation>,
    /// What this module trusts (ADR 0027). Emitted into the generated
    /// Lean as a comment header so it lands inside the artifact hash: an
    /// artifact must not survive a change to what it trusted, and the
    /// hash is over bytes, so a comment is enough.
    pub trust: TrustManifest,
    /// Formal machine semantics this module uses. Unlike `trust`, these
    /// entries are kernel-checked dependencies rather than audited axioms.
    pub machine: MachineManifest,
}

/// Everything a reader must take on faith to believe this module.
#[derive(Debug, Clone, Default)]
pub struct TrustManifest {
    /// Audited extern contracts, as `(audit id, reason, name)`, sorted.
    pub externs: Vec<(String, String, String)>,
}

/// Profile identity and the exact compiler-sealed intrinsics a module uses.
/// Both land in the generated artifact so semantic changes invalidate cached
/// evidence and build output can name the machine being verified against.
#[derive(Debug, Clone, Default)]
pub struct MachineManifest {
    /// `(stable profile id, content hash of its formal semantics)`.
    pub profiles: Vec<(String, String)>,
    /// Sorted source spellings of used profile operations.
    pub intrinsics: Vec<String>,
}

/// A class as the Lean emitter needs it: `structure name where fields`.
#[derive(Debug, Clone)]
pub struct ClassEmit {
    pub name: String,
    pub fields: Vec<(String, String)>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct RecordEmit {
    pub name: String,
    pub fields: Vec<RecordFieldEmit>,
    pub layout: StorageLayout,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct RecordFieldEmit {
    pub name: String,
    pub lean_ty: String,
    pub layout: String,
    pub offset: i128,
    pub wf: Option<String>,
}

fn collect_uart_dependencies(program: &Program) -> (bool, Vec<String>) {
    fn is_uart_ty(ty: Ty) -> bool {
        matches!(
            ty,
            Ty::Res(ResKind::Uart) | Ty::ResRef(ResKind::Uart, _)
        )
    }

    fn signature_uses_uart(function: &Fn) -> bool {
        is_uart_ty(function.ret) || function.params.iter().any(|param| is_uart_ty(param.ty))
    }

    fn visit_expr(expr: &Expr, uses_uart: &mut bool, used: &mut HashSet<String>) {
        *uses_uart |= expr.ty.is_some_and(is_uart_ty);
        match &expr.kind {
            ExprKind::DeviceOp { op, args, .. } => {
                used.insert(op.name().into());
                for arg in args {
                    visit_expr(arg, uses_uart, used);
                }
            }
            ExprKind::ResOp { op, args, .. } => {
                if *op == ResOp::TestUart {
                    used.insert(op.name().into());
                }
                for arg in args {
                    visit_expr(arg, uses_uart, used);
                }
            }
            ExprKind::Unary { operand, .. }
            | ExprKind::Widen { arg: operand, .. }
            | ExprKind::Narrow { arg: operand, .. }
            | ExprKind::IsSome { operand }
            | ExprKind::OptValue { operand }
            | ExprKind::SomeE(operand) => visit_expr(operand, uses_uart, used),
            ExprKind::Binary { lhs, rhs, .. } => {
                visit_expr(lhs, uses_uart, used);
                visit_expr(rhs, uses_uart, used);
            }
            ExprKind::Call { args, .. }
            | ExprKind::RawOp { args, .. }
            | ExprKind::CtorCall { args, .. }
            | ExprKind::RecordLit { args, .. }
            | ExprKind::TraitCall { args, .. }
            | ExprKind::MethodCall { args, .. }
            | ExprKind::ArrayLit(args) => {
                for arg in args {
                    visit_expr(arg, uses_uart, used);
                }
            }
            ExprKind::Index { index, .. }
            | ExprKind::SelfFieldIndex { index, .. }
            | ExprKind::ClassFieldIndex { index, .. } => {
                visit_expr(index, uses_uart, used)
            }
            ExprKind::AllocArray { len, init, .. } => {
                visit_expr(len, uses_uart, used);
                visit_expr(init, uses_uart, used);
            }
            ExprKind::IntLit(_)
            | ExprKind::BoolLit(_)
            | ExprKind::Var(_)
            | ExprKind::Len { .. }
            | ExprKind::NoneE
            | ExprKind::SelfField { .. }
            | ExprKind::SelfFieldLen { .. }
            | ExprKind::ClassField { .. }
            | ExprKind::RecordField { .. }
            | ExprKind::ClassFieldLen { .. }
            | ExprKind::Borrow { .. } => {}
        }
    }

    fn visit_block(block: &[Stmt], uses_uart: &mut bool, used: &mut HashSet<String>) {
        for stmt in block {
            match stmt {
                Stmt::Decl { ty, init, .. } => {
                    *uses_uart |= is_uart_ty(*ty);
                    if let Some(expr) = init {
                        visit_expr(expr, uses_uart, used);
                    }
                }
                Stmt::Assign { value, .. }
                | Stmt::VarDecl { init: value, .. }
                | Stmt::FieldAssign { value, .. }
                | Stmt::ExprStmt(value) => visit_expr(value, uses_uart, used),
                Stmt::If {
                    cond,
                    then_block,
                    else_block,
                } => {
                    visit_expr(cond, uses_uart, used);
                    visit_block(then_block, uses_uart, used);
                    if let Some(block) = else_block {
                        visit_block(block, uses_uart, used);
                    }
                }
                Stmt::Return { value, .. } => {
                    if let Some(expr) = value {
                        visit_expr(expr, uses_uart, used);
                    }
                }
                Stmt::FieldStore { index, value, .. } | Stmt::Store { index, value, .. } => {
                    visit_expr(index, uses_uart, used);
                    visit_expr(value, uses_uart, used);
                }
                Stmt::While { cond, body, .. } => {
                    visit_expr(cond, uses_uart, used);
                    visit_block(body, uses_uart, used);
                }
                Stmt::Unsafe { body, .. } | Stmt::Expose { body, .. } => {
                    visit_block(body, uses_uart, used);
                }
                Stmt::StaticAlloc { size, .. } | Stmt::SystemAlloc { size, .. } => {
                    visit_expr(size, uses_uart, used);
                }
                Stmt::SystemDealloc {
                    ptr, res, release, ..
                } => {
                    visit_expr(ptr, uses_uart, used);
                    visit_expr(res, uses_uart, used);
                    visit_expr(release, uses_uart, used);
                }
                Stmt::Assert(_) => {}
            }
        }
    }

    fn visit_fn(function: &Fn, uses_uart: &mut bool, used: &mut HashSet<String>) {
        *uses_uart |= signature_uses_uart(function);
        visit_block(&function.body, uses_uart, used);
    }

    let mut uses_uart = false;
    let mut used = HashSet::new();
    for function in &program.fns {
        if function.name.starts_with("test_") {
            // Tests are dynamic-only and generate neither definitions nor
            // obligations. Their bodies (including `test_uart`) therefore do
            // not belong in a verification manifest. The checker also enforces
            // that test signatures are parameterless procedures.
            continue;
        }
        visit_fn(function, &mut uses_uart, &mut used);
    }
    for function in &program.fn_templates {
        visit_fn(function, &mut uses_uart, &mut used);
    }
    for class in program.classes.iter().chain(&program.class_templates) {
        uses_uart |= class.fields.iter().any(|field| is_uart_ty(field.ty));
        for init in &class.inits {
            visit_fn(init, &mut uses_uart, &mut used);
        }
        for method in &class.methods {
            visit_fn(&method.f, &mut uses_uart, &mut used);
        }
        if let Some(body) = &class.deinit {
            visit_block(body, &mut uses_uart, &mut used);
        }
    }
    for implementation in &program.impls {
        for function in &implementation.fns {
            visit_fn(function, &mut uses_uart, &mut used);
        }
    }
    for trait_decl in &program.traits {
        for method in &trait_decl.methods {
            uses_uart |= signature_uses_uart(method);
        }
    }
    let mut used: Vec<String> = used.into_iter().collect();
    used.sort();
    (uses_uart || !used.is_empty(), used)
}

fn lean_field_ty(ty: Ty, classes: &[ClassDecl], records: &[RecordDecl]) -> String {
    match ty {
        Ty::Int(_) => "Int".into(),
        Ty::Bool => "Bool".into(),
        Ty::Array(..) => "Sable.Seq Int".into(),
        // A class-valued field is a nested structure (ADR 0020).
        Ty::Class(ci) => lean_class_name(&classes[ci].name),
        Ty::Record(ri) => lean_record_name(&records[ri].name),
        // A resource field contributes its *view* to the structure. The
        // authority it carries stays a checker property, so the class
        // gains a value and no obligation (ADR 0024/0029).
        Ty::Res(k) | Ty::ResRef(k, _) => lean_res_view_ty(k, records),
        Ty::Raw(_) | Ty::RawRecord(_) => "Sable.RawPtr".into(),
        Ty::Option(_) => "Option Int".into(),
        Ty::OptionRaw(_) => "Option Sable.RawPtr".into(),
        _ => unreachable!("checked: field types"),
    }
}

fn lean_record_field_layout(ty: Ty) -> String {
    match ty {
        Ty::Int(it) => it.lean_layout(),
        Ty::RawRecord(_) | Ty::OptionRaw(_) => "Sable.rawPtr.layout".into(),
        _ => unreachable!("checked: record fields are raw-storable"),
    }
}

fn lean_res_view_ty(kind: ResKind, records: &[RecordDecl]) -> String {
    match kind {
        ResKind::PointsToRecord(ri) => {
            format!("Sable.PointsToView {}", lean_record_name(&records[ri].name))
        }
        ResKind::ResourceMapPointsToRecord(ri) => format!(
            "Sable.ResourceMapView Int (Sable.PointsToView {})",
            lean_record_name(&records[ri].name)
        ),
        _ => kind.view_ty().into(),
    }
}

/// The class-member verification context.
#[derive(Clone, Copy)]
enum Cctx<'a> {
    None,
    Init(&'a ClassDecl),
    Method(&'a ClassDecl, SelfKind),
    /// A destructor. It owns `self` outright and the invariant holds on
    /// entry, but it is **not** re-established at exit: the value ceases to
    /// exist, so there is nothing left to hold it (ADR 0029).
    Deinit(&'a ClassDecl),
}

/// Well-formedness defs for an audited extern's clauses. Its parameters
/// bind exactly as a verified function's do, plus the `_old_` twin of each
/// `&mut` resource so `old mem` elaborates.
fn emit_extern_clause_wfs(
    f: &Fn,
    program: &Program,
    trait_map: &HashMap<&str, &TraitDecl>,
    result: &mut VcResult,
) {
    let _ = trait_map;
    let mut binders: Vec<(String, String)> = Vec::new();
    for p in &f.params {
        match p.ty {
            Ty::Int(_) => binders.push((p.name.clone(), "Int".into())),
            Ty::Bool => binders.push((p.name.clone(), "Bool".into())),
            Ty::Raw(_) | Ty::RawRecord(_) => binders.push((p.name.clone(), "Sable.RawPtr".into())),
            Ty::Res(k) | Ty::ResRef(k, _) => {
                binders.push((p.name.clone(), lean_res_view_ty(k, &program.records)));
                if matches!(p.ty, Ty::ResRef(_, Mutability::Mut)) {
                    binders.push((
                        format!("_old_{}", p.name),
                        lean_res_view_ty(k, &program.records),
                    ));
                }
            }
            Ty::Array(..) => binders.push((p.name.clone(), "Sable.Seq Int".into())),
            Ty::Class(ci) | Ty::ClassRef(ci, _) => {
                binders.push((p.name.clone(), lean_class_name(&program.classes[ci].name)))
            }
            Ty::Record(ri) => {
                binders.push((p.name.clone(), lean_record_name(&program.records[ri].name)))
            }
            Ty::OptionRaw(_) => binders.push((p.name.clone(), "Option Sable.RawPtr".into())),
            Ty::Option(_) | Ty::Unit => {}
        }
    }
    for (i, c) in f.pres.iter().enumerate() {
        result.clause_wfs.push(ClauseWf {
            def_name: format!("wf_{}_pre_{}", sanitize(&f.name), i + 1),
            binders: binders.clone(),
            text: preprocess_old_params(&c.text, &f.params),
            span: c.span,
            desc: format!("`pre` of extern `{}`", f.name),
            result_ty: "Prop",
        });
    }
    let mut post_binders = binders.clone();
    if f.ret != Ty::Unit {
        post_binders.push(("result".to_string(), "Int".to_string()));
    }
    for (i, c) in f.posts.iter().enumerate() {
        result.clause_wfs.push(ClauseWf {
            def_name: format!("wf_{}_post_{}", sanitize(&f.name), i + 1),
            binders: post_binders.clone(),
            text: preprocess_old_params(&c.text, &f.params),
            span: c.span,
            desc: format!("`post` of extern `{}`", f.name),
            result_ty: "Prop",
        });
    }
}

pub fn generate(
    program: &Program,
    sigs: &HashMap<String, FnSig>,
    source: &str,
    repo_root: &Path,
) -> Result<VcResult, String> {
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
    let (uses_uart_profile, uart_intrinsics) = collect_uart_dependencies(program);
    let uart_profile = uses_uart_profile
        .then(|| {
            crate::profile::uart_poll_v1_hash(repo_root).map(|hash| {
                vec![(crate::profile::UART_POLL_V1_ID.into(), hash)]
            })
        })
        .transpose()?;
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
                    .map(|f| {
                        (
                            f.name.clone(),
                            lean_field_ty(f.ty, &program.classes, &program.records),
                        )
                    })
                    .collect(),
                span: c.name_span,
            })
            .collect(),
        records: program
            .records
            .iter()
            .map(|r| RecordEmit {
                name: r.name.clone(),
                fields: r
                    .fields
                    .iter()
                    .map(|f| RecordFieldEmit {
                        name: f.name.clone(),
                        lean_ty: lean_field_ty(f.ty, &program.classes, &program.records),
                        layout: lean_record_field_layout(f.ty),
                        offset: f.offset,
                        wf: match f.ty {
                            Ty::Int(it) => Some(format!(
                                "{} ≤ value.{} ∧ value.{} ≤ {}",
                                it.lean_min(),
                                f.name,
                                f.name,
                                it.lean_max()
                            )),
                            _ => None,
                        },
                    })
                    .collect(),
                layout: r.layout,
                span: r.name_span,
            })
            .collect(),
        clause_wfs: Vec::new(),
        obligations: Vec::new(),
        trust: TrustManifest {
            externs: {
                // Sorted, so the artifact hash is stable across the
                // module map's iteration order. Imports are already in
                // `program.fns` after the flat merge, so a dependency's
                // audited boundary is in the importer's manifest without
                // any union step.
                let mut v: Vec<(String, String, String)> = program
                    .fns
                    .iter()
                    .filter_map(|f| {
                        f.extern_info
                            .as_ref()
                            .map(|x| (x.audit_id.clone(), x.reason.clone(), f.name.clone()))
                    })
                    .collect();
                v.sort();
                v.dedup();
                v
            },
        },
        machine: MachineManifest {
            profiles: uart_profile.unwrap_or_default(),
            intrinsics: uart_intrinsics,
        },
    };

    for c in &program.class_templates {
        result.classes.push(ClassEmit {
            name: c.name.clone(),
            fields: c
                .fields
                .iter()
                .map(|f| {
                    (
                        f.name.clone(),
                        lean_field_ty(f.ty, &program.classes, &program.records),
                    )
                })
                .collect(),
            span: c.name_span,
        });
    }

    // Class invariant well-formedness defs: binders are the bare fields.
    for c in program.classes.iter().chain(program.class_templates.iter()) {
        let binders: Vec<(String, String)> = c
            .fields
            .iter()
            .map(|f| {
                (
                    f.name.clone(),
                    lean_field_ty(f.ty, &program.classes, &program.records),
                )
            })
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
            records: &program.records,
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
        // An extern's contract is *audited*, not proved: there is no body
        // to check it against, so it owes no obligations. Its clauses
        // still get well-formedness defs — a trusted contract that does
        // not even elaborate is not a contract, and the manifest is what
        // makes the trust visible instead (ADR 0027).
        if f.extern_info.is_some() {
            emit_extern_clause_wfs(f, program, &trait_map, &mut result);
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
            records: &program.records,
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
                records: &program.records,
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
    // Destructor bodies are collected first and run after, because the
    // synthesized `Fn` each needs must outlive the generator that reads it.
    let mut deinit_fns: Vec<(Fn, &ClassDecl)> = Vec::new();
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
        // A destructor's body is verified like any other: its statements
        // owe their own obligations. What it does *not* owe is the class
        // invariant at exit (ADR 0029).
        if let Some(body) = &c.deinit {
            if !body.is_empty() {
                let synth = Fn {
                    is_pub: false,
                    extern_info: None,
                    name: "deinit".to_string(),
                    name_span: c.name_span,
                    type_params: Vec::new(),
                    type_bounds: Vec::new(),
                    requires: Vec::new(),
                    from_template: None,
                    params: Vec::new(),
                    ret: Ty::Unit,
                    pres: Vec::new(),
                    posts: Vec::new(),
                    variant: None,
                    body: body.clone(),
                    span: c.span,
                };
                deinit_fns.push((synth, c));
            }
        }
    }
    for (f, c) in &deinit_fns {
        run_one(
            f,
            format!("{}::deinit", c.name),
            Cctx::Deinit(c),
            &mut result,
        );
    }
    Ok(result)
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
    /// Symbolic POD record value. It is structurally represented in Lean
    /// like a class, but has no affine or invariant semantics.
    Record(String),
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
    records: &'a [RecordDecl],
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
                        Some(Val::Int(s)) | Some(Val::Arr(s)) | Some(Val::Obj(s))
                        | Some(Val::View(s)) | Some(Val::Ptr(s)) => format!("{s}"),
                        Some(Val::Prop(p)) => {
                            format!("@decide ({p}) (Classical.propDecidable ({p}))")
                        }
                        _ => "0".to_string(), // unreachable: checked init
                    }
                })
                .collect::<Vec<_>>()
                .join(" ")
        );
        let mut map = HashMap::new();
        map.insert("self".to_string(), literal.clone());
        for fld in &class.fields {
            if let Some(Val::Int(s)) | Some(Val::Arr(s)) | Some(Val::Obj(s)) | Some(Val::View(s))
            | Some(Val::Ptr(s)) = self.env.get(&format!("self.{}", fld.name))
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
            Some(Ty::Record(ri)) => lean_record_name(&self.records[*ri].name),
            Some(Ty::Res(k)) | Some(Ty::ResRef(k, _)) => lean_res_view_ty(*k, self.records),
            Some(Ty::Raw(_)) | Some(Ty::RawRecord(_)) => "Sable.RawPtr".to_string(),
            Some(Ty::OptionRaw(_)) => "Option Sable.RawPtr".to_string(),
            Some(Ty::Option(_)) => "Option Int".to_string(),
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
                Ty::Record(ri) => Some((name.clone(), lean_record_name(&self.records[*ri].name))),
                // A resource binds its *view*; the authority it names is
                // a checker property and appears nowhere in Lean.
                Ty::Res(k) | Ty::ResRef(k, _) => {
                    Some((name.clone(), lean_res_view_ty(*k, self.records)))
                }
                Ty::Raw(_) | Ty::RawRecord(_) => Some((name.clone(), "Sable.RawPtr".to_string())),
                Ty::OptionRaw(_) => Some((name.clone(), "Option Sable.RawPtr".to_string())),
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
            Cctx::Deinit(c) => scope_binders.push(("self".to_string(), lean_class_name(&c.name))),
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
        // The borrowed *place*, which may be a field: `&mut self.w` names
        // `w` inside `self`, so the fresh state has to be written back into
        // the object rather than replacing it. Getting this wrong replaced
        // `self` with a view and lost the whole self-chain.
        let targets: Vec<(String, String, Option<String>, Target)> = params
            .iter()
            .zip(args.iter())
            .filter_map(|(p, arg)| {
                let ExprKind::Borrow { array, field, .. } = &arg.kind else {
                    return None;
                };
                match p.ty {
                    Ty::ClassRef(aci, Mutability::Mut) => Some((
                        p.name.clone(),
                        array.clone(),
                        field.clone(),
                        Target::Class(aci),
                    )),
                    Ty::ResRef(k, Mutability::Mut) => Some((
                        p.name.clone(),
                        array.clone(),
                        field.clone(),
                        Target::View(k),
                    )),
                    _ => None,
                }
            })
            .collect();
        let mut out = Vec::new();
        for (pname, array, field, target) in targets {
            let hint = match &field {
                Some(f) => format!("{array}_{f}"),
                None => array.clone(),
            };
            let b = match target {
                Target::Class(aci) => {
                    let aname = self.classes[aci].name.clone();
                    let b = self.hinted_sym("_obj", Some(hint));
                    self.binders.push((b.clone(), lean_class_name(&aname)));
                    let acd = &self.classes[aci];
                    self.push_class_state_facts(acd, &b);
                    self.push_invariant_hyps(acd, &b);
                    b
                }
                Target::View(k) => {
                    let b = self.hinted_sym("_view", Some(hint));
                    self.binders
                        .push((b.clone(), lean_res_view_ty(k, self.records)));
                    for (h, prop) in view_wf_hyps(k, &array, &b, self.records) {
                        self.push_hyp_unique(h, prop);
                    }
                    b
                }
            };
            match field {
                // A whole place: the name now holds the fresh state.
                None => {
                    let v = match target {
                        Target::Class(_) => Val::Obj(b.clone()),
                        Target::View(_) => Val::View(b.clone()),
                    };
                    self.env.insert(array, v);
                }
                // A field place: write the fresh state back into the base,
                // leaving every sibling where it was.
                Some(f) => {
                    let base = match self.env.get(array.as_str()) {
                        Some(Val::Obj(chain)) => chain.clone(),
                        _ => array.clone(),
                    };
                    self.env
                        .insert(array, Val::Obj(format!("{{ {base} with {f} := {b} }}")));
                }
            }
            out.push((pname, b));
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
        if let Cctx::Deinit(class) = self.cctx {
            // No `_old_self` twin: a destructor has no "after" to compare
            // against, so `old self` would name nothing.
            self.binders
                .push(("self".to_string(), lean_class_name(&class.name)));
            self.push_class_state_facts(class, "self");
            self.push_invariant_hyps(class, "self");
            self.env
                .insert("self".to_string(), Val::Obj("self".to_string()));
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
                Ty::Record(ri) => {
                    let lean_record = lean_record_name(&self.records[ri].name);
                    self.binders.push((p.name.clone(), lean_record.clone()));
                    self.hyps.push((
                        format!("h_{}_wf", p.name),
                        format!("{lean_record}.wf {}", p.name),
                    ));
                    self.env.insert(p.name.clone(), Val::Record(p.name.clone()));
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
                    self.binders
                        .push((binder.clone(), lean_res_view_ty(k, self.records)));
                    for (h, prop) in view_wf_hyps(k, &p.name, &binder, self.records) {
                        self.hyps.push((h, prop));
                    }
                    self.env.insert(p.name.clone(), Val::View(binder));
                }
                Ty::Raw(_) | Ty::RawRecord(_) => {
                    self.binders.push((p.name.clone(), "Sable.RawPtr".into()));
                    self.env.insert(p.name.clone(), Val::Ptr(p.name.clone()));
                }
                Ty::OptionRaw(_) => {
                    self.binders
                        .push((p.name.clone(), "Option Sable.RawPtr".into()));
                    self.env.insert(p.name.clone(), Val::Opt(p.name.clone()));
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
            Ty::OptionRaw(_) => "Option Sable.RawPtr".into(),
            // Bool results are Prop-valued in the logic: posts like
            // `result → P` splice with no coercion noise.
            Ty::Bool => "Prop".into(),
            // A returned class value is its structure (ADR 0010).
            Ty::Class(ci) => lean_class_name(&self.classes[ci].name),
            Ty::Record(ri) => lean_record_name(&self.records[ri].name),
            // A returned resource is its view: the authority moves, and
            // the logic sees only what the view says (ADR 0024).
            Ty::Res(k) | Ty::ResRef(k, _) => lean_res_view_ty(k, self.records),
            Ty::Raw(_) | Ty::RawRecord(_) => "Sable.RawPtr".into(),
            Ty::Unit => "Unit".into(),
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
                    format!("every byte of `{array}` must be present and in `u8` range here"),
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
                        format!("∀ k, 0 ≤ k → k < {a2}.len → 0 ≤ {a2}.get k ∧ {a2}.get k ≤ u8.max"),
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
                            | ExprKind::DeviceOp { .. }
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
                        | ExprKind::DeviceOp { .. }
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
                let result_eq = value.as_ref().map(|value| {
                    match self.eval(value) {
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
                        Val::Record(record) => format!("(result = {record})"),
                        // Returning a resource returns its authority; in
                        // the logic that is just its view. There is no
                        // `ret_inv` analogue — a view carries its own
                        // well-formedness, not a user invariant.
                        Val::View(chain) => format!("(result = {chain})"),
                        // A raw pointer is data: provenance and an offset,
                        // no authority, nothing to re-establish (ADR 0026).
                        Val::Ptr(chain) => format!("(result = {chain})"),
                        _ => unreachable!("unit values cannot be returned"),
                    }
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
            Stmt::StaticAlloc { size, ptr, res, .. } => {
                let Val::Int(n) = self.eval(size) else {
                    unreachable!("checked: u64 size")
                };
                let alloc = self.hinted_sym("_static_alloc", Some(ptr.clone()));
                self.binders.push((alloc.clone(), "Int".into()));
                let view = self.hinted_sym("_view", Some(res.clone()));
                self.binders
                    .push((view.clone(), ResKind::RawSpan.view_ty().into()));
                self.push_hyp_unique(
                    format!("h_{res}_static"),
                    format!("{view} = Sable.SpanView.uninit {alloc} {n}"),
                );
                self.push_hyp_unique(
                    format!("h_{res}_wf"),
                    format!("0 ≤ {view}.len ∧ {view}.len ≤ {view}.bytes.len"),
                );
                self.env.insert(res.clone(), Val::View(view.clone()));
                self.var_tys.insert(res.clone(), Ty::Res(ResKind::RawSpan));
                let p = self.hinted_sym("_ptr", Some(ptr.clone()));
                self.binders.push((p.clone(), "Sable.RawPtr".into()));
                self.push_hyp_unique(
                    format!("h_{ptr}_static"),
                    format!("{p} = Sable.SpanView.start ({view})"),
                );
                self.env.insert(ptr.clone(), Val::Ptr(p));
                self.var_tys.insert(ptr.clone(), Ty::Raw(IntTy::U8));
                self.exec(rest, tail);
            }
            Stmt::SystemAlloc {
                size,
                ptr,
                res,
                release,
                ..
            } => {
                let Val::Int(n) = self.eval(size) else {
                    unreachable!("checked: u64 size")
                };
                let alloc = self.hinted_sym("_system_alloc", Some(ptr.clone()));
                self.binders.push((alloc.clone(), "Int".into()));
                let view = self.hinted_sym("_view", Some(res.clone()));
                self.binders
                    .push((view.clone(), ResKind::RawSpan.view_ty().into()));
                self.push_hyp_unique(
                    format!("h_{res}_system"),
                    format!("{view} = Sable.SpanView.uninit {alloc} {n}"),
                );
                self.push_hyp_unique(
                    format!("h_{res}_wf"),
                    format!("0 ≤ {view}.len ∧ {view}.len ≤ {view}.bytes.len"),
                );
                self.env.insert(res.clone(), Val::View(view.clone()));
                self.var_tys.insert(res.clone(), Ty::Res(ResKind::RawSpan));

                let rel = self.hinted_sym("_release", Some(release.clone()));
                self.binders
                    .push((rel.clone(), ResKind::SystemDealloc.view_ty().into()));
                self.push_hyp_unique(
                    format!("h_{release}_system"),
                    format!("{rel} = {{ alloc := {alloc}, len := {n} }}"),
                );
                self.push_hyp_unique(
                    format!("h_{release}_wf"),
                    format!("Sable.SystemDeallocView.wf {rel}"),
                );
                self.env.insert(release.clone(), Val::View(rel));
                self.var_tys
                    .insert(release.clone(), Ty::Res(ResKind::SystemDealloc));

                let p = self.hinted_sym("_ptr", Some(ptr.clone()));
                self.binders.push((p.clone(), "Sable.RawPtr".into()));
                self.push_hyp_unique(
                    format!("h_{ptr}_system"),
                    format!("{p} = Sable.SpanView.start ({view})"),
                );
                self.env.insert(ptr.clone(), Val::Ptr(p));
                self.var_tys.insert(ptr.clone(), Ty::Raw(IntTy::U8));
                self.exec(rest, tail);
            }
            Stmt::SystemDealloc {
                ptr, res, release, ..
            } => {
                let Val::Ptr(p) = self.eval(ptr) else {
                    unreachable!("checked: raw pointer")
                };
                let Val::View(bytes) = self.eval(res) else {
                    unreachable!("checked: RawSpan")
                };
                let Val::View(rel) = self.eval(release) else {
                    unreachable!("checked: SystemDealloc")
                };
                let goal = format!(
                    "({p}).alloc = ({rel}).alloc ∧ ({p}).off = 0 ∧ \
                     ({bytes}).alloc = ({rel}).alloc ∧ ({bytes}).off = 0 ∧ \
                     ({bytes}).len = ({rel}).len"
                );
                let ob = self.obligation(
                    &format!("{}.system_dealloc", self.fname),
                    "`system_dealloc` needs the base pointer and complete raw allocation authority"
                        .into(),
                    ptr.span,
                    goal.clone(),
                );
                self.push_obligation(ob);
                self.push_hyp_unique("h_system_dealloc".into(), goal);
                self.exec(rest, tail);
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
                self.var_tys.insert(res.clone(), Ty::Res(ResKind::RawSpan));
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
                    // A destructor may write a field too — it owns the
                    // value — and the update is the same chain a method's
                    // is; nothing downstream reads it, since the value is
                    // about to cease to exist.
                    Cctx::Method(..) | Cctx::Deinit(_) => {
                        let vs = match v {
                            // A resource field holds its view, and a raw
                            // field a pointer: both are ordinary values in
                            // the structure, and the authority that came
                            // with the resource is nowhere here (ADR 0024).
                            Val::Int(s)
                            | Val::Arr(s)
                            | Val::Obj(s)
                            | Val::View(s)
                            | Val::Ptr(s) => s,
                            Val::Prop(p) => {
                                format!("@decide ({p}) (Classical.propDecidable ({p}))")
                            }
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
                    Cctx::Method(..) | Cctx::Deinit(_) => {
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
                self.havoc(cond, body);

                // 3. Assume invariants; evaluate the condition once in the
                // havocked context (its VCs must follow from invariants).
                for inv in invariants.iter() {
                    let text = self.subst_env(&self.preprocess(&inv.text));
                    // Deduped: same-slug invariants must not shadow.
                    self.push_hyp_unique(format!("h_inv_{}", chslug(inv)), format!("({text})"));
                    self.context
                        .push((format!("invariant {}", inv.text), inv.line_span));
                }

                // The measure belongs to the loop head, before evaluating
                // the condition. A condition may mutate through `&mut` (or
                // an `&mut self` receiver), and those effects are part of
                // the iteration transition. Capturing the measure after the
                // condition would let a condition raise it and the body
                // restore it forever while still proving a false decrease.
                // Save only the substituted expression here; keep the fresh
                // binder below so existing numbering and branch contexts do
                // not change.
                let vtext = self.subst_env(&self.preprocess(&variant.text));
                let p = self.eval_prop(cond);

                // Full clones — see the If arm.
                let snap_env = self.env.clone();
                let snap_hyps = self.hyps.clone();
                let snap_ctx = self.context.clone();

                // 4. Body path.
                self.fresh += 1;
                let v0 = format!("_v{}", self.fresh);
                self.binders.push((v0.clone(), "Int".into()));
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
    fn havoc(&mut self, cond: &Expr, body: &[Stmt]) {
        let mut havoc_set: HashSet<String> = HashSet::new();
        {
            // `c.m()` havocs `c` only when `m` takes `&mut self`; a
            // shared-receiver call cannot write, so keeping its facts is
            // both sound and what framing across a loop depends on.
            let classes = self.classes;
            let var_tys = &self.var_tys;
            let cctx_class = match self.cctx {
                Cctx::Init(c) | Cctx::Method(c, _) | Cctx::Deinit(c) => Some(c),
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
            // The condition is executed once per iteration and may call a
            // mutating method or pass an explicit `&mut` argument. It belongs
            // to the loop transition just as much as the lexical body does.
            collect_mut_borrows(cond, &mut havoc_set, &resolver);
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
                    Val::Int(s)
                    | Val::Opt(s)
                    | Val::Arr(s)
                    | Val::Obj(s)
                    | Val::Record(s)
                    | Val::View(s)
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
                    self.binders
                        .push((name.clone(), lean_res_view_ty(k, self.records)));
                    for (h, prop) in view_wf_hyps(k, name, name, self.records) {
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
                let value = format!("(({o}).value)");
                match e.ty {
                    Some(Ty::RawRecord(_)) => Val::Ptr(value),
                    _ => Val::Int(value),
                }
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
            ExprKind::SomeE(inner) => {
                let value = match self.eval(inner) {
                    Val::Int(v) | Val::Ptr(v) => v,
                    _ => unreachable!("checked: option payload"),
                };
                Val::Opt(format!("some ({value})"))
            }
            ExprKind::NoneE => Val::Opt("none".into()),
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
                    RawOp::CastRecord(_) => {
                        let Val::Ptr(p) = self.eval(&args[0]) else {
                            unreachable!("checked: raw<u8>")
                        };
                        Val::Ptr(p)
                    }
                    RawOp::PointerOffsetRecord(_) => {
                        let Val::Ptr(p) = self.eval(&args[0]) else {
                            unreachable!("checked: raw record pointer")
                        };
                        let value = format!("({p}).off");
                        let goal = range_prop(&value, IntTy::U64);
                        let ob = self.obligation(
                            &format!("{}.pointer.offset", self.fname),
                            "a record pointer's arena offset must fit `u64`".into(),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        Val::Int(value)
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
                    RawOp::IntoCellU64 => {
                        let Val::Ptr(p) = self.eval(&args[0]) else {
                            unreachable!("checked: raw<u8>")
                        };
                        let Val::View(m) = self.eval(&args[1]) else {
                            unreachable!("checked: span value")
                        };
                        let leased = matches!(
                            vc_resource_kind(&self.var_tys, &args[1]),
                            Some(ResKind::BlockLease)
                        );
                        let bytes = if leased {
                            format!("({m}).span")
                        } else {
                            m.clone()
                        };
                        let layout = IntTy::U64.lean_layout();
                        let goal = format!(
                            "({p}).alloc = ({bytes}).alloc ∧ ({p}).off = ({bytes}).off \
                             ∧ ({bytes}).len = ({layout}).size \
                             ∧ ({bytes}).off % ({layout}).align = 0"
                        );
                        let ob = self.obligation(
                            &format!("{}.cell_u64.from_raw", self.fname),
                            "`raw_into_cell_u64` needs an aligned eight-byte raw extent".into(),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        let c = self.hinted_sym("_cell", hint);
                        let result_kind = if leased {
                            ResKind::LeasedPointsToU64
                        } else {
                            ResKind::PointsToU64
                        };
                        self.binders.push((c.clone(), result_kind.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{}_cell", c.trim_start_matches('_')),
                            if leased {
                                format!("{c} = Sable.BlockLeaseView.toCellU64 ({m})")
                            } else {
                                format!("{c} = Sable.SpanView.toCellU64 ({m})")
                            },
                        );
                        Val::View(c)
                    }
                    RawOp::FromCellU64 => {
                        let Val::Ptr(p) = self.eval(&args[0]) else {
                            unreachable!("checked: raw<u8>")
                        };
                        let Val::View(c) = self.eval(&args[1]) else {
                            unreachable!("checked: cell value")
                        };
                        let leased = matches!(
                            vc_resource_kind(&self.var_tys, &args[1]),
                            Some(ResKind::LeasedPointsToU64)
                        );
                        let cell = if leased {
                            format!("({c}).cell")
                        } else {
                            c.clone()
                        };
                        let goal = format!(
                            "Sable.PointsToView.names ({cell}) ({p}) \
                             ∧ ({cell}).state = Sable.CellState.uninit"
                        );
                        let ob = self.obligation(
                            &format!("{}.cell_u64.to_raw", self.fname),
                            "`raw_from_cell_u64` needs an uninitialized cell at this pointer"
                                .into(),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        let m = self.hinted_sym("_view", hint);
                        let result_kind = if leased {
                            ResKind::BlockLease
                        } else {
                            ResKind::RawSpan
                        };
                        self.binders.push((m.clone(), result_kind.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{}_span", m.trim_start_matches('_')),
                            if leased {
                                format!("{m} = Sable.LeasedPointsToU64View.toLease ({c})")
                            } else {
                                format!("{m} = Sable.PointsToView.toSpanU64 ({c})")
                            },
                        );
                        if !leased {
                            self.push_hyp_unique(
                                format!("h_{}_recon", m.trim_start_matches('_')),
                                format!("Sable.SpanView.reconstructible {m}"),
                            );
                        }
                        Val::View(m)
                    }
                    RawOp::CellInitU64 => {
                        let Val::Ptr(p) = self.eval(&args[0]) else {
                            unreachable!("checked: raw<u8>")
                        };
                        let Val::Int(w) = self.eval(&args[1]) else {
                            unreachable!("checked: u64")
                        };
                        let Val::View(c) = self.eval(&args[2]) else {
                            unreachable!("checked: cell borrow")
                        };
                        let leased = matches!(
                            vc_resource_kind(&self.var_tys, &args[2]),
                            Some(ResKind::LeasedPointsToU64)
                        );
                        let cell = if leased {
                            format!("({c}).cell")
                        } else {
                            c.clone()
                        };
                        let goal = format!(
                            "Sable.PointsToView.names ({cell}) ({p}) \
                             ∧ ({cell}).state = Sable.CellState.uninit"
                        );
                        let ob = self.obligation(
                            &format!("{}.cell_u64.init", self.fname),
                            "`raw_cell_init_u64` needs an uninitialized cell at this pointer"
                                .into(),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        let ExprKind::Borrow { array: name, .. } = &args[2].kind else {
                            unreachable!("checked: borrow arg")
                        };
                        let c2 = self.hinted_sym("_cell", Some(name.clone()));
                        let kind = if leased {
                            ResKind::LeasedPointsToU64
                        } else {
                            ResKind::PointsToU64
                        };
                        self.binders.push((c2.clone(), kind.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{name}_init"),
                            if leased {
                                format!("{c2} = Sable.LeasedPointsToU64View.put ({c}) {w}")
                            } else {
                                format!("{c2} = Sable.PointsToView.put ({c}) {w}")
                            },
                        );
                        self.env.insert(name.clone(), Val::View(c2));
                        Val::Unit
                    }
                    RawOp::CellReadU64 | RawOp::CellTakeU64 => {
                        let Val::Ptr(p) = self.eval(&args[0]) else {
                            unreachable!("checked: raw<u8>")
                        };
                        let Val::View(c) = self.eval(&args[1]) else {
                            unreachable!("checked: cell borrow")
                        };
                        let leased = matches!(
                            vc_resource_kind(&self.var_tys, &args[1]),
                            Some(ResKind::LeasedPointsToU64)
                        );
                        let cell = if leased {
                            format!("({c}).cell")
                        } else {
                            c.clone()
                        };
                        let goal = format!(
                            "Sable.PointsToView.names ({cell}) ({p}) \
                             ∧ ({cell}).state ≠ Sable.CellState.uninit"
                        );
                        let opname = if matches!(op, RawOp::CellReadU64) {
                            "read"
                        } else {
                            "take"
                        };
                        let ob = self.obligation(
                            &format!("{}.cell_u64.{opname}", self.fname),
                            format!(
                                "`raw_cell_{opname}_u64` needs an initialized cell at this pointer"
                            ),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        let value = self.hinted_sym("_value", hint);
                        self.binders.push((value.clone(), "Int".into()));
                        self.push_hyp_unique(
                            format!("h_{}_cell_value", value.trim_start_matches('_')),
                            format!("({cell}).state = Sable.CellState.init {value}"),
                        );
                        self.push_hyp_unique(
                            format!("h_{}_range", value.trim_start_matches('_')),
                            range_prop(&value, IntTy::U64),
                        );
                        if matches!(op, RawOp::CellTakeU64) {
                            let ExprKind::Borrow { array: name, .. } = &args[1].kind else {
                                unreachable!("checked: borrow arg")
                            };
                            let c2 = self.hinted_sym("_cell", Some(name.clone()));
                            let kind = if leased {
                                ResKind::LeasedPointsToU64
                            } else {
                                ResKind::PointsToU64
                            };
                            self.binders.push((c2.clone(), kind.view_ty().into()));
                            self.push_hyp_unique(
                                format!("h_{name}_take"),
                                if leased {
                                    format!("{c2} = Sable.LeasedPointsToU64View.clear ({c})")
                                } else {
                                    format!("{c2} = Sable.PointsToView.clear ({c})")
                                },
                            );
                            self.env.insert(name.clone(), Val::View(c2));
                        }
                        Val::Int(value)
                    }
                    RawOp::CellDropU64 => {
                        let Val::Ptr(p) = self.eval(&args[0]) else {
                            unreachable!("checked: raw<u8>")
                        };
                        let Val::View(c) = self.eval(&args[1]) else {
                            unreachable!("checked: cell borrow")
                        };
                        let leased = matches!(
                            vc_resource_kind(&self.var_tys, &args[1]),
                            Some(ResKind::LeasedPointsToU64)
                        );
                        let cell = if leased {
                            format!("({c}).cell")
                        } else {
                            c.clone()
                        };
                        let goal = format!(
                            "Sable.PointsToView.names ({cell}) ({p}) \
                             ∧ ({cell}).state ≠ Sable.CellState.uninit"
                        );
                        let ob = self.obligation(
                            &format!("{}.cell_u64.drop", self.fname),
                            "`raw_cell_drop_u64` needs an initialized cell at this pointer".into(),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        let ExprKind::Borrow { array: name, .. } = &args[1].kind else {
                            unreachable!("checked: borrow arg")
                        };
                        let c2 = self.hinted_sym("_cell", Some(name.clone()));
                        let kind = if leased {
                            ResKind::LeasedPointsToU64
                        } else {
                            ResKind::PointsToU64
                        };
                        self.binders.push((c2.clone(), kind.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{name}_drop"),
                            if leased {
                                format!("{c2} = Sable.LeasedPointsToU64View.clear ({c})")
                            } else {
                                format!("{c2} = Sable.PointsToView.clear ({c})")
                            },
                        );
                        self.env.insert(name.clone(), Val::View(c2));
                        Val::Unit
                    }
                    RawOp::IntoCellRecord(ri) => {
                        let Val::Ptr(p) = self.eval(&args[0]) else {
                            unreachable!("checked: raw record pointer")
                        };
                        let Val::View(bytes) = self.eval(&args[1]) else {
                            unreachable!("checked: raw span value")
                        };
                        let record = lean_record_name(&self.records[*ri].name);
                        let layout = format!("{record}.layout");
                        let goal = format!(
                            "({p}).alloc = ({bytes}).alloc ∧ ({p}).off = ({bytes}).off \
                             ∧ ({bytes}).len = ({layout}).size \
                             ∧ ({bytes}).off % ({layout}).align = 0"
                        );
                        let ob = self.obligation(
                            &format!("{}.record.from_raw", self.fname),
                            format!(
                                "`raw_into_cell<{}>` needs one complete aligned record extent",
                                self.records[*ri].name
                            ),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        let cell = self.hinted_sym("_cell", hint);
                        let kind = ResKind::PointsToRecord(*ri);
                        self.binders
                            .push((cell.clone(), lean_res_view_ty(kind, self.records)));
                        self.push_hyp_unique(
                            format!("h_{}_cell", cell.trim_start_matches('_')),
                            format!("{cell} = {record}.fromSpan ({bytes})"),
                        );
                        self.push_hyp_unique(
                            format!("h_{}_wf", cell.trim_start_matches('_')),
                            format!("{record}.cellWf {cell}"),
                        );
                        Val::View(cell)
                    }
                    RawOp::FromCellRecord(ri) => {
                        let Val::Ptr(p) = self.eval(&args[0]) else {
                            unreachable!("checked: raw record pointer")
                        };
                        let Val::View(cell) = self.eval(&args[1]) else {
                            unreachable!("checked: record cell value")
                        };
                        let record = lean_record_name(&self.records[*ri].name);
                        let goal = format!(
                            "Sable.PointsToView.names ({cell}) ({p}) ∧ \
                             ({cell}).state = Sable.CellState.uninit"
                        );
                        let ob = self.obligation(
                            &format!("{}.record.to_raw", self.fname),
                            format!(
                                "`raw_from_cell<{}>` needs a matching uninitialized cell",
                                self.records[*ri].name
                            ),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        let bytes = self.hinted_sym("_view", hint);
                        self.binders
                            .push((bytes.clone(), ResKind::RawSpan.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{}_span", bytes.trim_start_matches('_')),
                            format!("{bytes} = {record}.toSpan ({cell})"),
                        );
                        self.push_hyp_unique(
                            format!("h_{}_recon", bytes.trim_start_matches('_')),
                            format!("Sable.SpanView.reconstructible {bytes}"),
                        );
                        Val::View(bytes)
                    }
                    RawOp::CellInitRecord(ri) => {
                        let Val::Ptr(p) = self.eval(&args[0]) else {
                            unreachable!("checked: raw record pointer")
                        };
                        let Val::Record(value) = self.eval(&args[1]) else {
                            unreachable!("checked: record value")
                        };
                        let Val::View(cell) = self.eval(&args[2]) else {
                            unreachable!("checked: record cell borrow")
                        };
                        let record = lean_record_name(&self.records[*ri].name);
                        let goal = format!(
                            "Sable.PointsToView.names ({cell}) ({p}) ∧ \
                             ({cell}).state = Sable.CellState.uninit"
                        );
                        let ob = self.obligation(
                            &format!("{}.record.init", self.fname),
                            format!(
                                "`raw_cell_init<{}>` needs a matching uninitialized cell",
                                self.records[*ri].name
                            ),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        let ExprKind::Borrow { array: name, .. } = &args[2].kind else {
                            unreachable!("checked: record cell borrow")
                        };
                        let next = self.hinted_sym("_cell", Some(name.clone()));
                        self.binders.push((
                            next.clone(),
                            lean_res_view_ty(ResKind::PointsToRecord(*ri), self.records),
                        ));
                        self.push_hyp_unique(
                            format!("h_{name}_init"),
                            format!("{next} = Sable.PointsToView.put ({cell}) ({value})"),
                        );
                        self.push_hyp_unique(
                            format!("h_{name}_wf"),
                            format!("{record}.cellWf {next}"),
                        );
                        self.push_hyp_unique(
                            format!("h_{name}_names"),
                            format!("Sable.PointsToView.names ({next}) ({p})"),
                        );
                        self.env.insert(name.clone(), Val::View(next));
                        Val::Unit
                    }
                    RawOp::CellReadRecord(ri) | RawOp::CellTakeRecord(ri) => {
                        let Val::Ptr(p) = self.eval(&args[0]) else {
                            unreachable!("checked: raw record pointer")
                        };
                        let Val::View(cell) = self.eval(&args[1]) else {
                            unreachable!("checked: record cell borrow")
                        };
                        let taking = matches!(op, RawOp::CellTakeRecord(_));
                        let operation = if taking { "take" } else { "read" };
                        let goal = format!(
                            "Sable.PointsToView.names ({cell}) ({p}) ∧ \
                             ({cell}).state ≠ Sable.CellState.uninit"
                        );
                        let ob = self.obligation(
                            &format!("{}.record.{operation}", self.fname),
                            format!(
                                "`raw_cell_{operation}<{}>` needs a matching initialized cell",
                                self.records[*ri].name
                            ),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        let value = self.hinted_sym("_record", hint);
                        let record = lean_record_name(&self.records[*ri].name);
                        self.binders.push((value.clone(), record.clone()));
                        self.push_hyp_unique(
                            format!("h_{}_cell_value", value.trim_start_matches('_')),
                            format!("({cell}).state = Sable.CellState.init ({value})"),
                        );
                        self.push_hyp_unique(
                            format!("h_{}_wf", value.trim_start_matches('_')),
                            format!("{record}.wf {value}"),
                        );
                        if taking {
                            let ExprKind::Borrow { array: name, .. } = &args[1].kind else {
                                unreachable!("checked: record cell borrow")
                            };
                            let next = self.hinted_sym("_cell", Some(name.clone()));
                            self.binders.push((
                                next.clone(),
                                lean_res_view_ty(ResKind::PointsToRecord(*ri), self.records),
                            ));
                            self.push_hyp_unique(
                                format!("h_{name}_take"),
                                format!("{next} = Sable.PointsToView.clear ({cell})"),
                            );
                            self.push_hyp_unique(
                                format!("h_{name}_wf"),
                                format!("{record}.cellWf {next}"),
                            );
                            self.push_hyp_unique(
                                format!("h_{name}_names"),
                                format!("Sable.PointsToView.names ({next}) ({p})"),
                            );
                            self.env.insert(name.clone(), Val::View(next));
                        }
                        Val::Record(value)
                    }
                    RawOp::CellDropRecord(ri) => {
                        let Val::Ptr(p) = self.eval(&args[0]) else {
                            unreachable!("checked: raw record pointer")
                        };
                        let Val::View(cell) = self.eval(&args[1]) else {
                            unreachable!("checked: record cell borrow")
                        };
                        let goal = format!(
                            "Sable.PointsToView.names ({cell}) ({p}) ∧ \
                             ({cell}).state ≠ Sable.CellState.uninit"
                        );
                        let ob = self.obligation(
                            &format!("{}.record.drop", self.fname),
                            format!(
                                "`raw_cell_drop<{}>` needs a matching initialized cell",
                                self.records[*ri].name
                            ),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        let ExprKind::Borrow { array: name, .. } = &args[1].kind else {
                            unreachable!("checked: record cell borrow")
                        };
                        let next = self.hinted_sym("_cell", Some(name.clone()));
                        let record = lean_record_name(&self.records[*ri].name);
                        self.binders.push((
                            next.clone(),
                            lean_res_view_ty(ResKind::PointsToRecord(*ri), self.records),
                        ));
                        self.push_hyp_unique(
                            format!("h_{name}_drop"),
                            format!("{next} = Sable.PointsToView.clear ({cell})"),
                        );
                        self.push_hyp_unique(
                            format!("h_{name}_wf"),
                            format!("{record}.cellWf {next}"),
                        );
                        self.push_hyp_unique(
                            format!("h_{name}_names"),
                            format!("Sable.PointsToView.names ({next}) ({p})"),
                        );
                        self.env.insert(name.clone(), Val::View(next));
                        Val::Unit
                    }
                    RawOp::IntoFreeHeader => {
                        let Val::Ptr(p) = self.eval(&args[0]) else {
                            unreachable!("checked: raw<u8>")
                        };
                        let Val::View(block) = self.eval(&args[1]) else {
                            unreachable!("checked: free block value")
                        };
                        let goal = format!(
                            "({p}).alloc = ({block}).span.alloc ∧ \
                             ({p}).off = ({block}).span.off ∧ 0 ≤ ({p}).off ∧ \
                             ({p}).off % Sable.u64.layout.align = 0 ∧ \
                             Sable.freeHeaderBytes ≤ ({block}).span.len"
                        );
                        let ob = self.obligation(
                            &format!("{}.free_header.from_block", self.fname),
                            "`raw_into_free_header` needs an aligned two-word block header".into(),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        let header = self.hinted_sym("_header", hint);
                        self.binders
                            .push((header.clone(), ResKind::FreeHeader.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{}_header", header.trim_start_matches('_')),
                            format!("{header} = Sable.FreeBlockView.toHeader ({block})"),
                        );
                        self.push_hyp_unique(
                            format!("h_{}_wf", header.trim_start_matches('_')),
                            format!("Sable.FreeHeaderView.wf {header}"),
                        );
                        Val::View(header)
                    }
                    RawOp::FromFreeHeader => {
                        let Val::Ptr(p) = self.eval(&args[0]) else {
                            unreachable!("checked: raw<u8>")
                        };
                        let Val::View(header) = self.eval(&args[1]) else {
                            unreachable!("checked: free header value")
                        };
                        let goal = format!(
                            "Sable.PointsToView.names ({header}).sizeCell ({p}) ∧ \
                             ({header}).sizeCell.state = Sable.CellState.uninit ∧ \
                             ({header}).nextCell.alloc = ({p}).alloc ∧ \
                             ({header}).nextCell.off = ({p}).off + Sable.u64.layout.size ∧ \
                             ({header}).nextCell.state = Sable.CellState.uninit"
                        );
                        let ob = self.obligation(
                            &format!("{}.free_header.to_block", self.fname),
                            "`raw_from_free_header` needs two cleared header cells".into(),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        let block = self.hinted_sym("_free", hint);
                        self.binders
                            .push((block.clone(), ResKind::FreeBlock.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{}_block", block.trim_start_matches('_')),
                            format!("{block} = Sable.FreeHeaderView.toFree ({header})"),
                        );
                        self.push_hyp_unique(
                            format!("h_{}_wf", block.trim_start_matches('_')),
                            format!("Sable.FreeBlockView.wf {block}"),
                        );
                        Val::View(block)
                    }
                    RawOp::HeaderInit => {
                        let Val::Ptr(p) = self.eval(&args[0]) else {
                            unreachable!("checked: raw<u8>")
                        };
                        let Val::Int(size) = self.eval(&args[1]) else {
                            unreachable!("checked: u64 size")
                        };
                        let Val::Int(next) = self.eval(&args[2]) else {
                            unreachable!("checked: u64 next")
                        };
                        let Val::View(header) = self.eval(&args[3]) else {
                            unreachable!("checked: free header borrow")
                        };
                        let goal = format!(
                            "Sable.PointsToView.names ({header}).sizeCell ({p}) ∧ \
                             ({header}).sizeCell.state = Sable.CellState.uninit ∧ \
                             ({header}).nextCell.alloc = ({p}).alloc ∧ \
                             ({header}).nextCell.off = ({p}).off + Sable.u64.layout.size ∧ \
                             ({header}).nextCell.state = Sable.CellState.uninit ∧ \
                             {size} = ({header}).sizeCell.layout.size + \
                               ({header}).nextCell.layout.size + ({header}).payload.len"
                        );
                        let ob = self.obligation(
                            &format!("{}.free_header.init", self.fname),
                            "`raw_header_init` needs two empty cells and the exact block size"
                                .into(),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        let ExprKind::Borrow { array: name, .. } = &args[3].kind else {
                            unreachable!("checked: free header borrow")
                        };
                        let h2 = self.hinted_sym("_header", Some(name.clone()));
                        self.binders
                            .push((h2.clone(), ResKind::FreeHeader.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{name}_init"),
                            format!(
                                "{h2} = Sable.FreeHeaderView.putFields ({header}) {size} {next}"
                            ),
                        );
                        self.push_hyp_unique(
                            format!("h_{name}_wf"),
                            format!("Sable.FreeHeaderView.wf {h2}"),
                        );
                        self.env.insert(name.clone(), Val::View(h2));
                        Val::Unit
                    }
                    RawOp::HeaderSize | RawOp::HeaderNext => {
                        let Val::Ptr(p) = self.eval(&args[0]) else {
                            unreachable!("checked: raw<u8>")
                        };
                        let Val::View(header) = self.eval(&args[1]) else {
                            unreachable!("checked: free header borrow")
                        };
                        let is_size = matches!(op, RawOp::HeaderSize);
                        let field = if is_size { "sizeCell" } else { "nextCell" };
                        let names = if is_size {
                            format!("Sable.PointsToView.names ({header}).{field} ({p})")
                        } else {
                            format!(
                                "({header}).{field}.alloc = ({p}).alloc ∧ \
                                 ({header}).{field}.off = ({p}).off + Sable.u64.layout.size"
                            )
                        };
                        let goal = format!(
                            "({names}) ∧ ({header}).{field}.state ≠ Sable.CellState.uninit"
                        );
                        let label = if is_size { "size" } else { "next" };
                        let ob = self.obligation(
                            &format!("{}.free_header.{label}", self.fname),
                            format!("`raw_header_{label}` needs an initialized header field"),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        let value = self.hinted_sym("_value", hint);
                        self.binders.push((value.clone(), "Int".into()));
                        self.push_hyp_unique(
                            format!("h_{}_header_{label}", value.trim_start_matches('_')),
                            format!("({header}).{field}.state = Sable.CellState.init {value}"),
                        );
                        self.push_hyp_unique(
                            format!("h_{}_range", value.trim_start_matches('_')),
                            range_prop(&value, IntTy::U64),
                        );
                        Val::Int(value)
                    }
                    RawOp::HeaderClear => {
                        let Val::Ptr(p) = self.eval(&args[0]) else {
                            unreachable!("checked: raw<u8>")
                        };
                        let Val::View(header) = self.eval(&args[1]) else {
                            unreachable!("checked: free header borrow")
                        };
                        let goal = format!(
                            "Sable.PointsToView.names ({header}).sizeCell ({p}) ∧ \
                             ({header}).sizeCell.state ≠ Sable.CellState.uninit ∧ \
                             ({header}).nextCell.alloc = ({p}).alloc ∧ \
                             ({header}).nextCell.off = ({p}).off + Sable.u64.layout.size ∧ \
                             ({header}).nextCell.state ≠ Sable.CellState.uninit"
                        );
                        let ob = self.obligation(
                            &format!("{}.free_header.clear", self.fname),
                            "`raw_header_clear` needs two initialized header fields".into(),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        let ExprKind::Borrow { array: name, .. } = &args[1].kind else {
                            unreachable!("checked: free header borrow")
                        };
                        let h2 = self.hinted_sym("_header", Some(name.clone()));
                        self.binders
                            .push((h2.clone(), ResKind::FreeHeader.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{name}_clear"),
                            format!("{h2} = Sable.FreeHeaderView.clearFields ({header})"),
                        );
                        self.push_hyp_unique(
                            format!("h_{name}_wf"),
                            format!("Sable.FreeHeaderView.wf {h2}"),
                        );
                        self.env.insert(name.clone(), Val::View(h2));
                        Val::Unit
                    }
                }
            }
            ExprKind::DeviceOp { op, args, .. } => {
                let hint = self.name_hint.take();
                match op {
                    DeviceOp::UartStatus => {
                        let Val::View(old) = self.eval(&args[0]) else {
                            unreachable!("checked: UART borrow")
                        };
                        let ExprKind::Borrow { array: name, .. } = &args[0].kind else {
                            unreachable!("checked: explicit mutable UART borrow")
                        };
                        let status = self.hinted_sym("_uart_status", hint);
                        self.binders.push((status.clone(), "Int".into()));
                        self.push_hyp_unique(
                            format!("h_{}_status", status.trim_start_matches('_')),
                            format!("{status} = ({old}).status"),
                        );
                        self.push_hyp_unique(
                            format!("h_{}_range", status.trim_start_matches('_')),
                            range_prop(&status, IntTy::U8),
                        );
                        let next = self.hinted_sym("_uart", Some(name.clone()));
                        self.binders
                            .push((next.clone(), ResKind::Uart.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{name}_status_transition"),
                            format!("{next} = ({old}).afterStatus {status}"),
                        );
                        self.push_hyp_unique(
                            format!("h_{name}_wf"),
                            format!("Sable.UartView.wf {next}"),
                        );
                        self.env.insert(name.clone(), Val::View(next));
                        Val::Int(status)
                    }
                    DeviceOp::UartWrite => {
                        let Val::Int(byte) = self.eval(&args[0]) else {
                            unreachable!("checked: UART byte")
                        };
                        let Val::View(old) = self.eval(&args[1]) else {
                            unreachable!("checked: UART borrow")
                        };
                        let ready = format!("({old}).ready = true");
                        let ob = self.obligation(
                            &format!("{}.uart.write_ready", self.fname),
                            "`uart_write` requires a ready transmitter".into(),
                            e.span,
                            ready.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&ready);
                        let ExprKind::Borrow { array: name, .. } = &args[1].kind else {
                            unreachable!("checked: explicit mutable UART borrow")
                        };
                        let next = self.hinted_sym("_uart", Some(name.clone()));
                        self.binders
                            .push((next.clone(), ResKind::Uart.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{name}_write_transition"),
                            format!("{next} = ({old}).afterWrite {byte}"),
                        );
                        self.push_hyp_unique(
                            format!("h_{name}_wf"),
                            format!("Sable.UartView.wf {next}"),
                        );
                        self.env.insert(name.clone(), Val::View(next));
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
                        let goal = format!(
                            "({a}).alloc = ({b}).alloc ∧ ({a}).off + ({a}).len = ({b}).off"
                        );
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
                    // `open_file(&mut w, fd)`: the world hands out the
                    // authority. Whether the descriptor is open is a VC,
                    // not a checker fact — the checker tracks tokens, and
                    // the outside world is not one of them (ADR 0028).
                    //
                    // Handing it out *spends* it: the world records the
                    // claim, so the same descriptor cannot be adopted
                    // twice. Affinity governs one token; this is what
                    // stops a second token being minted beside it.
                    ResOp::OpenFileOf => {
                        let Val::View(w) = self.eval(&args[0]) else {
                            unreachable!("checked: world borrow")
                        };
                        let Val::Int(fd) = self.eval(&args[1]) else {
                            unreachable!("checked: i32 descriptor")
                        };
                        let goal = format!("Sable.PosixWorldView.available ({w}) {fd}");
                        let ob = self.obligation(
                            &format!("{}.open_file.{}", self.fname, slug(&fd)),
                            "`open_file` needs a descriptor the world has open and \
                             has not handed out"
                                .into(),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        let ExprKind::Borrow { array, .. } = &args[0].kind else {
                            unreachable!("checked: borrow arg")
                        };
                        let w2 = self.hinted_sym("_world", Some(array.clone()));
                        self.binders
                            .push((w2.clone(), ResKind::PosixWorld.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{array}_claim"),
                            format!("{w2} = Sable.PosixWorldView.claim ({w}) {fd}"),
                        );
                        self.env.insert(array.clone(), Val::View(w2));
                        let f = self.hinted_sym("_file", hint);
                        self.binders
                            .push((f.clone(), ResKind::OpenFile.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{}_open", f.trim_start_matches('_')),
                            format!("({f}).fd = {fd} ∧ ({f}).pos = 0"),
                        );
                        Val::View(f)
                    }
                    // `posix_world(script)`: a test's world. The script
                    // selects which external behaviour the monitor plays
                    // out, and the *view* says nothing about it — no
                    // contract can predict a short read.
                    ResOp::TestWorld => {
                        let Val::Int(_script) = self.eval(&args[0]) else {
                            unreachable!("checked: u64 script")
                        };
                        let w = self.hinted_sym("_world", hint);
                        self.binders
                            .push((w.clone(), ResKind::PosixWorld.view_ty().into()));
                        for (h, prop) in view_wf_hyps(ResKind::PosixWorld, &w, &w, self.records) {
                            self.push_hyp_unique(h, prop);
                        }
                        // A fresh world has handed out no authority yet.
                        // This is a fact about *this* world, not a
                        // well-formedness condition: a world reached any
                        // other way may well have claims outstanding.
                        self.push_hyp_unique(
                            format!("h_{}_unclaimed", w.trim_start_matches('_')),
                            format!("∀ k, ({w}).claimed.get k = 0"),
                        );
                        Val::View(w)
                    }
                    ResOp::TestUart => {
                        let Val::Int(_script) = self.eval(&args[0]) else {
                            unreachable!("checked: u64 script")
                        };
                        let uart = self.hinted_sym("_uart", hint);
                        self.binders
                            .push((uart.clone(), ResKind::Uart.view_ty().into()));
                        for (h, prop) in view_wf_hyps(ResKind::Uart, &uart, &uart, self.records) {
                            self.push_hyp_unique(h, prop);
                        }
                        Val::View(uart)
                    }
                    ResOp::ResourceMapEmpty => {
                        let Some(Ty::Res(
                            map_kind @ (ResKind::ResourceMapPointsToU64
                            | ResKind::ResourceMapPointsToRecord(_)),
                        )) = e.ty
                        else {
                            unreachable!("checked: resource-map result type")
                        };
                        let map = self.hinted_sym("_resource_map", hint);
                        self.binders
                            .push((map.clone(), lean_res_view_ty(map_kind, self.records)));
                        self.push_hyp_unique(
                            format!("h_{}_empty", map.trim_start_matches('_')),
                            format!("{map} = Sable.ResourceMapView.empty"),
                        );
                        for (h, prop) in
                            view_wf_hyps(map_kind, map.trim_start_matches('_'), &map, self.records)
                        {
                            self.push_hyp_unique(h, prop);
                        }
                        Val::View(map)
                    }
                    ResOp::ResourceMapTake => {
                        let Some(
                            map_kind @ (ResKind::ResourceMapPointsToU64
                            | ResKind::ResourceMapPointsToRecord(_)),
                        ) = vc_resource_kind(&self.var_tys, &args[0])
                        else {
                            unreachable!("checked: resource-map borrow")
                        };
                        let cell_kind = match map_kind {
                            ResKind::ResourceMapPointsToU64 => ResKind::PointsToU64,
                            ResKind::ResourceMapPointsToRecord(ri) => ResKind::PointsToRecord(ri),
                            _ => unreachable!(),
                        };
                        let Val::View(map) = self.eval(&args[0]) else {
                            unreachable!("checked: resource map borrow")
                        };
                        let Val::Int(key) = self.eval(&args[1]) else {
                            unreachable!("checked: u64 key")
                        };
                        let goal = match map_kind {
                            ResKind::ResourceMapPointsToU64 => {
                                format!("Sable.ResourceMapView.canTakeU64 ({map}) {key}")
                            }
                            ResKind::ResourceMapPointsToRecord(_) => {
                                format!("∃ cell, ({map}).entries {key} = some cell")
                            }
                            _ => unreachable!(),
                        };
                        let ob = self.obligation(
                            &format!("{}.resource_map_take.{}", self.fname, slug(&key)),
                            "`resource_map_take` needs a stored entry at this key".into(),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        let ExprKind::Borrow { array, .. } = &args[0].kind else {
                            unreachable!("checked: resource map borrow")
                        };
                        let residual = self.hinted_sym("_resource_map", Some(array.clone()));
                        self.binders
                            .push((residual.clone(), lean_res_view_ty(map_kind, self.records)));
                        self.push_hyp_unique(
                            format!("h_{array}_take"),
                            format!("{residual} = Sable.ResourceMapView.erase ({map}) {key}"),
                        );
                        for (h, prop) in view_wf_hyps(map_kind, array, &residual, self.records) {
                            self.push_hyp_unique(h, prop);
                        }
                        self.env.insert(array.clone(), Val::View(residual.clone()));
                        let cell = self.hinted_sym("_cell", hint);
                        self.binders
                            .push((cell.clone(), lean_res_view_ty(cell_kind, self.records)));
                        if map_kind == ResKind::ResourceMapPointsToU64 {
                            self.push_hyp_unique(
                                format!("h_{}_take", cell.trim_start_matches('_')),
                                format!("{cell} = Sable.ResourceMapView.cellAtU64 ({map}) {key}"),
                            );
                        }
                        self.push_hyp_unique(
                            format!("h_{}_entry", cell.trim_start_matches('_')),
                            format!("({map}).entries {key} = some {cell}"),
                        );
                        for (h, prop) in view_wf_hyps(
                            cell_kind,
                            cell.trim_start_matches('_'),
                            &cell,
                            self.records,
                        ) {
                            self.push_hyp_unique(h, prop);
                        }
                        Val::View(cell)
                    }
                    ResOp::ResourceMapPut => {
                        let Some(
                            map_kind @ (ResKind::ResourceMapPointsToU64
                            | ResKind::ResourceMapPointsToRecord(_)),
                        ) = vc_resource_kind(&self.var_tys, &args[0])
                        else {
                            unreachable!("checked: resource-map borrow")
                        };
                        let Val::View(map) = self.eval(&args[0]) else {
                            unreachable!("checked: resource map borrow")
                        };
                        let Val::Int(key) = self.eval(&args[1]) else {
                            unreachable!("checked: u64 key")
                        };
                        let Val::View(cell) = self.eval(&args[2]) else {
                            unreachable!("checked: points-to value")
                        };
                        let goal = format!("({map}).entries {key} = none");
                        let ob = self.obligation(
                            &format!("{}.resource_map_put.{}", self.fname, slug(&key)),
                            "`resource_map_put` needs an absent key".into(),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        let ExprKind::Borrow { array, .. } = &args[0].kind else {
                            unreachable!("checked: resource map borrow")
                        };
                        let restored = self.hinted_sym("_resource_map", Some(array.clone()));
                        self.binders
                            .push((restored.clone(), lean_res_view_ty(map_kind, self.records)));
                        self.push_hyp_unique(
                            format!("h_{array}_put"),
                            format!(
                                "{restored} = Sable.ResourceMapView.insert \
                                 ({map}) {key} ({cell})"
                            ),
                        );
                        self.push_hyp_unique(
                            format!("h_{array}_entry"),
                            format!("({restored}).entries {key} = some {cell}"),
                        );
                        for (h, prop) in view_wf_hyps(map_kind, array, &restored, self.records) {
                            self.push_hyp_unique(h, prop);
                        }
                        self.env.insert(array.clone(), Val::View(restored));
                        Val::Unit
                    }
                    ResOp::AllocatorCreate => {
                        let Val::View(root) = self.eval(&args[0]) else {
                            unreachable!("checked: raw span value")
                        };
                        let goal = format!("({root}).off = 0 ∧ 0 < ({root}).len");
                        let ob = self.obligation(
                            &format!("{}.allocator_create", self.fname),
                            "`allocator_create` needs a positive root span at offset zero".into(),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        self.fresh += 1;
                        let identity = format!("_allocator{}", self.fresh);
                        self.binders.push((identity.clone(), "Int".into()));
                        let state = self.hinted_sym("_allocator_view", hint);
                        self.binders
                            .push((state.clone(), ResKind::AllocatorState.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{}_create", state.trim_start_matches('_')),
                            format!("{state} = Sable.AllocatorView.initial {identity} ({root})"),
                        );
                        self.push_hyp_unique(
                            format!("h_{}_complete", state.trim_start_matches('_')),
                            format!("Sable.AllocatorView.complete {state}"),
                        );
                        self.push_hyp_unique(
                            format!("h_{}_key0", state.trim_start_matches('_')),
                            format!("Sable.AllocatorView.canTake {state} 0"),
                        );
                        self.push_hyp_unique(
                            format!("h_{}_free0", state.trim_start_matches('_')),
                            format!("Sable.AllocatorView.canTakeFree {state} 0"),
                        );
                        Val::View(state)
                    }
                    ResOp::AllocatorDestroy => {
                        let Val::View(state) = self.eval(&args[0]) else {
                            unreachable!("checked: allocator state value")
                        };
                        let goal = format!("Sable.AllocatorView.complete ({state})");
                        let ob = self.obligation(
                            &format!("{}.allocator_destroy", self.fname),
                            "`allocator_destroy` needs the complete root returned to the free map"
                                .into(),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        let root = self.hinted_sym("_view", hint);
                        self.binders
                            .push((root.clone(), ResKind::RawSpan.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{}_destroy", root.trim_start_matches('_')),
                            format!("{root} = Sable.AllocatorView.releaseSpan ({state})"),
                        );
                        self.push_hyp_unique(
                            format!("h_{}_extent", root.trim_start_matches('_')),
                            format!(
                                "({root}).alloc = ({state}).root.alloc ∧ \
                                 ({root}).off = ({state}).root.off ∧ \
                                 ({root}).len = ({state}).root.len"
                            ),
                        );
                        for (h, prop) in view_wf_hyps(
                            ResKind::RawSpan,
                            root.trim_start_matches('_'),
                            &root,
                            self.records,
                        ) {
                            self.push_hyp_unique(h, prop);
                        }
                        Val::View(root)
                    }
                    ResOp::AllocatorTake => {
                        let Val::View(state) = self.eval(&args[0]) else {
                            unreachable!("checked: allocator state borrow")
                        };
                        let Val::Int(key) = self.eval(&args[1]) else {
                            unreachable!("checked: u64 key")
                        };
                        let goal = format!("Sable.AllocatorView.canTake ({state}) {key}");
                        let ob = self.obligation(
                            &format!("{}.allocator_take.{}", self.fname, slug(&key)),
                            "`allocator_take` needs a free entry at this key".into(),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        let ExprKind::Borrow { array, .. } = &args[0].kind else {
                            unreachable!("checked: allocator borrow")
                        };
                        let residual = self.hinted_sym("_allocator_view", Some(array.clone()));
                        self.binders
                            .push((residual.clone(), ResKind::AllocatorState.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{array}_take"),
                            format!("{residual} = Sable.AllocatorView.take ({state}) {key}"),
                        );
                        self.env.insert(array.clone(), Val::View(residual.clone()));
                        let lease = self.hinted_sym("_lease", hint);
                        self.binders
                            .push((lease.clone(), ResKind::BlockLease.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{}_take", lease.trim_start_matches('_')),
                            format!("{lease} = Sable.AllocatorView.leaseAt ({state}) {key}"),
                        );
                        self.push_hyp_unique(
                            format!("h_{}_returnable", lease.trim_start_matches('_')),
                            format!("Sable.AllocatorView.canPut ({residual}) ({lease})"),
                        );
                        Val::View(lease)
                    }
                    ResOp::AllocatorPut => {
                        let Val::View(state) = self.eval(&args[0]) else {
                            unreachable!("checked: allocator state borrow")
                        };
                        let Val::View(lease) = self.eval(&args[1]) else {
                            unreachable!("checked: block lease value")
                        };
                        let goal = format!("Sable.AllocatorView.canPut ({state}) ({lease})");
                        let ob = self.obligation(
                            &format!("{}.allocator_put", self.fname),
                            "`allocator_put` needs a lease from this allocator and an absent key"
                                .into(),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        let ExprKind::Borrow { array, .. } = &args[0].kind else {
                            unreachable!("checked: allocator borrow")
                        };
                        let restored = self.hinted_sym("_allocator_view", Some(array.clone()));
                        self.binders
                            .push((restored.clone(), ResKind::AllocatorState.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{array}_put"),
                            format!("{restored} = Sable.AllocatorView.put ({state}) ({lease})"),
                        );
                        self.env.insert(array.clone(), Val::View(restored));
                        Val::Unit
                    }
                    ResOp::AllocatorTakeFree => {
                        let Val::View(state) = self.eval(&args[0]) else {
                            unreachable!("checked: allocator state borrow")
                        };
                        let Val::Int(key) = self.eval(&args[1]) else {
                            unreachable!("checked: u64 key")
                        };
                        let goal = format!("Sable.AllocatorView.canTakeFree ({state}) {key}");
                        let ob = self.obligation(
                            &format!("{}.allocator_take_free.{}", self.fname, slug(&key)),
                            "`allocator_take_free` needs a free entry at this key".into(),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        let ExprKind::Borrow { array, .. } = &args[0].kind else {
                            unreachable!("checked: allocator borrow")
                        };
                        let residual = self.hinted_sym("_allocator_view", Some(array.clone()));
                        self.binders
                            .push((residual.clone(), ResKind::AllocatorState.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{array}_take_free"),
                            format!("{residual} = Sable.AllocatorView.take ({state}) {key}"),
                        );
                        self.push_hyp_unique(
                            format!("h_{array}_owner_free"),
                            format!("({residual}).allocator = ({state}).allocator"),
                        );
                        self.env.insert(array.clone(), Val::View(residual.clone()));
                        let block = self.hinted_sym("_free", hint);
                        self.binders
                            .push((block.clone(), ResKind::FreeBlock.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{}_take", block.trim_start_matches('_')),
                            format!("{block} = Sable.AllocatorView.takeFree ({state}) {key}"),
                        );
                        self.push_hyp_unique(
                            format!("h_{}_wf", block.trim_start_matches('_')),
                            format!("Sable.FreeBlockView.wf {block}"),
                        );
                        self.push_hyp_unique(
                            format!("h_{}_owner", block.trim_start_matches('_')),
                            format!("({block}).allocator = ({residual}).allocator"),
                        );
                        Val::View(block)
                    }
                    ResOp::AllocatorPutFree => {
                        let Val::View(state) = self.eval(&args[0]) else {
                            unreachable!("checked: allocator state borrow")
                        };
                        let Val::View(block) = self.eval(&args[1]) else {
                            unreachable!("checked: free block value")
                        };
                        let goal = format!("Sable.AllocatorView.canPutFree ({state}) ({block})");
                        let ob = self.obligation(
                            &format!("{}.allocator_put_free", self.fname),
                            "`allocator_put_free` needs a matching well-formed internal block"
                                .into(),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        let ExprKind::Borrow { array, .. } = &args[0].kind else {
                            unreachable!("checked: allocator borrow")
                        };
                        let restored = self.hinted_sym("_allocator_view", Some(array.clone()));
                        self.binders
                            .push((restored.clone(), ResKind::AllocatorState.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{array}_put_free"),
                            format!("{restored} = Sable.AllocatorView.putFree ({state}) ({block})"),
                        );
                        self.push_hyp_unique(
                            format!("h_{array}_owner_free"),
                            format!("({restored}).allocator = ({state}).allocator"),
                        );
                        self.push_hyp_unique(
                            format!("h_{array}_takeable_free"),
                            format!("Sable.AllocatorView.canTakeFree ({restored}) ({block}).key"),
                        );
                        self.push_hyp_unique(
                            format!("h_{array}_entry_free"),
                            format!(
                                "Sable.AllocatorView.takeFree ({restored}) ({block}).key = {block}"
                            ),
                        );
                        self.env.insert(array.clone(), Val::View(restored));
                        Val::Unit
                    }
                    ResOp::AllocatorTakeHeader => {
                        let Val::View(state) = self.eval(&args[0]) else {
                            unreachable!("checked: allocator state borrow")
                        };
                        let Val::Int(key) = self.eval(&args[1]) else {
                            unreachable!("checked: u64 key")
                        };
                        let goal = format!("Sable.AllocatorView.canTakeHeader ({state}) {key}");
                        let ob = self.obligation(
                            &format!("{}.allocator_take_header.{}", self.fname, slug(&key)),
                            "`allocator_take_header` needs a stored header at this key".into(),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        let ExprKind::Borrow { array, .. } = &args[0].kind else {
                            unreachable!("checked: allocator borrow")
                        };
                        let residual = self.hinted_sym("_allocator_view", Some(array.clone()));
                        self.binders
                            .push((residual.clone(), ResKind::AllocatorState.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{array}_take_header"),
                            format!("{residual} = Sable.AllocatorView.takeHeader ({state}) {key}"),
                        );
                        self.env.insert(array.clone(), Val::View(residual.clone()));
                        let header = self.hinted_sym("_header", hint);
                        self.binders
                            .push((header.clone(), ResKind::FreeHeader.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{}_take", header.trim_start_matches('_')),
                            format!("{header} = Sable.AllocatorView.headerAt ({state}) {key}"),
                        );
                        self.push_hyp_unique(
                            format!("h_{}_wf", header.trim_start_matches('_')),
                            format!("Sable.FreeHeaderView.wf {header}"),
                        );
                        self.push_hyp_unique(
                            format!("h_{}_owner", header.trim_start_matches('_')),
                            format!("({header}).allocator = ({residual}).allocator"),
                        );
                        Val::View(header)
                    }
                    ResOp::AllocatorStepHeader => {
                        let Val::View(state) = self.eval(&args[0]) else {
                            unreachable!("checked: allocator state borrow")
                        };
                        let Val::Int(limit) = self.eval(&args[1]) else {
                            unreachable!("checked: u64 limit")
                        };
                        let Val::Int(key) = self.eval(&args[2]) else {
                            unreachable!("checked: u64 key")
                        };
                        let goal = format!(
                            "{key} ≠ {limit} ∧ \
                             Sable.AllocatorView.StoredChain ({state}) {limit} {key}"
                        );
                        let ob = self.obligation(
                            &format!("{}.allocator_step_header.{}", self.fname, slug(&key)),
                            "`allocator_step_header` needs a non-sentinel node in the sorted chain"
                                .into(),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        let ExprKind::Borrow { array, .. } = &args[0].kind else {
                            unreachable!("checked: allocator borrow")
                        };
                        let residual = self.hinted_sym("_allocator_view", Some(array.clone()));
                        self.binders
                            .push((residual.clone(), ResKind::AllocatorState.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{array}_step_header"),
                            format!("{residual} = Sable.AllocatorView.takeHeader ({state}) {key}"),
                        );
                        self.env.insert(array.clone(), Val::View(residual.clone()));
                        let header = self.hinted_sym("_header", hint);
                        self.binders
                            .push((header.clone(), ResKind::FreeHeader.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{}_step", header.trim_start_matches('_')),
                            format!("{header} = Sable.AllocatorView.headerAt ({state}) {key}"),
                        );
                        self.push_hyp_unique(
                            format!("h_{}_wf", header.trim_start_matches('_')),
                            format!("Sable.FreeHeaderView.wf {header}"),
                        );
                        self.push_hyp_unique(
                            format!("h_{}_owner", header.trim_start_matches('_')),
                            format!("({header}).allocator = ({residual}).allocator"),
                        );
                        Val::View(header)
                    }
                    ResOp::AllocatorPutHeader => {
                        let Val::View(state) = self.eval(&args[0]) else {
                            unreachable!("checked: allocator state borrow")
                        };
                        let Val::View(header) = self.eval(&args[1]) else {
                            unreachable!("checked: free header value")
                        };
                        let goal = format!("Sable.AllocatorView.canPutHeader ({state}) ({header})");
                        let ob = self.obligation(
                            &format!("{}.allocator_put_header", self.fname),
                            "`allocator_put_header` needs a matching well-formed header slot"
                                .into(),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        let ExprKind::Borrow { array, .. } = &args[0].kind else {
                            unreachable!("checked: allocator borrow")
                        };
                        let restored = self.hinted_sym("_allocator_view", Some(array.clone()));
                        self.binders
                            .push((restored.clone(), ResKind::AllocatorState.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{array}_put_header"),
                            format!(
                                "{restored} = Sable.AllocatorView.putHeader ({state}) ({header})"
                            ),
                        );
                        self.push_hyp_unique(
                            format!("h_{array}_takeable_header"),
                            format!(
                                "Sable.AllocatorView.canTakeHeader ({restored}) ({header}).key"
                            ),
                        );
                        self.push_hyp_unique(
                            format!("h_{array}_entry_header"),
                            format!(
                                "Sable.AllocatorView.headerAt ({restored}) ({header}).key = {header}"
                            ),
                        );
                        self.env.insert(array.clone(), Val::View(restored));
                        Val::Unit
                    }
                    ResOp::FreeBlockSplit => {
                        let Val::View(block) = self.eval(&args[0]) else {
                            unreachable!("checked: free block borrow")
                        };
                        let Val::Int(n) = self.eval(&args[1]) else {
                            unreachable!("checked: u64 split")
                        };
                        let goal = format!("0 < {n} ∧ {n} < ({block}).span.len");
                        let mut ob = self.obligation(
                            &format!("{}.free_block_split.{}", self.fname, slug(&n)),
                            "`free_block_split` needs two nonempty result blocks".into(),
                            e.span,
                            goal.clone(),
                        );
                        // Allocator identity is irrelevant to this numeric
                        // bound and expanding aggregate-view equalities gives
                        // simplification an enormous higher-order search
                        // surface. Keep the fact for later transitions, but
                        // leave it out of this local geometry VC.
                        ob.hyps.retain(|(name, _)| !name.ends_with("_owner"));
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        let ExprKind::Borrow { array, .. } = &args[0].kind else {
                            unreachable!("checked: free block borrow")
                        };
                        let prefix = self.hinted_sym("_free", Some(array.clone()));
                        self.binders
                            .push((prefix.clone(), ResKind::FreeBlock.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{array}_prefix"),
                            format!("{prefix} = Sable.FreeBlockView.prefix ({block}) {n}"),
                        );
                        self.push_hyp_unique(
                            format!("h_{array}_wf"),
                            format!("Sable.FreeBlockView.wf {prefix}"),
                        );
                        self.env.insert(array.clone(), Val::View(prefix));
                        let suffix = self.hinted_sym("_free", hint);
                        self.binders
                            .push((suffix.clone(), ResKind::FreeBlock.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{}_suffix", suffix.trim_start_matches('_')),
                            format!("{suffix} = Sable.FreeBlockView.suffix ({block}) {n}"),
                        );
                        self.push_hyp_unique(
                            format!("h_{}_wf", suffix.trim_start_matches('_')),
                            format!("Sable.FreeBlockView.wf {suffix}"),
                        );
                        self.push_hyp_unique(
                            format!("h_{}_split", suffix.trim_start_matches('_')),
                            format!(
                                "({suffix}).allocator = ({block}).allocator ∧ \
                                 ({suffix}).key = ({block}).key + {n} ∧ \
                                 ({suffix}).span.alloc = ({block}).span.alloc ∧ \
                                 ({suffix}).span.off = ({block}).span.off + {n} ∧ \
                                 ({suffix}).span.len = ({block}).span.len - {n}"
                            ),
                        );
                        Val::View(suffix)
                    }
                    ResOp::FreeBlockJoin => {
                        let Val::View(left) = self.eval(&args[0]) else {
                            unreachable!("checked: free block value")
                        };
                        let Val::View(right) = self.eval(&args[1]) else {
                            unreachable!("checked: free block value")
                        };
                        let goal = format!("Sable.FreeBlockView.joinable ({left}) ({right})");
                        let ob = self.obligation(
                            &format!("{}.free_block_join", self.fname),
                            "`free_block_join` needs adjacent blocks from one allocator".into(),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        let joined = self.hinted_sym("_free", hint);
                        self.binders
                            .push((joined.clone(), ResKind::FreeBlock.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{}_join", joined.trim_start_matches('_')),
                            format!("{joined} = Sable.FreeBlockView.join ({left}) ({right})"),
                        );
                        self.push_hyp_unique(
                            format!("h_{}_wf", joined.trim_start_matches('_')),
                            format!("Sable.FreeBlockView.wf {joined}"),
                        );
                        self.push_hyp_unique(
                            format!("h_{}_owner", joined.trim_start_matches('_')),
                            format!("({joined}).allocator = ({left}).allocator"),
                        );
                        Val::View(joined)
                    }
                    ResOp::FreeBlockLease => {
                        let Val::View(block) = self.eval(&args[0]) else {
                            unreachable!("checked: free block value")
                        };
                        let lease = self.hinted_sym("_lease", hint);
                        self.binders
                            .push((lease.clone(), ResKind::BlockLease.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{}_lease", lease.trim_start_matches('_')),
                            format!("{lease} = Sable.FreeBlockView.toLease ({block})"),
                        );
                        self.push_hyp_unique(
                            format!("h_{}_owner", lease.trim_start_matches('_')),
                            format!("({lease}).allocator = ({block}).allocator"),
                        );
                        self.push_hyp_unique(
                            format!("h_{}_whole", lease.trim_start_matches('_')),
                            format!(
                                "({lease}).key = ({lease}).span.off ∧ \
                                 0 < ({lease}).span.len"
                            ),
                        );
                        Val::View(lease)
                    }
                    ResOp::BlockLeaseFree => {
                        let Val::View(lease) = self.eval(&args[0]) else {
                            unreachable!("checked: block lease value")
                        };
                        let goal =
                            format!("({lease}).key = ({lease}).span.off ∧ 0 < ({lease}).span.len");
                        let ob = self.obligation(
                            &format!("{}.block_lease_free", self.fname),
                            "`block_lease_free` needs a positive whole-block lease".into(),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        let block = self.hinted_sym("_free", hint);
                        self.binders
                            .push((block.clone(), ResKind::FreeBlock.view_ty().into()));
                        self.push_hyp_unique(
                            format!("h_{}_free", block.trim_start_matches('_')),
                            format!("{block} = Sable.BlockLeaseView.toFree ({lease})"),
                        );
                        self.push_hyp_unique(
                            format!("h_{}_wf", block.trim_start_matches('_')),
                            format!("Sable.FreeBlockView.wf {block}"),
                        );
                        self.push_hyp_unique(
                            format!("h_{}_owner", block.trim_start_matches('_')),
                            format!("({block}).allocator = ({lease}).allocator"),
                        );
                        Val::View(block)
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
            ExprKind::RecordField { obj, field, .. } => {
                let Val::Record(record) = self.env[obj.as_str()].clone() else {
                    unreachable!("checked: record receiver")
                };
                let projection = format!("({record}).{field}");
                match e.ty {
                    Some(Ty::Int(_)) => Val::Int(projection),
                    Some(Ty::RawRecord(_)) => Val::Ptr(projection),
                    Some(Ty::OptionRaw(_)) => Val::Opt(projection),
                    _ => unreachable!("checked: initial record field type"),
                }
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
                // The field's *kind* decides the symbolic value: a resource
                // field projects to its view, a class field to its
                // structure. This is what lets a destructor hand a resource
                // field on to something that consumes it (ADR 0029).
                Cctx::Method(..) | Cctx::Deinit(_) => {
                    let projected = project_field(&self.self_chain(), field);
                    match e.ty {
                        Some(Ty::Res(_)) | Some(Ty::ResRef(..)) => Val::View(projected),
                        Some(Ty::Class(_)) | Some(Ty::ClassRef(..)) => Val::Obj(projected),
                        Some(Ty::Raw(_)) => Val::Ptr(projected),
                        Some(Ty::Array(..)) => Val::Arr(projected),
                        _ => Val::Int(projected),
                    }
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
                // Int args and `&[T]` borrows (shared only — no havoc to
                // apply): the seq chain substitutes for the param name in
                // the init's pres/posts exactly like fn-call array args.
                let arg_vals: Vec<String> = args
                    .iter()
                    .map(|a| match self.eval(a) {
                        // Class args (by value or borrowed) substitute
                        // as their symbolic structure value (ADR 0020).
                        Val::Int(v) | Val::Arr(v) | Val::Obj(v) | Val::View(v) => v,
                        Val::Prop(p) => {
                            format!("@decide ({p}) (Classical.propDecidable ({p}))")
                        }
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
            ExprKind::RecordLit { record, args, .. } => {
                let ri = self
                    .records
                    .iter()
                    .position(|r| r.name == *record)
                    .expect("checked: record exists");
                let lean_record = lean_record_name(record);
                let values: Vec<String> = args
                    .iter()
                    .map(|arg| match self.eval(arg) {
                        Val::Int(v) | Val::Opt(v) | Val::Ptr(v) => format!("({v})"),
                        _ => unreachable!("checked: raw-storable record field"),
                    })
                    .collect();
                let value = format!("({lean_record}.mk {})", values.join(" "));
                self.push_hyp_unique(
                    format!("h_{}_wf", slug(self.src(e.span))),
                    format!("{}.wf {value}", lean_record_name(&self.records[ri].name)),
                );
                Val::Record(value)
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
                        Val::Int(v) | Val::Arr(v) | Val::Obj(v) | Val::View(v) | Val::Ptr(v) => v,
                        _ => unreachable!("checked: int/array/class/resource/pointer args"),
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
                    // A method returns a class or a resource on the same
                    // terms a function does: a fresh state with its field
                    // facts and invariant, or a fresh view. Ownership of
                    // what came back is the checker's business and appears
                    // nowhere here (ADR 0010, ADR 0024).
                    Ty::Class(rci) => {
                        let rcd = &self.classes[rci];
                        self.binders
                            .push((ret_sym.clone(), lean_class_name(&rcd.name)));
                        let rcd = rcd.clone();
                        self.push_class_state_facts(&rcd, &ret_sym);
                        self.push_invariant_hyps(&rcd, &ret_sym);
                    }
                    Ty::Res(k) | Ty::ResRef(k, _) => {
                        self.binders
                            .push((ret_sym.clone(), lean_res_view_ty(k, self.records)));
                        for (h, prop) in view_wf_hyps(k, &ret_sym, &ret_sym, self.records) {
                            self.push_hyp_unique(h, prop);
                        }
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
                    let text = preprocess_old_params(&preprocess_old_self(&post.text), &m.f.params);
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
                    Ty::Class(_) => Val::Obj(ret_sym),
                    Ty::Res(_) | Ty::ResRef(..) => Val::View(ret_sym),
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
                        Val::Int(v) | Val::Arr(v) | Val::Obj(v) | Val::View(v) | Val::Ptr(v) => v,
                        _ => unreachable!("checked: int/array/class/resource/pointer args"),
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
                        self.binders
                            .push((ret_sym.clone(), lean_res_view_ty(k, self.records)));
                        for (h, prop) in view_wf_hyps(k, &ret_sym, &ret_sym, self.records) {
                            self.push_hyp_unique(h, prop);
                        }
                    }
                    // A returned pointer is an opaque `RawPtr`: what is
                    // known about it is whatever the post says.
                    Ty::Raw(_) => {
                        self.binders.push((ret_sym.clone(), "Sable.RawPtr".into()));
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
                    Ty::Raw(_) => Val::Ptr(ret_sym),
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
                Val::Int(s)
                | Val::Opt(s)
                | Val::Arr(s)
                | Val::Obj(s)
                | Val::Record(s)
                | Val::View(s)
                | Val::Ptr(s)
                    if s != name =>
                {
                    Some((name.clone(), s.clone()))
                }
                // Source booleans are `Bool`, while the symbolic evaluator
                // carries their meaning as a Lean `Prop`. Reify a changed
                // proposition back to `Bool` before splicing it into an
                // arbitrary source clause (`b`, `b = true`, and `b ↔ p`
                // must all remain well-typed). A parameter or havocked bool's
                // canonical self mapping is already represented by its source
                // binder and must stay untouched.
                Val::Prop(p) if p != name && p != &format!("({name} = true)") => Some((
                    name.clone(),
                    format!("@decide ({p}) (Classical.propDecidable ({p}))"),
                )),
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
            Cctx::Method(..) | Cctx::Deinit(_) => project_field(&self.self_chain(), field),
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
                Ty::Record(ri) => {
                    out.push((p.name.clone(), lean_record_name(&self.records[ri].name)))
                }
                Ty::Array(..) => {
                    out.push((p.name.clone(), "Sable.Seq Int".into()));
                    if let Some(entry) = self.entry_states.get(&p.name) {
                        out.push((entry.clone(), "Sable.Seq Int".into()));
                    }
                }
                Ty::Raw(_) | Ty::RawRecord(_) => out.push((p.name.clone(), "Sable.RawPtr".into())),
                Ty::OptionRaw(_) => out.push((p.name.clone(), "Option Sable.RawPtr".into())),
                Ty::Res(k) | Ty::ResRef(k, _) => {
                    out.push((p.name.clone(), lean_res_view_ty(k, self.records)));
                    if let Some(entry) = self.entry_states.get(&p.name) {
                        out.push((entry.clone(), lean_res_view_ty(k, self.records)));
                    }
                }
                Ty::Option(_) | Ty::Unit => {}
            }
        }
        match self.cctx {
            Cctx::Init(c) | Cctx::Deinit(c) => {
                out.push(("self".to_string(), lean_class_name(&c.name)))
            }
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
            // A destructor owes no invariant at exit: the value ceases to
            // exist, so there is nothing left to hold it (ADR 0029). Its
            // field states still substitute, because its own body's
            // obligations speak about them.
            Cctx::Deinit(class) => {
                let chain = self.self_chain();
                mut_map.extend(self.class_state_map(class, &chain));
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
            Stmt::Store {
                array,
                index,
                value,
                ..
            } => {
                out.insert(array.clone());
                collect_mut_borrows(index, out, mut_recv);
                collect_mut_borrows(value, out, mut_recv);
            }
            Stmt::FieldAssign { value, .. } => {
                out.insert("self".to_string());
                collect_mut_borrows(value, out, mut_recv);
            }
            Stmt::FieldStore { index, value, .. } => {
                out.insert("self".to_string());
                collect_mut_borrows(index, out, mut_recv);
                collect_mut_borrows(value, out, mut_recv);
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
                cond,
                then_block,
                else_block,
            } => {
                collect_mut_borrows(cond, out, mut_recv);
                collect_assigned(then_block, out, mut_recv);
                if let Some(eb) = else_block {
                    collect_assigned(eb, out, mut_recv);
                }
            }
            Stmt::While { cond, body, .. } => {
                collect_mut_borrows(cond, out, mut_recv);
                collect_assigned(body, out, mut_recv);
            }
            // `unsafe` is a vocabulary marker, not an effect barrier. An
            // exposure is a nested scope, but writes through its mutable raw
            // view change the exposed safe array at exit, and its body may
            // also mutate unrelated outer state.
            Stmt::Unsafe { body, .. } => collect_assigned(body, out, mut_recv),
            Stmt::Expose {
                array,
                mutable,
                body,
                ..
            } => {
                if *mutable {
                    out.insert(array.clone());
                }
                collect_assigned(body, out, mut_recv);
            }
            Stmt::StaticAlloc { size, .. } | Stmt::SystemAlloc { size, .. } => {
                collect_mut_borrows(size, out, mut_recv);
            }
            Stmt::SystemDealloc {
                ptr, res, release, ..
            } => {
                collect_mut_borrows(ptr, out, mut_recv);
                collect_mut_borrows(res, out, mut_recv);
                collect_mut_borrows(release, out, mut_recv);
            }
            Stmt::Decl { init: None, .. } | Stmt::Return { value: None, .. } => {}
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
        ExprKind::Call { args, .. }
        | ExprKind::CtorCall { args, .. }
        | ExprKind::RecordLit { args, .. }
        | ExprKind::RawOp { args, .. }
        | ExprKind::ResOp { args, .. }
        | ExprKind::DeviceOp { args, .. } => {
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
        // Deliberately exhaustive: a new expression form must decide whether
        // it contains an effectful subexpression instead of silently falling
        // through and reopening loop-havoc unsoundness.
        ExprKind::IntLit(_)
        | ExprKind::BoolLit(_)
        | ExprKind::Var(_)
        | ExprKind::Len { .. }
        | ExprKind::NoneE
        | ExprKind::SelfField { .. }
        | ExprKind::SelfFieldLen { .. }
        | ExprKind::ClassField { .. }
        | ExprKind::RecordField { .. }
        | ExprKind::ClassFieldLen { .. } => {}
    }
}

/// The well-formedness a resource view carries at every binding site.
/// This is the shape of the *value*, not a claim about authority: a span
/// has a nonnegative length its byte sequence covers.
fn vc_resource_kind(var_tys: &HashMap<String, Ty>, e: &Expr) -> Option<ResKind> {
    let name = match &e.kind {
        ExprKind::Var(name) => Some(name.clone()),
        ExprKind::SelfField { field } => Some(format!("self.{field}")),
        ExprKind::Borrow { array, field, .. } => Some(
            field
                .as_ref()
                .map_or_else(|| array.clone(), |f| format!("{array}.{f}")),
        ),
        _ => None,
    }?;
    match var_tys.get(name.as_str()).copied()? {
        Ty::Res(kind) | Ty::ResRef(kind, _) => Some(kind),
        _ => None,
    }
}

fn view_wf_hyps(
    kind: ResKind,
    name: &str,
    binder: &str,
    records: &[RecordDecl],
) -> Vec<(String, String)> {
    match kind {
        ResKind::RawSpan => vec![(
            format!("h_{name}_wf"),
            format!("0 ≤ {binder}.len ∧ {binder}.len ≤ {binder}.bytes.len"),
        )],
        ResKind::PointsToU64 => vec![(
            format!("h_{name}_wf"),
            format!("Sable.PointsToView.wfU64 {binder}"),
        )],
        ResKind::PointsToRecord(ri) => vec![(
            format!("h_{name}_wf"),
            format!("{}.cellWf {binder}", lean_record_name(&records[ri].name)),
        )],
        // A descriptor is nonnegative and a position never goes backwards
        // past the start of the file. Nothing about *which* file, and
        // nothing about the outside world: that is the world's business.
        ResKind::OpenFile => vec![(
            format!("h_{name}_wf"),
            format!("0 ≤ {binder}.fd ∧ 0 ≤ {binder}.pos"),
        )],
        // A world's stream is a *byte* stream. Without that, a `read`
        // post saying "these bytes came from the stream" says nothing
        // about whether they are bytes, and the caller's `[u8]` cannot be
        // reconstructed from them (ADR 0028).
        ResKind::PosixWorld => vec![(
            format!("h_{name}_wf"),
            format!("Sable.PosixWorldView.wf {binder}"),
        )],
        ResKind::Uart => vec![(
            format!("h_{name}_wf"),
            format!("Sable.UartView.wf {binder}"),
        )],
        ResKind::SystemDealloc => vec![(
            format!("h_{name}_wf"),
            format!("Sable.SystemDeallocView.wf {binder}"),
        )],
        // These aggregate views contain functions. Expanding their shape
        // predicates in every unrelated VC gives automation an unbounded
        // matching surface; sealed operations emit the local facts they
        // establish instead.
        ResKind::AllocatorState | ResKind::BlockLease | ResKind::LeasedPointsToU64 => vec![],
        ResKind::FreeBlock => vec![(
            format!("h_{name}_wf"),
            format!("Sable.FreeBlockView.wf {binder}"),
        )],
        ResKind::FreeHeader => vec![(
            format!("h_{name}_wf"),
            format!("Sable.FreeHeaderView.wf {binder}"),
        )],
        ResKind::ResourceMapPointsToU64 => vec![(
            format!("h_{name}_wf"),
            format!("Sable.ResourceMapView.wfU64 {binder}"),
        )],
        ResKind::ResourceMapPointsToRecord(ri) => vec![(
            format!("h_{name}_wf"),
            format!(
                "Sable.ResourceMapView.wfWith {}.cellWf {binder}",
                lean_record_name(&records[ri].name)
            ),
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

/// Lean name of a POD record structure. The distinct prefix mirrors the
/// source category split from affine classes (ADR 0054).
pub fn lean_record_name(name: &str) -> String {
    format!("SableR_{name}")
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
    if out.is_empty() {
        "e".to_string()
    } else {
        out
    }
}
