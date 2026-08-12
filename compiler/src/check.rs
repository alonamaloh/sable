//! Typechecking: exact-width integer types with no
//! implicit conversions (only explicit `widen`), array/option restrictions,
//! definite initialization, all-paths-return, loop variants required, and
//! recursion allowed only for self-calls with a declared measure.
//!
//! The checker writes types into the AST (`Expr::ty`) for the VC generator.

use crate::ast::*;
use crate::diag::Diagnostic;
use crate::span::Span;
use std::collections::{HashMap, HashSet};

pub struct FnSig {
    pub params: Vec<Param>,
    pub ret: Ty,
}

/// Lightweight class signature data, pre-collected so member bodies can
/// be checked while the AST is mutably traversed.
#[derive(Clone)]
pub struct ClassMeta {
    pub name: String,
    pub fields: Vec<(String, Ty)>,
    pub inits: Vec<(String, Vec<Param>)>,
    pub methods: Vec<(String, Vec<Param>, Ty, SelfKind)>,
}

pub struct CheckResult {
    pub sigs: HashMap<String, FnSig>,
    /// How many `unsafe` regions the program opened. Reported by the
    /// driver: the number of places a reader must audit is a fact about
    /// the program, and burying it would defeat the point of having a
    /// boundary (ADR 0026).
    pub unsafe_regions: usize,
}

type CResult<T> = Result<T, Diagnostic>;

struct VarInfo {
    ty: Ty,
    initialized: bool,
    /// Declared `mut` (ADR 0016). Params are immutable; `self.f`
    /// pseudo-vars are governed by the receiver kind instead.
    mutable: bool,
    /// Introduced by, or derived from, a lexical exposure — a *loan
    /// brand* (ADR 0026). Branded values name storage that exists only
    /// for the body of that exposure, so they may not escape it: no
    /// return, no assignment to an outer place, and no passing to a
    /// user function that could launder them out.
    branded: bool,
    /// An undischarged mandatory-consumption obligation is sitting *here*
    /// (ADRs 0029/0030/0035). It may come from the resource type or the
    /// older per-field marker and travels with the token. Being a state of
    /// the place rather than a property of the declaration is what lets it
    /// join path-sensitively — outstanding after a branch iff outstanding
    /// on some reaching path.
    obligation: bool,
}

struct Ctx<'a> {
    /// Inside an `unsafe` block or an exposure body: raw operations are
    /// legal here and nowhere else (ADR 0026).
    in_unsafe: bool,
    /// How many `unsafe` regions this function opened — reported, because
    /// the number of places a reader must audit is a fact about the
    /// program worth surfacing.
    unsafe_blocks: usize,
    sigs: &'a HashMap<String, FnSig>,
    current_fn: String,
    current_has_variant: bool,
    /// `test_*` functions: dynamic-only, excluded from verification,
    /// allowed owned arrays / borrows / array-passing (design §9).
    in_test: bool,
    vars: HashMap<String, VarInfo>,
    /// Places moved out of (ADR 0020/0022). Keyed by place rather than
    /// by name: a field is a place in its own right, so moving one out
    /// kills that field and the whole, but not its siblings.
    moved: HashSet<Place>,
    /// Locals and parameters have pairwise-distinct names
    /// (keeps path-splitting and havoc in the VC generator scope-free).
    declared: HashSet<String>,
    /// Non-self callees (for mutual-recursion detection).
    calls: Vec<String>,
    /// Class-member context: (class meta index, self is &mut).
    in_class: Option<(usize, bool)>,
    /// Inside an `init`: fields start uninitialized, `return` forbidden.
    in_init: bool,
    /// Inside a destructor. The class invariant holds on entry and is not
    /// re-established, which is precisely the premise `class.mut_field_borrow`
    /// was deferred on — so a mutable field borrow is legitimate here and
    /// nowhere else (ADR 0029).
    in_deinit: bool,
    class_metas: &'a [ClassMeta],
    /// Name and declaration span of the enclosing class's
    /// `#[must_consume]` fields; empty outside a class member. A field
    /// keeps its marker when it is given a new value, so the sink needs
    /// to know which fields carry one.
    marked_fields: &'a [(String, Span)],
    /// Template context (ADR 0009): bounded type parameter →
    /// (trait name, parameter index).
    tbounds: HashMap<String, (String, u8)>,
    /// Operator bindings (ADR 0012): (symbol, class meta index) → the
    /// bound function's name.
    operators: &'a HashMap<(OpSym, usize), String>,
    traits: &'a [TraitDecl],
}

/// The class index of a class-typed name (owned local or class-borrow
/// param).
fn class_of(ctx: &Ctx, name: &str, span: Span) -> CResult<usize> {
    reject_view_read(ctx, name, span)?;
    match ctx.vars.get(name).map(|v| v.ty) {
        Some(Ty::Class(ci)) | Some(Ty::ClassRef(ci, _)) => Ok(ci),
        _ => Err(Diagnostic {
            name: "type.mismatch".into(),
            title: format!("`{name}` is not a class value"),
            span,
            label: "field access needs a class-typed receiver".into(),
            notes: vec![],
        }),
    }
}

fn tbounds_of(params: &[String], bounds: &[Option<String>]) -> HashMap<String, (String, u8)> {
    let mut out = HashMap::new();
    for (i, p) in params.iter().enumerate() {
        if let Some(Some(b)) = bounds.get(i) {
            out.insert(p.clone(), (b.clone(), i as u8));
        }
    }
    out
}

fn class_tbounds(c: &ClassDecl) -> HashMap<String, (String, u8)> {
    tbounds_of(&c.type_params, &c.type_bounds)
}

/// An extern's signature must be ABI-representable and must not be able
/// to hand storage back: retained pointers and ownership transfer to
/// foreign code are out of scope for v1. For a verified Sable callee the
/// signature establishes nonescape; for foreign code it is an audited
/// promise, because C could retain a pointer in state Sable cannot see
/// (ADR 0027).
fn check_extern_signature(f: &Fn) -> CResult<()> {
    // A whitelist, not a blacklist. Forbidding raw and resource returns
    // named the *storage* cases and missed the container: a class may hold
    // resource fields (ADR 0029), so returning one is returning storage by
    // another route. Every other type — options, arrays, classes — would
    // need a layout and an ownership-transfer meaning at the ABI that
    // Sable has not specified, so they wait until it does.
    if !matches!(f.ret, Ty::Unit | Ty::Int(_)) {
        let what = match f.ret {
            Ty::Class(_) => "a class value".to_string(),
            other => format!("`{}`", other.name()),
        };
        return Err(Diagnostic {
            name: "extern.returns_storage".into(),
            title: format!("`{}` may not return {what}", f.name),
            span: f.name_span,
            label: "an extern returns an integer or nothing".into(),
            notes: vec![(
                "note".into(),
                "retained pointers and ownership transfer to foreign code are out of \
                 scope; a signature that cannot hand storage back is what lets a \
                 caller pass borrowed storage to an extern at all — and a class \
                 counts, because it may have resource fields"
                    .into(),
            )],
        });
    }
    for p in &f.params {
        let ok = matches!(p.ty, Ty::Int(_) | Ty::Raw(_) | Ty::ResRef(..) | Ty::Res(_));
        if !ok {
            return Err(Diagnostic {
                name: "extern.param_abi".into(),
                title: format!("`{}` is not an ABI type", p.ty.name()),
                span: p.span,
                label: "extern parameters are integers, raw pointers, and resources".into(),
                notes: vec![(
                    "note".into(),
                    "resources are erased from the ABI, so the foreign function receives \
                     the pointer and the length and nothing else; a safe array or class \
                     would need a layout guarantee Sable does not make yet"
                        .into(),
                )],
            });
        }
        if matches!(p.ty, Ty::Res(kind) | Ty::ResRef(kind, _) if kind.sealed_terminal()) {
            let kind = match p.ty {
                Ty::Res(kind) | Ty::ResRef(kind, _) => kind,
                _ => unreachable!(),
            };
            return Err(Diagnostic {
                name: "resource.release_sealed".into(),
                title: format!(
                    "{} authority may not cross an extern boundary",
                    kind.name()
                ),
                span: p.span,
                label: "compiler-sealed authority is not an extern ABI capability".into(),
                notes: vec![(
                    "note".into(),
                    "resource authority erases at the ABI, so a foreign parameter could \
                     only promise the token away; it could not perform the checked \
                     authority transition"
                        .into(),
                )],
            });
        }
        let mandatory = matches!(p.ty, Ty::Res(kind) if kind.must_consume());
        if p.consumes && !mandatory {
            return Err(Diagnostic {
                name: "resource.consumes_non_mandatory".into(),
                title: format!("`{}` is not mandatory authority", p.name),
                span: p.span,
                label: "`#[consumes]` applies to an owned must-consume resource".into(),
                notes: vec![],
            });
        }
        if mandatory && !p.consumes {
            return Err(Diagnostic {
                name: "resource.extern_must_consume".into(),
                title: format!("extern `{}` could abandon `{}`", f.name, p.name),
                span: p.span,
                label: "mark this audited terminal sink `#[consumes]`".into(),
                notes: vec![(
                    "note".into(),
                    "a foreign declaration has no Sable body in which the checker can \
                     follow mandatory authority; the attribute makes terminal consumption \
                     part of its audited boundary"
                        .into(),
                )],
            });
        }
    }
    Ok(())
}

pub fn check(program: &mut Program) -> CResult<CheckResult> {
    let mut unsafe_regions = 0usize;
    let traits_c: Vec<TraitDecl> = program.traits.clone();
    let mut sigs: HashMap<String, FnSig> = HashMap::new();
    for f in &program.fns {
        if sigs.contains_key(&f.name) {
            return Err(Diagnostic {
                name: "type.duplicate_function".into(),
                title: format!("function `{}` is defined twice", f.name),
                span: f.name_span,
                label: "second definition here".into(),
                notes: vec![],
            });
        }
        if matches!(f.ret, Ty::Array(..)) {
            return Err(Diagnostic {
                name: "type.array_return".into(),
                title: format!("function `{}` returns an array", f.name),
                span: f.name_span,
                label: "arrays are parameters only for now".into(),
                notes: vec![],
            });
        }
        sigs.insert(
            f.name.clone(),
            FnSig {
                params: f.params.clone(),
                ret: f.ret,
            },
        );
    }

    // Class signatures + validation.
    let mut class_metas: Vec<ClassMeta> = Vec::new();
    {
        let mut seen = HashSet::new();
        for c in &program.classes {
            if !seen.insert(c.name.clone()) || sigs.contains_key(&c.name) {
                return Err(Diagnostic {
                    name: "type.duplicate_class".into(),
                    title: format!("`{}` is defined twice", c.name),
                    span: c.name_span,
                    label: "class/function names share one namespace".into(),
                    notes: vec![],
                });
            }
            let mut fields = Vec::new();
            let mut fseen = HashSet::new();
            for fld in &c.fields {
                if !fseen.insert(fld.name.clone()) {
                    return Err(Diagnostic {
                        name: "type.duplicate_field".into(),
                        title: format!("duplicate field `{}`", fld.name),
                        span: fld.span,
                        label: "already declared".into(),
                        notes: vec![],
                    });
                }
                fields.push((fld.name.clone(), fld.ty));
            }
            let scalar_params = |params: &[Param], allow_shared_arrays: bool| -> CResult<()> {
                for p in params {
                    // Class parameters: by value (moved in) or borrowed
                    // (ADR 0020, ADR 0023), and resources — a class that
                    // owns authority takes it in through an init
                    // (ADR 0029).
                    let ok = matches!(
                        p.ty,
                        Ty::Int(_) | Ty::Class(_) | Ty::ClassRef(..) | Ty::Res(_) | Ty::ResRef(..)
                    )
                        || (allow_shared_arrays
                            && matches!(p.ty, Ty::Array(_, Mutability::Shared)));
                    if !ok {
                        return Err(Diagnostic {
                            name: "type.member_param".into(),
                            title: "init/method parameters must be integers for now".into(),
                            span: p.span,
                            label: format!("this has type `{}`", p.ty.name()),
                            notes: vec![],
                        });
                    }
                }
                Ok(())
            };
            let mut inits = Vec::new();
            for i in &c.inits {
                // Inits additionally take `&[T]` (the bignum from_prefix
                // shape: build a class value from computed limbs).
                scalar_params(&i.params, true)?;
                inits.push((i.name.clone(), i.params.clone()));
            }
            let mut methods = Vec::new();
            for m in &c.methods {
                scalar_params(&m.f.params, false)?;
                methods.push((m.f.name.clone(), m.f.params.clone(), m.f.ret, m.self_kind));
            }
            if c.deinit.is_none() {
                if let Some(f) = c
                    .fields
                    .iter()
                    .find(|f| f.must_consume || mandatory_ty(f.ty))
                {
                    let mandatory = mandatory_ty(f.ty);
                    return Err(Diagnostic {
                        name: "resource.abandoned".into(),
                        title: format!("`{}` has no `deinit` to consume `{}`", c.name, f.name),
                        span: f.span,
                        label: if mandatory {
                            "this field's resource type requires consumption".into()
                        } else {
                            "this field is `#[must_consume]`".into()
                        },
                        notes: vec![(
                            "note".into(),
                            if mandatory {
                                "without a destructor there is no path from the field to an \
                                 audited consuming operation, so every value would abandon it"
                                    .into()
                            } else {
                                "without a destructor there is nowhere to hand the authority \
                                 on, so every value of this class would abandon it"
                                    .into()
                            },
                        )],
                    });
                }
            }
            class_metas.push(ClassMeta {
                name: c.name.clone(),
                fields,
                inits,
                methods,
            });
        }
    }

    let mut call_graph: HashMap<String, Vec<String>> = HashMap::new();
    // Operator bindings (ADR 0012): validate each binding's target and
    // signature, and build the (symbol, class) → fn resolution table the
    // Binary rewrite consults.
    let mut operators: HashMap<(OpSym, usize), String> = HashMap::new();
    for ob in &program.operators {
        let Some(sig) = sigs.get(&ob.fn_name) else {
            return Err(Diagnostic {
                name: "op.unknown_fn".into(),
                title: format!(
                    "`operator {}` binds unknown function `{}`",
                    ob.op.symbol(),
                    ob.fn_name
                ),
                span: ob.span,
                label: "no such function".into(),
                notes: vec![],
            });
        };
        let bad_sig = |why: &str| Diagnostic {
            name: "op.bad_signature".into(),
            title: format!(
                "`{}` cannot be bound to `operator {}`",
                ob.fn_name,
                ob.op.symbol()
            ),
            span: ob.span,
            label: why.to_string(),
            notes: vec![],
        };
        let (ci_a, ci_b) = match (
            sig.params.first().map(|p| p.ty),
            sig.params.get(1).map(|p| p.ty),
        ) {
            (Some(Ty::ClassRef(a, Mutability::Shared)), Some(Ty::ClassRef(b, Mutability::Shared)))
                if sig.params.len() == 2 =>
            {
                (a, b)
            }
            _ => return Err(bad_sig("operators bind functions of shape `fn (&C, &C)`")),
        };
        if ci_a != ci_b {
            return Err(bad_sig("both operands must be the same class"));
        }
        match ob.op {
            OpSym::Cmp => {
                if sig.ret != Ty::Int(IntTy::I32) {
                    return Err(bad_sig(
                        "`operator cmp` needs an `i32` result (the −1/0/1 convention)",
                    ));
                }
            }
            _ => {
                if sig.ret != Ty::Class(ci_a) {
                    return Err(bad_sig("arithmetic operators return the operand class"));
                }
            }
        }
        if operators
            .insert((ob.op, ci_a), ob.fn_name.clone())
            .is_some()
        {
            return Err(Diagnostic {
                name: "op.duplicate".into(),
                title: format!(
                    "`operator {}` is bound twice for the same class",
                    ob.op.symbol()
                ),
                span: ob.span,
                label: "second binding here".into(),
                notes: vec![],
            });
        }
    }

    for f in &mut program.fns {
        // An extern has no body to check: its contract is the whole of
        // what is known about it, and the signature is what confines the
        // trust (ADR 0027).
        if f.extern_info.is_some() {
            check_extern_signature(f)?;
            continue;
        }
        let is_test = f.name.starts_with("test_");
        if is_test
            && (f.ret != Ty::Unit
                || !f.params.is_empty()
                || !f.pres.is_empty()
                || !f.posts.is_empty()
                || f.variant.is_some())
        {
            return Err(Diagnostic {
                name: "type.test_shape".into(),
                title: format!(
                    "`{}` is a test but has parameters, a return type, or contracts",
                    f.name
                ),
                span: f.name_span,
                label: "tests are contract-free procedures: `fn test_x() { ... }`".into(),
                notes: vec![(
                    "note".into(),
                    "tests are executed by `sable test` with contracts of the code under \
                     test checked dynamically; they are never verified (design §9)"
                        .into(),
                )],
            });
        }
        let mut ctx = Ctx {
            sigs: &sigs,
            current_fn: f.name.clone(),
            current_has_variant: f.variant.is_some(),
            in_test: is_test,
            vars: HashMap::new(),
            declared: HashSet::new(),
            moved: HashSet::new(),
            marked_fields: MARKED_NONE,
            in_unsafe: false,
            unsafe_blocks: 0,
            calls: Vec::new(),
            in_class: None,
            in_init: false,
            in_deinit: false,
            class_metas: &class_metas,
            tbounds: HashMap::new(),
            operators: &operators,
            traits: &traits_c,
        };
        for p in &f.params {
            if !ctx.declared.insert(p.name.clone()) {
                return Err(Diagnostic {
                    name: "type.duplicate_name".into(),
                    title: format!("duplicate parameter name `{}`", p.name),
                    span: p.span,
                    label: "already declared".into(),
                    notes: vec![],
                });
            }
            if matches!(p.ty, Ty::Option(_)) {
                return Err(Diagnostic {
                    name: "type.option_param".into(),
                    title: "option-typed parameters are not supported yet".into(),
                    span: p.span,
                    label: "`option<T>` is a return type for now".into(),
                    notes: vec![],
                });
            }
            ctx.vars.insert(
                p.name.clone(),
                VarInfo {
                    ty: p.ty,
                    initialized: true,
                    mutable: false,
                    branded: false,
                    obligation: mandatory_ty(p.ty),
                },
            );
        }
        let returns = check_block(&mut ctx, &mut f.body, f.ret)?;
        unsafe_regions += ctx.unsafe_blocks;
        if !returns && f.ret != Ty::Unit {
            return Err(Diagnostic {
                name: "type.missing_return".into(),
                title: format!("not all paths in `{}` return a value", f.name),
                span: f.name_span,
                label: "this function must return on every path".into(),
                notes: vec![],
            });
        }
        if !returns {
            reject_outstanding_obligations(
                &ctx,
                MARKED_NONE,
                f.name_span,
                &f.name,
                true,
            )?;
        }
        call_graph.insert(f.name.clone(), ctx.calls);
    }

    // Fn templates (ADR 0009): typecheck against the abstract model —
    // TParam flows as an ordinary integer type; the TParam-specific
    // gates (literals, conversions, division) fire on the way.
    let mut templates = std::mem::take(&mut program.fn_templates);
    for f in &mut templates {
        let mut ctx = Ctx {
            sigs: &sigs,
            current_fn: f.name.clone(),
            current_has_variant: f.variant.is_some(),
            in_test: false,
            vars: HashMap::new(),
            declared: HashSet::new(),
            moved: HashSet::new(),
            marked_fields: MARKED_NONE,
            in_unsafe: false,
            unsafe_blocks: 0,
            calls: Vec::new(),
            in_class: None,
            in_init: false,
            in_deinit: false,
            class_metas: &class_metas,
            tbounds: tbounds_of(&f.type_params, &f.type_bounds),
            operators: &operators,
            traits: &traits_c,
        };
        for p in &f.params {
            if !ctx.declared.insert(p.name.clone()) {
                return Err(Diagnostic {
                    name: "type.duplicate_name".into(),
                    title: format!("duplicate parameter name `{}`", p.name),
                    span: p.span,
                    label: "already declared".into(),
                    notes: vec![],
                });
            }
            ctx.vars.insert(
                p.name.clone(),
                VarInfo {
                    ty: p.ty,
                    initialized: true,
                    mutable: false,
                        branded: false,
                        obligation: mandatory_ty(p.ty),
                    },
            );
        }
        let returns = check_block(&mut ctx, &mut f.body, f.ret)?;
        unsafe_regions += ctx.unsafe_blocks;
        if !returns && f.ret != Ty::Unit {
            return Err(Diagnostic {
                name: "type.missing_return".into(),
                title: format!("not all paths in `{}` return a value", f.name),
                span: f.name_span,
                label: "this function must return on every path".into(),
                notes: vec![],
            });
        }
        if !returns {
            reject_outstanding_obligations(
                &ctx,
                MARKED_NONE,
                f.name_span,
                &f.name,
                true,
            )?;
        }
    }
    program.fn_templates = templates;

    // Class members.
    for (ci, class) in program.classes.iter_mut().enumerate() {
        let meta = &class_metas[ci];
        // Name and declaration span of every `#[must_consume]` field,
        // snapshotted because the member loops borrow the class mutably.
        let marked: Vec<(String, Span)> = class
            .fields
            .iter()
            .filter(|f| f.must_consume || mandatory_ty(f.ty))
            .map(|f| (f.name.clone(), f.span))
            .collect();
        let class_span = class.name_span;
        for init in &mut class.inits {
            let mut ctx = Ctx {
                sigs: &sigs,
                current_fn: format!("{}::{}", meta.name, init.name),
                current_has_variant: false,
                in_test: false,
                vars: HashMap::new(),
                declared: HashSet::new(),
            moved: HashSet::new(),
            marked_fields: &marked,
            in_unsafe: false,
            unsafe_blocks: 0,
                calls: Vec::new(),
                in_class: Some((ci, true)),
                in_init: true,
            in_deinit: false,
                class_metas: &class_metas,
                tbounds: HashMap::new(),
                operators: &operators,
                traits: &traits_c,
            };
            for p in &init.params {
                ctx.declared.insert(p.name.clone());
                ctx.vars.insert(
                    p.name.clone(),
                    VarInfo {
                        ty: p.ty,
                        initialized: true,
                        mutable: false,
                        branded: false,
                        obligation: mandatory_ty(p.ty),
                    },
                );
            }
            for (fname, fty) in &meta.fields {
                ctx.vars.insert(
                    format!("self.{fname}"),
                    VarInfo {
                        ty: *fty,
                        initialized: false,
                        mutable: true,
                        branded: false,
                        // A field holds nothing yet, so it owes nothing
                        // yet: the first assignment is what puts the
                        // authority there, and what makes the marker bite.
                        obligation: false,
                    },
                );
            }
            check_block(&mut ctx, &mut init.body, Ty::Unit)?;
            unsafe_regions += ctx.unsafe_blocks;
            reject_field_holes(&ctx, &meta.name, &init.name, init.name_span)?;
            reject_outstanding_obligations(&ctx, &marked, class_span, &init.name, false)?;
            for (fname, _) in &meta.fields {
                if !ctx.vars[&format!("self.{fname}")].initialized {
                    return Err(Diagnostic {
                        name: "type.field_uninitialized".into(),
                        title: format!(
                            "`{}::{}` does not initialize field `{fname}` on every path",
                            meta.name, init.name
                        ),
                        span: init.name_span,
                        label: "every field must be assigned before the init returns".into(),
                        notes: vec![],
                    });
                }
            }
            call_graph.insert(ctx.current_fn.clone(), ctx.calls);
        }
        for m in &mut class.methods {
            let mut ctx = Ctx {
                sigs: &sigs,
                current_fn: format!("{}::{}", meta.name, m.f.name),
                current_has_variant: false,
                in_test: false,
                vars: HashMap::new(),
                declared: HashSet::new(),
            moved: HashSet::new(),
            marked_fields: &marked,
            in_unsafe: false,
            unsafe_blocks: 0,
                calls: Vec::new(),
                in_class: Some((ci, m.self_kind == SelfKind::Mut)),
                in_init: false,
            in_deinit: false,
                class_metas: &class_metas,
                tbounds: HashMap::new(),
                operators: &operators,
                traits: &traits_c,
            };
            for p in &m.f.params {
                ctx.declared.insert(p.name.clone());
                ctx.vars.insert(
                    p.name.clone(),
                    VarInfo {
                        ty: p.ty,
                        initialized: true,
                        mutable: false,
                        branded: false,
                        obligation: mandatory_ty(p.ty),
                    },
                );
            }
            for (fname, fty) in &meta.fields {
                ctx.vars.insert(
                    format!("self.{fname}"),
                    VarInfo {
                        ty: *fty,
                        initialized: true,
                        mutable: true,
                        branded: false,
                        obligation: marked_field(&marked, fname),
                    },
                );
            }
            let returns = check_block(&mut ctx, &mut m.f.body, m.f.ret)?;
            unsafe_regions += ctx.unsafe_blocks;
            reject_field_holes(&ctx, &meta.name, &m.f.name, m.f.name_span)?;
            if !returns {
                reject_outstanding_obligations(&ctx, &marked, class_span, &m.f.name, false)?;
            }
            if !returns && m.f.ret != Ty::Unit {
                return Err(Diagnostic {
                    name: "type.missing_return".into(),
                    title: format!(
                        "not all paths in `{}::{}` return a value",
                        meta.name, m.f.name
                    ),
                    span: m.f.name_span,
                    label: "this method must return on every path".into(),
                    notes: vec![],
                });
            }
            call_graph.insert(ctx.current_fn.clone(), ctx.calls);
        }
        // `deinit` — the destructor. Its semantics differ from a method in
        // exactly the ways the value ceasing to exist implies (ADR 0029):
        //
        //   * the class invariant holds on entry and need **not** be
        //     re-established, because there is nothing left to hold it;
        //   * the body may move fields out, which is how a resource-owning
        //     class hands its authority on;
        //   * a moved field is not dropped again, and the rest drop in
        //     reverse declaration order.
        if let Some(body) = &mut class.deinit {
            let mut ctx = Ctx {
                sigs: &sigs,
                current_fn: format!("{}::deinit", meta.name),
                current_has_variant: false,
                in_test: false,
                vars: HashMap::new(),
                declared: HashSet::new(),
                moved: HashSet::new(),
                marked_fields: &marked,
                in_unsafe: false,
                unsafe_blocks: 0,
                calls: Vec::new(),
                // `&mut self`-like: the body owns the value outright.
                in_class: Some((ci, true)),
                in_init: false,
                in_deinit: true,
                class_metas: &class_metas,
                tbounds: HashMap::new(),
                operators: &operators,
                traits: &traits_c,
            };
            for (fname, fty) in &meta.fields {
                ctx.vars.insert(
                    format!("self.{fname}"),
                    VarInfo {
                        ty: *fty,
                        initialized: true,
                        mutable: true,
                        branded: false,
                        obligation: marked_field(&marked, fname),
                    },
                );
            }
            let returns = check_block(&mut ctx, body, Ty::Unit)?;
            unsafe_regions += ctx.unsafe_blocks;
            if returns {
                return Err(Diagnostic {
                    name: "type.return_in_deinit".into(),
                    title: "`return` is not allowed inside `deinit`".into(),
                    span: class.name_span,
                    label: "a destructor runs to the end of its body".into(),
                    notes: vec![(
                        "note".into(),
                        "leaving early would skip the drops that follow the body".into(),
                    )],
                });
            }
            // `#[must_consume]`: the field's authority has to be handed on.
            // An ordinary affine field may be abandoned — that is a leak,
            // and affine-not-linear authority permits leaks.
            //
            // The obligation travels with the token, so this asks about
            // every place that holds one and not only about the field:
            // moving it into a local and dropping the local abandons the
            // authority exactly as leaving it in the field does. What
            // discharges it is passing it *by value* to something that
            // takes it — which is why the check is "still live here", not
            // "was moved at some point".
            reject_outstanding_obligations(&ctx, &marked, class_span, "deinit", true)?;
            call_graph.insert(ctx.current_fn.clone(), ctx.calls);
        }
    }

    // Class templates (ADR 0009): members typecheck against the
    // abstract model; TParam flows as an ordinary integer type. Template
    // bodies may not reference other classes (their metas are not in
    // scope here) — diagnosed as unknown names.
    let mut ctemplates = std::mem::take(&mut program.class_templates);
    {
        let mut tmetas: Vec<ClassMeta> = Vec::new();
        for c in &ctemplates {
            let mut fields = Vec::new();
            let mut fseen = HashSet::new();
            for fld in &c.fields {
                if !fseen.insert(fld.name.clone()) {
                    return Err(Diagnostic {
                        name: "type.duplicate_field".into(),
                        title: format!("duplicate field `{}`", fld.name),
                        span: fld.span,
                        label: "already declared".into(),
                        notes: vec![],
                    });
                }
                fields.push((fld.name.clone(), fld.ty));
            }
            tmetas.push(ClassMeta {
                name: c.name.clone(),
                fields,
                inits: c
                    .inits
                    .iter()
                    .map(|i| (i.name.clone(), i.params.clone()))
                    .collect(),
                methods: c
                    .methods
                    .iter()
                    .map(|m| (m.f.name.clone(), m.f.params.clone(), m.f.ret, m.self_kind))
                    .collect(),
            });
        }
        for (ci, class) in ctemplates.iter_mut().enumerate() {
            let meta = &tmetas[ci];
            let ctb = class_tbounds(class);
            // A template's members answer to the same ownership rules as a
            // monomorphic class's. Verifying a generic once at the template
            // (ADR 0009) is only a saving if what it verifies is the same
            // thing.
            let marked: Vec<(String, Span)> = class
                .fields
                .iter()
                .filter(|f| f.must_consume || mandatory_ty(f.ty))
                .map(|f| (f.name.clone(), f.span))
                .collect();
            let class_span = class.name_span;
            for init in &mut class.inits {
                let mut ctx = Ctx {
                    sigs: &sigs,
                    current_fn: format!("{}::{}", meta.name, init.name),
                    current_has_variant: false,
                    in_test: false,
                    vars: HashMap::new(),
                    declared: HashSet::new(),
            moved: HashSet::new(),
            marked_fields: &marked,
            in_unsafe: false,
            unsafe_blocks: 0,
                    calls: Vec::new(),
                    in_class: Some((ci, true)),
                    in_init: true,
            in_deinit: false,
                    class_metas: &tmetas,
                    tbounds: ctb.clone(),
                    operators: &operators,
                    traits: &traits_c,
                };
                for p in &init.params {
                    ctx.declared.insert(p.name.clone());
                    ctx.vars.insert(
                        p.name.clone(),
                        VarInfo {
                            ty: p.ty,
                            initialized: true,
                            mutable: false,
                            branded: false,
                            obligation: mandatory_ty(p.ty),
                    },
                    );
                }
                for (fname, fty) in &meta.fields {
                    ctx.vars.insert(
                        format!("self.{fname}"),
                        VarInfo {
                            ty: *fty,
                            initialized: false,
                            mutable: true,
                            branded: false,
                            obligation: false,
                    },
                    );
                }
                check_block(&mut ctx, &mut init.body, Ty::Unit)?;
                unsafe_regions += ctx.unsafe_blocks;
                reject_field_holes(&ctx, &meta.name, &init.name, init.name_span)?;
                reject_outstanding_obligations(&ctx, &marked, class_span, &init.name, false)?;
                for (fname, _) in &meta.fields {
                    if !ctx.vars[&format!("self.{fname}")].initialized {
                        return Err(Diagnostic {
                            name: "type.field_uninitialized".into(),
                            title: format!(
                                "`{}::{}` does not initialize field `{fname}` on every path",
                                meta.name, init.name
                            ),
                            span: init.name_span,
                            label: "every field must be assigned before the init returns".into(),
                            notes: vec![],
                        });
                    }
                }
            }
            for m in &mut class.methods {
                let mut ctx = Ctx {
                    sigs: &sigs,
                    current_fn: format!("{}::{}", meta.name, m.f.name),
                    current_has_variant: false,
                    in_test: false,
                    vars: HashMap::new(),
                    declared: HashSet::new(),
            moved: HashSet::new(),
            marked_fields: &marked,
            in_unsafe: false,
            unsafe_blocks: 0,
                    calls: Vec::new(),
                    in_class: Some((ci, m.self_kind == SelfKind::Mut)),
                    in_init: false,
            in_deinit: false,
                    class_metas: &tmetas,
                    tbounds: ctb.clone(),
                    operators: &operators,
                    traits: &traits_c,
                };
                for p in &m.f.params {
                    ctx.declared.insert(p.name.clone());
                    ctx.vars.insert(
                        p.name.clone(),
                        VarInfo {
                            ty: p.ty,
                            initialized: true,
                            mutable: false,
                        branded: false,
                        obligation: mandatory_ty(p.ty),
                    },
                    );
                }
                for (fname, fty) in &meta.fields {
                    ctx.vars.insert(
                        format!("self.{fname}"),
                        VarInfo {
                            ty: *fty,
                            initialized: true,
                            mutable: true,
                        branded: false,
                        obligation: marked_field(&marked, fname),
                    },
                    );
                }
                let returns = check_block(&mut ctx, &mut m.f.body, m.f.ret)?;
                unsafe_regions += ctx.unsafe_blocks;
                reject_field_holes(&ctx, &meta.name, &m.f.name, m.f.name_span)?;
                if !returns {
                    reject_outstanding_obligations(
                        &ctx,
                        &marked,
                        class_span,
                        &m.f.name,
                        false,
                    )?;
                }
                if !returns && m.f.ret != Ty::Unit {
                    return Err(Diagnostic {
                        name: "type.missing_return".into(),
                        title: format!(
                            "not all paths in `{}::{}` return a value",
                            meta.name, m.f.name
                        ),
                        span: m.f.name_span,
                        label: "this method must return on every path".into(),
                        notes: vec![],
                    });
                }
            }
            // A template's destructor is checked exactly as a monomorphic
            // one is. Skipping it would leave the one member where fields
            // may be moved out unchecked, and generic resource-owning
            // classes are the ones that need it most.
            if let Some(body) = &mut class.deinit {
                let mut ctx = Ctx {
                    sigs: &sigs,
                    current_fn: format!("{}::deinit", meta.name),
                    current_has_variant: false,
                    in_test: false,
                    vars: HashMap::new(),
                    declared: HashSet::new(),
                    moved: HashSet::new(),
                    marked_fields: &marked,
                    in_unsafe: false,
                    unsafe_blocks: 0,
                    calls: Vec::new(),
                    in_class: Some((ci, true)),
                    in_init: false,
                    in_deinit: true,
                    class_metas: &tmetas,
                    tbounds: ctb.clone(),
                    operators: &operators,
                    traits: &traits_c,
                };
                for (fname, fty) in &meta.fields {
                    ctx.vars.insert(
                        format!("self.{fname}"),
                        VarInfo {
                            ty: *fty,
                            initialized: true,
                            mutable: true,
                            branded: false,
                            obligation: marked_field(&marked, fname),
                        },
                    );
                }
                let returns = check_block(&mut ctx, body, Ty::Unit)?;
                unsafe_regions += ctx.unsafe_blocks;
                if returns {
                    return Err(Diagnostic {
                        name: "type.return_in_deinit".into(),
                        title: "`return` is not allowed inside `deinit`".into(),
                        span: class_span,
                        label: "a destructor runs to the end of its body".into(),
                        notes: vec![(
                            "note".into(),
                            "leaving early would skip the drops that follow the body".into(),
                        )],
                    });
                }
                reject_outstanding_obligations(&ctx, &marked, class_span, "deinit", true)?;
            }
        }
    }
    program.class_templates = ctemplates;

    // Mutual recursion (self-recursion with a variant is handled inline).
    if let Some(cycle_member) = find_cycle(&call_graph) {
        let f = program.fns.iter().find(|f| f.name == cycle_member).unwrap();
        return Err(Diagnostic {
            name: "type.mutual_recursion".into(),
            title: format!("`{}` is mutually recursive", f.name),
            span: f.name_span,
            label: "mutual recursion is not supported yet (self-recursion with `variant` is)"
                .into(),
            notes: vec![("note".into(), "see docs/PLAN.md".into())],
        });
    }

    Ok(CheckResult {
        sigs,
        unsafe_regions,
    })
}

/// Returns whether every path through the block returns.
fn check_block(ctx: &mut Ctx, stmts: &mut [Stmt], ret_ty: Ty) -> CResult<bool> {
    let mut returned = false;
    for stmt in stmts.iter_mut() {
        if returned {
            let span = stmt_span(stmt);
            return Err(Diagnostic {
                name: "type.unreachable".into(),
                title: "unreachable statement".into(),
                span,
                label: "every path above has already returned".into(),
                notes: vec![],
            });
        }
        match stmt {
            Stmt::Decl {
                ty,
                name,
                name_span,
                init,
                mutable,
            } => {
                if !ctx.declared.insert(name.clone()) {
                    return Err(Diagnostic {
                        name: "type.duplicate_name".into(),
                        title: format!("duplicate variable name `{name}`"),
                        span: *name_span,
                        label: "already declared in this function".into(),
                        notes: vec![(
                            "note".into(),
                            "all locals in a function must have distinct names".into(),
                        )],
                    });
                }
                let alloc_init = matches!(
                    init.as_ref().map(|e| &e.kind),
                    Some(ExprKind::AllocArray { .. }) | Some(ExprKind::ArrayLit(_))
                );
                if matches!(ty, Ty::Array(_, Mutability::Owned)) && !ctx.in_test && !alloc_init {
                    return Err(Diagnostic {
                        name: "type.owned_array_outside_test".into(),
                        title: "owned arrays exist only in test functions for now".into(),
                        span: *name_span,
                        label: "allocation design is a scheduled deliverable (see the goals doc)"
                            .into(),
                        notes: vec![],
                    });
                }
                let mut branded = false;
                let mut must_consume = false;
                if let Some(e) = init {
                    check_expr(ctx, e, Some(*ty))?;
                    // A local initialized from branded storage is branded
                    // — but only if it *names* storage. A byte loaded out
                    // of raw memory is an ordinary number, and branding it
                    // would forbid returning the very thing the raw
                    // operations exist to produce.
                    branded = matches!(ty, Ty::Raw(_) | Ty::Res(_)) && brand_of(ctx, e);
                    // `resource RawSpan t = s;` — a local-to-local move,
                    // the same rule classes follow (ADR 0020/0024). A
                    // declaration is not an escape: the new local inherits
                    // the brand rather than laundering it.
                    must_consume = transfer(ctx, e, None)?;
                }
                ctx.vars.insert(
                    name.clone(),
                    VarInfo {
                        ty: *ty,
                        initialized: init.is_some(),
                        mutable: *mutable,
                        branded,
                        obligation: must_consume,
                    },
                );
            }
            Stmt::Assign {
                name,
                name_span,
                value,
            } => {
                let (ty, was_mutable) = match ctx.vars.get(name.as_str()) {
                    Some(v) => (v.ty, v.mutable),
                    None => {
                        return Err(Diagnostic {
                            name: "type.unknown_variable".into(),
                            title: format!("assignment to undeclared variable `{name}`"),
                            span: *name_span,
                            label: "not declared".into(),
                            notes: vec![],
                        });
                    }
                };
                let dest_branded = ctx
                    .vars
                    .get(name.as_str())
                    .is_some_and(|v| v.branded);
                if !was_mutable {
                    return Err(Diagnostic {
                        name: "mut.assign_immutable".into(),
                        title: format!("assignment to immutable local `{name}`"),
                        span: *name_span,
                        label: "declare it `mut` to allow assignment".into(),
                        notes: vec![],
                    });
                }
                if matches!(ty, Ty::Class(_) | Ty::Res(_)) {
                    // Reassignment of a class local is a move-in of an
                    // owned value; the old value is dropped, with its
                    // RAII invariant check. Check first: operator sugar
                    // may rewrite a Binary RHS into the bound call
                    // (ADR 0012). A resource local follows the same rule,
                    // and dropping the old token discards its authority
                    // rather than running anything (ADR 0024).
                    check_expr(ctx, value, Some(ty))?;
                    // A bare name is a local-to-local move: the source
                    // place dies here (ADR 0020). Every other class-typed
                    // expression is a call or a construction — a fresh
                    // owned value that nothing else names.
                    let dest = Place::local(name);
                    reject_overwrite_of_obligation(ctx, &dest, *name_span)?;
                    let carries = transfer(ctx, value, escape_sink(dest_branded, name_span))?;
                    // The destination owns a value again even if it had
                    // been moved out earlier.
                    ctx.moved.retain(|m| !dest.contains(m));
                    let v = ctx.vars.get_mut(name.as_str()).unwrap();
                    v.initialized = true;
                    // The local now holds whatever obligation the value
                    // brought, and no longer the previous one.
                    v.obligation = carries;
                } else {
                    if matches!(ty, Ty::Array(..)) {
                        return Err(Diagnostic {
                            name: "type.array_assign".into(),
                            title: format!("cannot assign to array `{name}`"),
                            span: *name_span,
                            label: "arrays cannot be rebound; element stores use `a[i] = v`".into(),
                            notes: vec![],
                        });
                    }
                    check_expr(ctx, value, Some(ty))?;
                    transfer(ctx, value, escape_sink(dest_branded, name_span))?;
                    ctx.vars.get_mut(name.as_str()).unwrap().initialized = true;
                }
            }

            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                check_expr(ctx, cond, Some(Ty::Bool))?;
                // Every flow fact is per-path. A name is initialized after
                // the `if` iff every falling-through branch initialized it;
                // it is moved-out iff any of them moved it; and it is
                // branded, or still owes a `#[must_consume]` obligation,
                // iff some reaching branch left it that way. A branch that
                // returns contributes none of them.
                //
                // The whole per-place state travels together: a fact
                // carried by `VarInfo` and *not* snapshotted here would
                // leak out of whichever branch the checker happened to
                // walk last, which is traversal order deciding a rule.
                let before = snapshot(ctx);
                let before_moved = ctx.moved.clone();
                let then_ret = check_block(ctx, then_block, ret_ty)?;
                let after_then = snapshot(ctx);
                let after_then_moved = ctx.moved.clone();
                restore(ctx, &before);
                ctx.moved = before_moved.clone();
                let else_ret = match else_block {
                    Some(b) => check_block(ctx, b, ret_ty)?,
                    None => false,
                };
                let after_else = snapshot(ctx);
                let after_else_moved = ctx.moved.clone();
                // Reaching branches only: a branch that returns
                // contributes nothing to the fall-through state.
                let mut reaching_init: Vec<&HashMap<String, PlaceState>> = Vec::new();
                let mut reaching_moved: Vec<&HashSet<Place>> = Vec::new();
                if !then_ret {
                    reaching_init.push(&after_then);
                    reaching_moved.push(&after_then_moved);
                }
                if !else_ret {
                    match else_block {
                        Some(_) => {
                            reaching_init.push(&after_else);
                            reaching_moved.push(&after_else_moved);
                        }
                        None => {
                            reaching_init.push(&before);
                            reaching_moved.push(&before_moved);
                        }
                    }
                }
                for (name, v) in ctx.vars.iter_mut() {
                    let was = before.get(name).cloned().unwrap_or(PlaceState {
                        initialized: v.initialized,
                        branded: v.branded,
                        obligation: v.obligation,
                    });
                    if reaching_init.is_empty() {
                        v.initialized = was.initialized;
                        v.branded = was.branded;
                        v.obligation = was.obligation;
                        continue;
                    }
                    let states = || reaching_init.iter().map(|m| m.get(name).unwrap_or(&was));
                    v.initialized = states().all(|st| st.initialized);
                    v.branded = states().any(|st| st.branded);
                    // Outstanding after the branch iff some reaching path
                    // left it outstanding: a token consumed on one path and
                    // abandoned on the other is abandoned.
                    v.obligation = states().any(|st| st.obligation);
                }
                // Resource shape must agree across reaching branches
                // (ADR 0024): a token moved on one path and not the other
                // is a leak on one of them, and the checker should say so
                // rather than quietly taking the dead union. Ordinary
                // class values take the union — dropping one runs its
                // deinit and costs nothing but the value.
                if reaching_moved.len() > 1 {
                    let (first, rest) = reaching_moved.split_first().expect("checked: len > 1");
                    for other in rest {
                        // Only resources that existed before the branch
                        // are part of its shape: one declared and
                        // consumed inside a branch never outlives it.
                        let differ = first
                            .symmetric_difference(other)
                            .find(|p| ctx.is_resource_place(p) && snapshot_has_place(&before, p));
                        if let Some(p) = differ {
                            return Err(Diagnostic {
                                name: "resource.branch_shape".into(),
                                title: format!(
                                    "`{}` is consumed on one branch but not the other",
                                    p.render()
                                ),
                                span: cond.span,
                                label: "the branches leave different resources live".into(),
                                notes: vec![(
                                    "note".into(),
                                    "every fall-through branch must leave the same resources \
                                     live; consume it on both paths or on neither"
                                        .into(),
                                )],
                            });
                        }
                    }
                }
                // Moved on any reaching path means dead below.
                ctx.moved = if reaching_moved.is_empty() {
                    before_moved
                } else {
                    reaching_moved.iter().flat_map(|s| s.iter().cloned()).collect()
                };
                returned = then_ret && else_ret;
            }
            Stmt::While {
                cond,
                variant,
                kw_span,
                body,
                ..
            } => {
                if variant.is_none() {
                    return Err(Diagnostic {
                        name: "proof.missing_variant".into(),
                        title: "loop has no `variant`".into(),
                        span: *kw_span,
                        label: "every loop must declare a decreasing measure (design §4)".into(),
                        notes: vec![(
                            "note".into(),
                            "add `/// variant <ghost nat expression>` directly above the loop"
                                .into(),
                        )],
                    });
                }
                check_expr(ctx, cond, Some(Ty::Bool))?;
                // The body may run zero times: check it against the entry
                // state, then restore the entry state (body-declared locals
                // become uninitialized after the loop).
                let before = snapshot(ctx);
                let before_moved = ctx.moved.clone();
                let _body_ret = check_block(ctx, body, ret_ty)?;
                // Affine shape must be preserved at the backedge
                // (ADR 0024): a value consumed by the body is not there
                // for the second iteration, and a resource created per
                // iteration and never consumed leaks one per turn. Views
                // may change freely — that is what the loop invariant is
                // for; the *shape* is what must come back.
                // Only values live at the loop head are part of the
                // shape. One declared and consumed inside the body is
                // per-iteration scratch, not something the backedge owes.
                if let Some(p) = ctx.moved.symmetric_difference(&before_moved).find(|p| {
                    ctx.place_ty(p).is_some_and(is_affine) && snapshot_has_place(&before, p)
                }) {
                    return Err(Diagnostic {
                        name: format!("{}.loop_shape", ctx.affine_kind(p)),
                        title: format!("the loop body consumes `{}`", p.render()),
                        span: *kw_span,
                        label: "the second iteration would not have it".into(),
                        notes: vec![(
                            "note".into(),
                            "a loop must leave the same values live at the backedge as at \
                             the head; an invariant carries what they are, not whether \
                             they are still there"
                                .into(),
                        )],
                    });
                }
                // The values may all still be live while ownership state
                // migrates between them. Restoring the loop-head snapshot
                // would then forget which value names loaned storage or
                // carries a must-consume token. Those are part of the
                // static backedge shape, unlike initialization (the loop
                // may run zero times) and resource views (loop invariants
                // describe how those change).
                let after = snapshot(ctx);
                for (name, was) in &before {
                    let Some(now) = after.get(name) else {
                        continue;
                    };
                    if was.branded != now.branded {
                        return Err(Diagnostic {
                            name: "expose.brand_escapes".into(),
                            title: format!("the loop changes the loan state of `{name}`"),
                            span: *kw_span,
                            label: "the next iteration would name a different exposure lifetime"
                                .into(),
                            notes: vec![(
                                "note".into(),
                                "a loop must leave loan brands on the same places at the backedge; \
                                 only the resource views may change under an invariant"
                                    .into(),
                            )],
                        });
                    }
                    if was.obligation != now.obligation {
                        return Err(Diagnostic {
                            name: "resource.loop_shape".into(),
                            title: format!(
                                "the loop changes the must-consume state of `{name}`"
                            ),
                            span: *kw_span,
                            label: "the backedge leaves the obligation on a different place".into(),
                            notes: vec![(
                                "note".into(),
                                "a loop must leave must-consume obligations on the same places at \
                                 the backedge; restoring the loop-head state must not forget a \
                                 token that moved elsewhere"
                                    .into(),
                            )],
                        });
                    }
                }
                // The body may run zero times, so the state after the loop
                // is the state before it. A body that consumed something
                // live at the head was already rejected above, which is
                // what makes restoring an obligation here correct rather
                // than merely conservative.
                ctx.moved = before_moved;
                restore(ctx, &before);
            }
            Stmt::Return { value, span } => {
                if ctx.in_init {
                    return Err(Diagnostic {
                        name: "type.return_in_init".into(),
                        title: "`return` is not allowed inside `init`".into(),
                        span: *span,
                        label: "an init runs to the end of its body".into(),
                        notes: vec![],
                    });
                }
                match (value, ret_ty) {
                    (None, Ty::Unit) => {}
                    (Some(e), Ty::Unit) => {
                        return Err(Diagnostic {
                            name: "type.return_value_in_procedure".into(),
                            title: "this function has no return type".into(),
                            span: e.span,
                            label: "remove the value (or declare `-> T`)".into(),
                            notes: vec![],
                        });
                    }
                    (None, _) => {
                        return Err(Diagnostic {
                            name: "type.missing_return_value".into(),
                            title: format!("`return;` in a function returning `{}`", ret_ty.name()),
                            span: *span,
                            label: "a value is required".into(),
                            notes: vec![],
                        });
                    }
                    (Some(e), _) => {
                        check_expr(ctx, e, Some(ret_ty))?;
                        // Returning a place consumes it: the value leaves
                        // with the caller, and a field returned this way is
                        // authority the object no longer has.
                        transfer(ctx, e, Some(("be returned", e.span)))?;
                    }
                }
                // A return is a frame exit on this path. Mandatory
                // resource parameters and locals must already have
                // reached a consuming boundary (or be the returned
                // value, whose transfer above moved the obligation to
                // the caller). An ordinary method may retain authority
                // in `self`; that object outlives this frame.
                let current = ctx.current_fn.clone();
                reject_outstanding_obligations(
                    ctx,
                    ctx.marked_fields,
                    *span,
                    &current,
                    ctx.in_class.is_none() || ctx.in_deinit,
                )?;
                returned = true;
            }
            Stmt::ExprStmt(e) => {
                let ty = check_expr(ctx, e, None)?;
                if mandatory_ty(ty) {
                    return Err(Diagnostic {
                        name: "resource.abandoned".into(),
                        title: format!(
                            "discarding this `{}` abandons mandatory authority",
                            ty.name()
                        ),
                        span: e.span,
                        label: "bind it and hand it to a consuming operation".into(),
                        notes: vec![],
                    });
                }
            }
            Stmt::VarDecl {
                name,
                name_span,
                init,
                mutable,
                ty,
            } => {
                if !ctx.declared.insert(name.clone()) {
                    return Err(Diagnostic {
                        name: "type.duplicate_name".into(),
                        title: format!("duplicate variable name `{name}`"),
                        span: *name_span,
                        label: "already declared in this function".into(),
                        notes: vec![],
                    });
                }
                // `var d = c;` — a local-to-local move (ADR 0020). A bare
                // name is not otherwise a class-typed expression, so the
                // expected type has to be supplied here for the move to
                // be legal at all. `var x = self.f;` moves a field the
                // same way.
                let moved_from = match &init.kind {
                    ExprKind::Var(src) => match ctx.vars.get(src.as_str()).map(|v| v.ty) {
                        Some(Ty::Class(ci)) => Some(ci),
                        _ => None,
                    },
                    ExprKind::SelfField { field } => {
                        match ctx.vars.get(format!("self.{field}").as_str()).map(|v| v.ty) {
                            Some(Ty::Class(ci)) => Some(ci),
                            _ => None,
                        }
                    }
                    _ => None,
                };
                let t = match moved_from {
                    Some(ci) => {
                        check_expr(ctx, init, Some(Ty::Class(ci)))?;
                        Ty::Class(ci)
                    }
                    None => check_expr(ctx, init, None)?,
                };
                // A declaration takes the value like any other sink, and
                // is not an escape: the new local inherits the brand
                // rather than laundering it — which only works if the
                // brand is actually computed here, exactly as a typed
                // declaration computes it.
                let branded = matches!(t, Ty::Raw(_) | Ty::Res(_)) && brand_of(ctx, init);
                let must_consume = transfer(ctx, init, None)?;
                if t == Ty::Unit {
                    return Err(Diagnostic {
                        name: "type.unit_binding".into(),
                        title: "cannot bind the result of a procedure".into(),
                        span: init.span,
                        label: "this expression has no value".into(),
                        notes: vec![],
                    });
                }
                *ty = Some(t);
                ctx.vars.insert(
                    name.clone(),
                    VarInfo {
                        ty: t,
                        initialized: true,
                        mutable: *mutable,
                        branded,
                        obligation: must_consume,
                    },
                );
            }
            // `unsafe { ... }` is a marker, not a scope: locals declared
            // inside outlive the block, exactly as in an `if` body would
            // not — the block only licenses raw operations (ADR 0026).
            Stmt::Unsafe { body, .. } => {
                let outer = ctx.in_unsafe;
                ctx.in_unsafe = true;
                ctx.unsafe_blocks += 1;
                let r = check_block(ctx, body, ret_ty);
                ctx.in_unsafe = outer;
                returned = r?;
            }
            Stmt::StaticAlloc {
                size,
                ptr,
                ptr_span,
                res,
                res_span,
                ..
            } => {
                check_expr(ctx, size, Some(Ty::Int(IntTy::U64)))?;
                let ExprKind::IntLit(n) = size.kind else {
                    return Err(Diagnostic {
                        name: "static_root.literal_size".into(),
                        title: "a static root needs a compile-time literal size".into(),
                        span: size.span,
                        label: "use an integer literal from 1 through 50000000".into(),
                        notes: vec![],
                    });
                };
                if !(1..=50_000_000).contains(&n) {
                    return Err(Diagnostic {
                        name: "static_root.size".into(),
                        title: format!("static root size {n} is outside the supported profile"),
                        span: size.span,
                        label: "expected 1 through 50000000 bytes".into(),
                        notes: vec![],
                    });
                }
                for (name, span, ty, mutable) in [
                    (ptr.as_str(), ptr_span, Ty::Raw(IntTy::U8), false),
                    (res.as_str(), res_span, Ty::Res(ResKind::RawSpan), true),
                ] {
                    if !ctx.declared.insert(name.to_string()) {
                        return Err(Diagnostic {
                            name: "type.duplicate_name".into(),
                            title: format!("duplicate variable name `{name}`"),
                            span: *span,
                            label: "already declared in this function".into(),
                            notes: vec![],
                        });
                    }
                    ctx.vars.insert(name.to_string(), VarInfo {
                        ty, initialized: true, mutable, branded: false, obligation: false,
                    });
                }
                ctx.unsafe_blocks += 1;
            }
            Stmt::SystemAlloc {
                size,
                ptr,
                ptr_span,
                res,
                res_span,
                release,
                release_span,
                ..
            } => {
                check_expr(ctx, size, Some(Ty::Int(IntTy::U64)))?;
                let ExprKind::IntLit(n) = size.kind else {
                    return Err(Diagnostic {
                        name: "system_root.literal_size".into(),
                        title: "a system root needs a compile-time literal size".into(),
                        span: size.span,
                        label: "use an integer literal from 1 through 50000000".into(),
                        notes: vec![],
                    });
                };
                if !(1..=50_000_000).contains(&n) {
                    return Err(Diagnostic {
                        name: "system_root.size".into(),
                        title: format!("system root size {n} is outside the supported profile"),
                        span: size.span,
                        label: "expected 1 through 50000000 bytes".into(),
                        notes: vec![],
                    });
                }
                for (name, span, ty, mutable) in [
                    (ptr.as_str(), ptr_span, Ty::Raw(IntTy::U8), false),
                    (res.as_str(), res_span, Ty::Res(ResKind::RawSpan), true),
                    (
                        release.as_str(),
                        release_span,
                        Ty::Res(ResKind::SystemDealloc),
                        false,
                    ),
                ] {
                    if !ctx.declared.insert(name.to_string()) {
                        return Err(Diagnostic {
                            name: "type.duplicate_name".into(),
                            title: format!("duplicate variable name `{name}`"),
                            span: *span,
                            label: "already declared in this function".into(),
                            notes: vec![],
                        });
                    }
                    ctx.vars.insert(
                        name.to_string(),
                        VarInfo {
                            ty,
                            initialized: true,
                            mutable,
                            branded: false,
                            obligation: mandatory_ty(ty),
                        },
                    );
                }
                ctx.unsafe_blocks += 1;
            }
            Stmt::SystemDealloc {
                ptr,
                res,
                release,
                ..
            } => {
                check_expr(ctx, ptr, Some(Ty::Raw(IntTy::U8)))?;
                check_expr(ctx, res, Some(Ty::Res(ResKind::RawSpan)))?;
                transfer(ctx, res, None)?;
                check_expr(ctx, release, Some(Ty::Res(ResKind::SystemDealloc)))?;
                transfer(ctx, release, None)?;
                ctx.unsafe_blocks += 1;
            }
            Stmt::Expose {
                kw_span,
                array,
                array_span,
                mutable,
                ptr,
                ptr_span,
                res,
                res_span,
                body,
            } => {
                let (elem, src_mut, declared_mut) = match ctx.vars.get(array.as_str()) {
                    Some(v) => match v.ty {
                        Ty::Array(e, m) => (e, m, v.mutable),
                        _ => {
                            return Err(Diagnostic {
                                name: "expose.not_an_array".into(),
                                title: format!("`{array}` is not an array"),
                                span: *array_span,
                                label: format!("this has type `{}`", v.ty.name()),
                                notes: vec![],
                            });
                        }
                    },
                    None => {
                        return Err(Diagnostic {
                            name: "type.unknown_variable".into(),
                            title: format!("unknown variable `{array}`"),
                            span: *array_span,
                            label: "not declared".into(),
                            notes: vec![],
                        });
                    }
                };
                if elem != IntTy::U8 {
                    return Err(Diagnostic {
                        name: "expose.element_type".into(),
                        title: format!("cannot expose `[{}]` as bytes yet", elem.name()),
                        span: *array_span,
                        label: "only `u8` arrays for now".into(),
                        notes: vec![(
                            "note".into(),
                            "a wider element would make the byte order part of the \
                             contract, and layout is a scheduled deliverable"
                                .into(),
                        )],
                    });
                }
                if *mutable {
                    if src_mut == Mutability::Shared {
                        return Err(Diagnostic {
                            name: "expose.mutate_shared".into(),
                            title: format!("cannot expose `{array}` mutably"),
                            span: *array_span,
                            label: "this array is a shared borrow".into(),
                            notes: vec![],
                        });
                    }
                    if src_mut == Mutability::Owned && !declared_mut {
                        return Err(Diagnostic {
                            name: "mut.borrow_immutable".into(),
                            title: format!("`&mut` exposure of immutable local `{array}`"),
                            span: *array_span,
                            label: "declare it `mut` to allow mutable exposure".into(),
                            notes: vec![],
                        });
                    }
                }
                // Everything in scope before the loan opens. What the
                // exposure adds — its two bindings, and whatever the body
                // declares — goes away with it.
                let declared_before: HashSet<String> = ctx.vars.keys().cloned().collect();
                // The two bindings carry the loan brand. They name storage
                // that exists only for this body, so nothing derived from
                // them may outlive it.
                for (name, span, ty) in [
                    (ptr.as_str(), ptr_span, Ty::Raw(IntTy::U8)),
                    (res.as_str(), res_span, Ty::Res(ResKind::RawSpan)),
                ] {
                    if !ctx.declared.insert(name.to_string()) {
                        return Err(Diagnostic {
                            name: "type.duplicate_name".into(),
                            title: format!("duplicate variable name `{name}`"),
                            span: *span,
                            label: "already declared in this function".into(),
                            notes: vec![],
                        });
                    }
                    ctx.vars.insert(
                        name.to_string(),
                        VarInfo {
                            ty,
                            initialized: true,
                            // A mutable exposure's resource may be split
                            // and rejoined, which needs `&mut m`; a shared
                            // one may not, which is how "shared exposure
                            // cannot mutate" is enforced rather than
                            // proved.
                            mutable: *mutable,
                            branded: true,
                            obligation: false,
                        },
                    );
                }
                // Raw operations are legal in an exposure body without a
                // nested `unsafe`: `unsafe expose` already said the word.
                let outer = ctx.in_unsafe;
                ctx.in_unsafe = true;
                ctx.unsafe_blocks += 1;
                let r = check_block(ctx, body, ret_ty);
                ctx.in_unsafe = outer;
                let body_returned = r?;
                if body_returned {
                    return Err(Diagnostic {
                        name: "expose.return_from_body".into(),
                        title: "cannot return from inside an exposure".into(),
                        span: *kw_span,
                        label: "the array has to be reconstructed first".into(),
                        notes: vec![(
                            "note".into(),
                            "leaving the body is what puts the bytes back; a `return` \
                             would skip that"
                                .into(),
                        )],
                    });
                }
                // The resource must still be owned here: the whole extent
                // has to come back, and a split descendant has to be
                // rejoined explicitly (the extent obligation checks that
                // it covers everything).
                if ctx.is_moved(&Place::local(res)) {
                    return Err(Diagnostic {
                        name: "expose.resource_lost".into(),
                        title: format!("`{res}` does not come back at the end of the body"),
                        span: *kw_span,
                        label: "the exposed storage was moved away".into(),
                        notes: vec![(
                            "note".into(),
                            "the array is reconstructed from this resource's bytes, so it \
                             must still be owned here; rejoin what was split off"
                                .into(),
                        )],
                    });
                }
                // An exposure body *is* a scope, and this is the one place
                // in the language where that matters: the loan ends here.
                // Its own bindings go, and so does everything declared
                // inside — a local derived from `p` or `m` names storage
                // the safe world owns again, and letting it keep a name
                // would leave a value the brand rule has to chase forever
                // (ADR 0030). `unsafe { ... }` is the opposite case: it
                // grants vocabulary, has no lifetime, and is not a scope.
                //
                // Names stay reserved in `ctx.declared`, so nothing later
                // reuses one and reads as a reference to what is gone.
                reject_scoped_obligations(ctx, &declared_before, *kw_span)?;
                ctx.vars.retain(|name, _| declared_before.contains(name));
                ctx.moved
                    .retain(|p| declared_before.contains(&p.state_key()));
            }
            Stmt::Assert(_) => {
                // Proof language: elaborated by Lean (well-formedness def)
                // and evaluated by the monitor; nothing to typecheck.
            }
            Stmt::FieldAssign {
                field,
                field_span,
                value,
            } => {
                let fty = ctx.self_field_ty_rebind(field, *field_span, true)?;
                // Array fields accept an owned-array MOVE (`self.buf = nb;`
                // — Vec growth) or a fresh allocation; the moved-from local
                // is not tracked as dead in v1 (documented).
                let mut checked = false;
                if let Ty::Array(elem, _) = fty {
                    match &value.kind {
                        ExprKind::Var(name) => match ctx.vars.get(name.as_str()).map(|v| v.ty) {
                            Some(Ty::Array(e2, Mutability::Owned)) if e2 == elem => {
                                value.ty = Some(Ty::Array(e2, Mutability::Owned));
                                checked = true;
                            }
                            _ => {
                                return Err(Diagnostic {
                                    name: "type.field_array_move".into(),
                                    title: format!(
                                        "`{name}` cannot move into array field `{field}`"
                                    ),
                                    span: value.span,
                                    label: "needs an owned array of the same element type".into(),
                                    notes: vec![],
                                });
                            }
                        },
                        ExprKind::AllocArray { .. } => {}
                        _ => {
                            return Err(Diagnostic {
                                name: "type.field_array_move".into(),
                                title: format!("array field `{field}` needs an owned array"),
                                span: value.span,
                                label: "assign a fresh `alloc_array` or move an owned local".into(),
                                notes: vec![],
                            });
                        }
                    }
                }
                if !checked {
                    check_expr(ctx, value, Some(fty))?;
                }
                // A field is a sink like any other: it takes the value, so
                // the source place dies. And a field outlives the exposure
                // body, so it is a place a brand may not reach.
                let dest = Place {
                    root: "self".to_string(),
                    fields: vec![field.clone()],
                };
                reject_overwrite_of_obligation(ctx, &dest, *field_span)?;
                let carries = transfer(ctx, value, Some(("be stored in a field", *field_span)))?;
                // The field owns a value again even if it had been moved
                // out earlier: `resource R old = self.f; self.f = new;` is
                // how a member replaces authority rather than losing it.
                ctx.moved.retain(|m| !dest.contains(m));
                // A field keeps its declared obligation and picks up one
                // that travelled into it; storing a token in a field is
                // not a way to lose its marker.
                let marked = marked_field(ctx.marked_fields, field);
                if let Some(v) = ctx.vars.get_mut(&format!("self.{field}")) {
                    v.obligation = marked || carries;
                }
                if ctx.in_init {
                    ctx.vars
                        .get_mut(&format!("self.{field}"))
                        .unwrap()
                        .initialized = true;
                }
            }
            Stmt::FieldStore {
                field,
                field_span,
                index,
                value,
            } => {
                let fty = ctx.self_field_ty(field, *field_span, true)?;
                let Ty::Array(elem, _) = fty else {
                    return Err(Diagnostic {
                        name: "type.not_an_array".into(),
                        title: format!("field `{field}` is not an array"),
                        span: *field_span,
                        label: format!("this has type `{}`", fty.name()),
                        notes: vec![],
                    });
                };
                ctx.require_field_init(field, *field_span)?;
                check_expr(ctx, index, Some(Ty::Int(IntTy::U64)))?;
                check_expr(ctx, value, Some(Ty::Int(elem)))?;
            }
            Stmt::Store {
                array,
                array_span,
                index,
                value,
            } => {
                let (elem, mutability, arr_mutable) = match ctx.vars.get(array.as_str()) {
                    Some(VarInfo {
                        ty: Ty::Array(t, m),
                        mutable,
                        ..
                    }) => (*t, *m, *mutable),
                    Some(v) => {
                        return Err(Diagnostic {
                            name: "type.not_an_array".into(),
                            title: format!("`{array}` is not an array"),
                            span: *array_span,
                            label: format!("this has type `{}`", v.ty.name()),
                            notes: vec![],
                        });
                    }
                    None => {
                        return Err(Diagnostic {
                            name: "type.unknown_variable".into(),
                            title: format!("unknown variable `{array}`"),
                            span: *array_span,
                            label: "not declared".into(),
                            notes: vec![],
                        });
                    }
                };
                if mutability == Mutability::Owned && !arr_mutable {
                    return Err(Diagnostic {
                        name: "mut.store_immutable".into(),
                        title: format!("store into immutable local `{array}`"),
                        span: *array_span,
                        label: "declare it `mut` to allow element stores".into(),
                        notes: vec![],
                    });
                }
                if mutability == Mutability::Shared {
                    return Err(Diagnostic {
                        name: "type.store_shared".into(),
                        title: format!("cannot store through shared borrow `&[{}]`", elem.name()),
                        span: *array_span,
                        label: format!("`{array}` must be `&mut [{}]` to be written", elem.name()),
                        notes: vec![],
                    });
                }
                // Writing is a use: an owned array moved into a field is
                // gone, and a store through the old name would reach the
                // field's storage while the logic believes the two are
                // separate values.
                let place = Place::local(array);
                if ctx.is_moved(&place) {
                    return Err(moved_out(ctx, &place, *array_span, "store"));
                }
                check_expr(ctx, index, Some(Ty::Int(IntTy::U64)))?;
                check_expr(ctx, value, Some(Ty::Int(elem)))?;
            }
        }
    }
    Ok(returned)
}

fn stmt_span(stmt: &Stmt) -> Span {
    match stmt {
        Stmt::Unsafe { kw_span, .. }
        | Stmt::StaticAlloc { kw_span, .. }
        | Stmt::SystemAlloc { kw_span, .. }
        | Stmt::SystemDealloc { kw_span, .. }
        | Stmt::Expose { kw_span, .. } => *kw_span,
        Stmt::Decl { name_span, .. } => *name_span,
        Stmt::Assert(c) => c.line_span,
        Stmt::Assign { name_span, .. } => *name_span,
        Stmt::If { cond, .. } => cond.span,
        Stmt::While { kw_span, .. } => *kw_span,
        Stmt::Return { span, .. } => *span,
        Stmt::Store { array_span, .. } => *array_span,
        Stmt::ExprStmt(e) => e.span,
        Stmt::VarDecl { name_span, .. } => *name_span,
        Stmt::FieldAssign { field_span, .. } => *field_span,
        Stmt::FieldStore { field_span, .. } => *field_span,
    }
}

/// Resource kind named by an operation argument before contextual checking.
/// Owned resource names otherwise deliberately reject context-free use, so
/// overloaded sealed/raw operations need this narrow peek first.
fn resource_arg_kind(ctx: &Ctx, e: &Expr) -> Option<ResKind> {
    let ty = match &e.kind {
        ExprKind::Var(name) => ctx.vars.get(name.as_str()).map(|v| v.ty),
        ExprKind::SelfField { field } => ctx
            .vars
            .get(format!("self.{field}").as_str())
            .map(|v| v.ty),
        ExprKind::Borrow { array, field, .. } => {
            let key = field
                .as_ref()
                .map_or_else(|| array.clone(), |f| format!("{array}.{f}"));
            ctx.vars.get(key.as_str()).map(|v| v.ty)
        }
        _ => e.ty,
    }?;
    match ty {
        Ty::Res(kind) | Ty::ResRef(kind, _) => Some(kind),
        _ => None,
    }
}

fn check_expr(ctx: &mut Ctx, e: &mut Expr, expected: Option<Ty>) -> CResult<Ty> {
    let ty = infer_expr(ctx, e, expected)?;
    if let Some(exp) = expected {
        if ty != exp {
            return Err(Diagnostic {
                name: "type.mismatch".into(),
                title: format!(
                    "type mismatch: expected `{}`, found `{}`",
                    exp.name(),
                    ty.name()
                ),
                span: e.span,
                label: format!("this has type `{}`", ty.name()),
                notes: vec![(
                    "note".into(),
                    "Sable has no implicit conversions; `widen<T>(e)` widens explicitly".into(),
                )],
            });
        }
    }
    Ok(ty)
}

fn infer_expr(ctx: &mut Ctx, e: &mut Expr, expected: Option<Ty>) -> CResult<Ty> {
    let span = e.span;
    let ty = match &mut e.kind {
        ExprKind::IntLit(n) => {
            let t = match expected {
                Some(Ty::Int(t)) => t,
                Some(other) => {
                    return Err(Diagnostic {
                        name: "type.mismatch".into(),
                        title: format!("expected `{}`, found an integer literal", other.name()),
                        span,
                        label: "integer literal".into(),
                        notes: vec![],
                    });
                }
                None => {
                    return Err(Diagnostic {
                        name: "type.ambiguous_literal".into(),
                        title: format!("cannot infer the type of literal `{n}`"),
                        span,
                        label: "no type context".into(),
                        notes: vec![(
                            "note".into(),
                            "give the literal context, e.g. bind it to a typed variable".into(),
                        )],
                    });
                }
            };
            if !matches!(t, IntTy::TParam(_)) && (*n < t.min() || *n > t.max()) {
                return Err(Diagnostic {
                    name: "type.literal_out_of_range".into(),
                    title: format!("literal `{n}` does not fit in `{}`", t.name()),
                    span,
                    label: format!("`{}` holds {}..={}", t.name(), t.min(), t.max()),
                    notes: vec![],
                });
            }
            Ty::Int(t)
        }
        ExprKind::BoolLit(_) => Ty::Bool,
        ExprKind::Var(name) => match ctx.vars.get(name.as_str()) {
            Some(v) => {
                if ctx.is_moved(&Place::local(name)) {
                    return Err(moved_out(ctx, &Place::local(name), span, "read"));
                }
                if let Ty::Res(got) = v.ty {
                    // Resources are affine: a bare name is a move, and
                    // there is nowhere else a resource-typed expression
                    // may appear (ADR 0024).
                    if let Some(Ty::Res(want)) = expected {
                        if want != got {
                            return Err(Diagnostic {
                                name: "type.mismatch".into(),
                                title: format!(
                                    "expected `resource {}`, found `resource {}`",
                                    want.name(),
                                    got.name()
                                ),
                                span,
                                label: "different resource type".into(),
                                notes: vec![],
                            });
                        }
                        return Ok(v.ty);
                    }
                    return Err(Diagnostic {
                        name: "resource.not_a_value".into(),
                        title: format!("resource `{name}` used as a value"),
                        span,
                        label: "a resource may only be moved, borrowed, or returned".into(),
                        notes: vec![(
                            "note".into(),
                            "a resource is authority, not data; what the proof language \
                             reads is its view, written `s.len` in a clause"
                                .into(),
                        )],
                    });
                }
                if let Ty::Class(got) = v.ty {
                    // Class values move: out through `return`, into a
                    // by-value parameter, or into another local
                    // (ADR 0010/0020).
                    if let Some(Ty::Class(want)) = expected {
                        if want != got {
                            return Err(Diagnostic {
                                name: "type.mismatch".into(),
                                title: format!(
                                    "expected `{}`, found `{}`",
                                    ctx.class_metas[want].name, ctx.class_metas[got].name
                                ),
                                span,
                                label: "different class".into(),
                                notes: vec![],
                            });
                        }
                        return Ok(v.ty);
                    }
                    return Err(Diagnostic {
                        name: "type.class_value".into(),
                        title: format!("class value `{name}` used as a value"),
                        span,
                        label: "class values cannot be copied or moved yet \
                                (returning a local is the exception — ADR 0010)"
                            .into(),
                        notes: vec![],
                    });
                }
                if matches!(v.ty, Ty::Array(..)) {
                    return Err(Diagnostic {
                        name: "type.array_value".into(),
                        title: format!("array `{name}` used as a value"),
                        span,
                        label: "arrays support only `a[i]` and `a.len` here".into(),
                        notes: vec![],
                    });
                }
                if !v.initialized {
                    return Err(Diagnostic {
                        name: "type.uninitialized".into(),
                        title: format!("`{name}` may be read before initialization"),
                        span,
                        label: "not initialized on every path to this point".into(),
                        notes: vec![(
                            "note".into(),
                            "there is no default zero (design §2.3); initialize on all paths \
                             (a loop body may run zero times)"
                                .into(),
                        )],
                    });
                }
                v.ty
            }
            None => {
                return Err(Diagnostic {
                    name: "type.unknown_variable".into(),
                    title: format!("unknown variable `{name}`"),
                    span,
                    label: "not declared".into(),
                    notes: vec![],
                });
            }
        },
        ExprKind::Index {
            array,
            array_span,
            index,
        } => {
            let elem = array_elem_ty(ctx, array, *array_span)?;
            check_expr(ctx, index, Some(Ty::Int(IntTy::U64)))?;
            Ty::Int(elem)
        }
        ExprKind::Len { array } => {
            // `a.len` on a class receiver is the FIELD named `len`
            // (ADR 0010) — rewrite and re-check.
            if matches!(
                ctx.vars.get(array.as_str()).map(|v| v.ty),
                Some(Ty::Class(_)) | Some(Ty::ClassRef(..))
            ) {
                let obj = array.clone();
                e.kind = ExprKind::ClassField {
                    obj,
                    obj_span: span,
                    field: "len".to_string(),
                };
                return check_expr(ctx, e, expected);
            }
            array_elem_ty(ctx, array, span)?;
            Ty::Int(IntTy::U64)
        }
        ExprKind::Widen { target, arg } => {
            let src = match check_expr(ctx, arg, None) {
                Ok(Ty::Int(t)) => t,
                Ok(other) => {
                    return Err(Diagnostic {
                        name: "type.mismatch".into(),
                        title: format!("`widen` applied to `{}`", other.name()),
                        span,
                        label: "expected an integer".into(),
                        notes: vec![],
                    });
                }
                Err(d) => {
                    // Literals need context; widening a literal is pointless
                    // but legal — retry with the target type.
                    if d.name == "type.ambiguous_literal" {
                        check_expr(ctx, arg, Some(Ty::Int(*target)))?;
                        *target
                    } else {
                        return Err(d);
                    }
                }
            };
            if matches!(src, IntTy::TParam(_)) || matches!(target, IntTy::TParam(_)) {
                return Err(Diagnostic {
                    name: "concepts.template_conv".into(),
                    title: "`widen`/`narrow` on a type parameter".into(),
                    span,
                    label: "conversions involving type parameters are not yet \
                            supported in templates (ADR 0009)"
                        .into(),
                    notes: vec![],
                });
            }
            if src.min() < target.min() || src.max() > target.max() {
                return Err(Diagnostic {
                    name: "type.narrowing_widen".into(),
                    title: format!(
                        "`widen<{}>` from `{}` is not value-preserving",
                        target.name(),
                        src.name()
                    ),
                    span,
                    label: format!(
                        "the range of `{}` is not contained in `{}`",
                        src.name(),
                        target.name()
                    ),
                    notes: vec![(
                        "note".into(),
                        "use `narrow<T>(e)` — any-to-any conversion under a range VC".into(),
                    )],
                });
            }
            Ty::Int(*target)
        }
        ExprKind::Narrow { target, arg } => {
            // Any integer type to any integer type; the range fact is a
            // proof obligation (`narrow.range`), not a typing rule.
            match check_expr(ctx, arg, None) {
                Ok(Ty::Int(_)) => {}
                Ok(other) => {
                    return Err(Diagnostic {
                        name: "type.mismatch".into(),
                        title: format!("`narrow` applied to `{}`", other.name()),
                        span,
                        label: "expected an integer".into(),
                        notes: vec![],
                    });
                }
                Err(d) => {
                    if d.name == "type.ambiguous_literal" {
                        check_expr(ctx, arg, Some(Ty::Int(*target)))?;
                    } else {
                        return Err(d);
                    }
                }
            }
            Ty::Int(*target)
        }
        ExprKind::IsSome { operand } => {
            match check_expr(ctx, operand, None)? {
                Ty::Option(_) => {}
                other => {
                    return Err(Diagnostic {
                        name: "type.mismatch".into(),
                        title: format!("`.is_some` on `{}`", other.name()),
                        span,
                        label: "expected an `option<T>` value".into(),
                        notes: vec![],
                    });
                }
            }
            Ty::Bool
        }
        ExprKind::OptValue { operand } => match check_expr(ctx, operand, None)? {
            Ty::Option(it) => Ty::Int(it),
            other => {
                return Err(Diagnostic {
                    name: "type.mismatch".into(),
                    title: format!("`.value` on `{}`", other.name()),
                    span,
                    label: "expected an `option<T>` value".into(),
                    notes: vec![],
                });
            }
        },
        ExprKind::ClassField {
            obj,
            obj_span,
            field,
        } => {
            let ci = class_of(ctx, obj, *obj_span)?;
            let meta = &ctx.class_metas[ci];
            let Some((_, fty)) = meta.fields.iter().find(|(n, _)| n == field) else {
                return Err(Diagnostic {
                    name: "type.unknown_field".into(),
                    title: format!("`{}` has no field `{field}`", meta.name),
                    span,
                    label: "unknown field".into(),
                    notes: vec![],
                });
            };
            match fty {
                Ty::Int(it) => Ty::Int(*it),
                Ty::Array(..) => {
                    return Err(Diagnostic {
                        name: "type.array_field_value".into(),
                        title: format!("array field `{field}` used as a value"),
                        span,
                        label: format!("use `{obj}.{field}[i]` or `{obj}.{field}.len`"),
                        notes: vec![],
                    });
                }
                other => {
                    return Err(Diagnostic {
                        name: "type.mismatch".into(),
                        title: format!("field `{field}` has type `{}`", other.name()),
                        span,
                        label: "unsupported field read".into(),
                        notes: vec![],
                    });
                }
            }
        }
        ExprKind::ClassFieldLen { obj, field } => {
            let ci = class_of(ctx, obj, span)?;
            let meta = &ctx.class_metas[ci];
            match meta.fields.iter().find(|(n, _)| n == field) {
                Some((_, Ty::Array(..))) => Ty::Int(IntTy::U64),
                _ => {
                    return Err(Diagnostic {
                        name: "type.mismatch".into(),
                        title: format!("`.len` needs an array field; `{field}` is not one"),
                        span,
                        label: "not an array field".into(),
                        notes: vec![],
                    });
                }
            }
        }
        ExprKind::ClassFieldIndex {
            obj,
            obj_span,
            field,
            index,
        } => {
            let ci = class_of(ctx, obj, *obj_span)?;
            let meta = &ctx.class_metas[ci];
            let elem = match meta.fields.iter().find(|(n, _)| n == field) {
                Some((_, Ty::Array(el, _))) => *el,
                _ => {
                    return Err(Diagnostic {
                        name: "type.mismatch".into(),
                        title: format!("`{field}` is not an array field"),
                        span,
                        label: "not indexable".into(),
                        notes: vec![],
                    });
                }
            };
            check_expr(ctx, index, Some(Ty::Int(IntTy::U64)))?;
            Ty::Int(elem)
        }
        ExprKind::TraitCall {
            param,
            param_span,
            method,
            args,
        } => {
            let Some((tname, pidx)) = ctx.tbounds.get(param.as_str()).cloned() else {
                return Err(Diagnostic {
                    name: "concepts.unbound_trait_call".into(),
                    title: format!("`{param}` has no trait bound"),
                    span: *param_span,
                    label: "trait calls go through a bounded type parameter".into(),
                    notes: vec![],
                });
            };
            let tr = ctx
                .traits
                .iter()
                .find(|t| t.name == tname)
                .expect("mono validated the bound");
            let Some(m) = tr.methods.iter().find(|mm| mm.name == *method) else {
                return Err(Diagnostic {
                    name: "concepts.no_trait_method".into(),
                    title: format!("`{tname}` has no method `{method}`"),
                    span: *param_span,
                    label: "not a method of the bounding trait".into(),
                    notes: vec![],
                });
            };
            // In the trait, `Self` is TParam(0); in this template, the
            // bounded parameter is TParam(pidx).
            let remap = |t: Ty| -> Ty {
                match t {
                    Ty::Int(IntTy::TParam(0)) => Ty::Int(IntTy::TParam(pidx)),
                    other => other,
                }
            };
            if args.len() != m.params.len() {
                return Err(Diagnostic {
                    name: "type.arity".into(),
                    title: format!(
                        "`{param}::{method}` takes {} argument(s), {} given",
                        m.params.len(),
                        args.len()
                    ),
                    span: *param_span,
                    label: "wrong number of arguments".into(),
                    notes: vec![],
                });
            }
            let want: Vec<Ty> = m.params.iter().map(|p| remap(p.ty)).collect();
            for (a, w) in args.iter_mut().zip(&want) {
                check_expr(ctx, a, Some(*w))?;
            }
            remap(m.ret)
        }
        ExprKind::RawOp { op, op_span, args } => {
            let op = *op;
            let op_span = *op_span;
            if op.touches_memory() && !ctx.in_unsafe {
                return Err(Diagnostic {
                    name: "raw.outside_unsafe".into(),
                    title: format!("`{}` may only be called inside `unsafe`", op.name()),
                    span: op_span,
                    label: "raw memory access".into(),
                    notes: vec![(
                        "note".into(),
                        "the block is the audit boundary: it marks every place where a \
                         proof, rather than the type system, is what keeps memory safe"
                            .into(),
                    )],
                });
            }
            if args.len() != op.arity() {
                return Err(Diagnostic {
                    name: "type.arity".into(),
                    title: format!(
                        "`{}` takes {} argument(s), {} given",
                        op.name(),
                        op.arity(),
                        args.len()
                    ),
                    span: op_span,
                    label: "wrong number of arguments".into(),
                    notes: vec![],
                });
            }
            let raw = Ty::Raw(IntTy::U8);
            let u8t = Ty::Int(IntTy::U8);
            let u64t = Ty::Int(IntTy::U64);
            let shared = Ty::ResRef(ResKind::RawSpan, Mutability::Shared);
            let unique = Ty::ResRef(ResKind::RawSpan, Mutability::Mut);
            let span = Ty::Res(ResKind::RawSpan);
            let cell = Ty::Res(ResKind::PointsToU64);
            let cell_shared = Ty::ResRef(ResKind::PointsToU64, Mutability::Shared);
            let cell_unique = Ty::ResRef(ResKind::PointsToU64, Mutability::Mut);
            let leased = Ty::Res(ResKind::BlockLease);
            let leased_cell = Ty::Res(ResKind::LeasedPointsToU64);
            let free_block = Ty::Res(ResKind::FreeBlock);
            let free_header = Ty::Res(ResKind::FreeHeader);
            let free_header_shared = Ty::ResRef(ResKind::FreeHeader, Mutability::Shared);
            let free_header_unique = Ty::ResRef(ResKind::FreeHeader, Mutability::Mut);
            let arg_kind = |i: usize| resource_arg_kind(ctx, &args[i]);
            let cell_kind = match op {
                RawOp::IntoCellU64 => arg_kind(1),
                RawOp::FromCellU64 => arg_kind(1),
                RawOp::CellInitU64 => arg_kind(2),
                RawOp::CellReadU64 | RawOp::CellTakeU64 | RawOp::CellDropU64 => arg_kind(1),
                _ => None,
            };
            let leased_role = matches!(
                cell_kind,
                Some(ResKind::BlockLease | ResKind::LeasedPointsToU64)
            );
            let leased_cell_shared =
                Ty::ResRef(ResKind::LeasedPointsToU64, Mutability::Shared);
            let leased_cell_unique =
                Ty::ResRef(ResKind::LeasedPointsToU64, Mutability::Mut);
            let want: Vec<Ty> = match op {
                RawOp::Offset => vec![raw, u64t],
                RawOp::Load8 => vec![raw, shared],
                RawOp::Store8 => vec![raw, u8t, unique],
                RawOp::Copy => vec![raw, raw, u64t, shared, unique],
                RawOp::IntoCellU64 => vec![raw, if leased_role { leased } else { span }],
                RawOp::FromCellU64 => vec![raw, if leased_role { leased_cell } else { cell }],
                RawOp::CellInitU64 => vec![
                    raw,
                    u64t,
                    if leased_role { leased_cell_unique } else { cell_unique },
                ],
                RawOp::CellReadU64 => vec![
                    raw,
                    if leased_role { leased_cell_shared } else { cell_shared },
                ],
                RawOp::CellTakeU64 | RawOp::CellDropU64 => vec![
                    raw,
                    if leased_role { leased_cell_unique } else { cell_unique },
                ],
                RawOp::IntoFreeHeader => vec![raw, free_block],
                RawOp::FromFreeHeader => vec![raw, free_header],
                RawOp::HeaderInit => vec![raw, u64t, u64t, free_header_unique],
                RawOp::HeaderSize | RawOp::HeaderNext => vec![raw, free_header_shared],
                RawOp::HeaderClear => vec![raw, free_header_unique],
            };
            for (arg, w) in args.iter_mut().zip(&want) {
                require_explicit_borrow(ctx, arg, *w)?;
                check_expr(ctx, arg, Some(*w))?;
                if matches!(w, Ty::Res(_)) {
                    transfer(ctx, arg, None)?;
                }
            }
            check_borrow_conflicts(ctx, args, None)?;
            match op {
                // A pointer derived from a branded one is branded too:
                // provenance is what the brand tracks, and arithmetic
                // preserves it.
                RawOp::Offset => raw,
                RawOp::Load8 => u8t,
                RawOp::Store8 | RawOp::Copy => Ty::Unit,
                RawOp::IntoCellU64 => if leased_role { leased_cell } else { cell },
                RawOp::FromCellU64 => if leased_role { leased } else { span },
                RawOp::CellInitU64 | RawOp::CellDropU64 => Ty::Unit,
                RawOp::CellReadU64 | RawOp::CellTakeU64 => u64t,
                RawOp::IntoFreeHeader => free_header,
                RawOp::FromFreeHeader => free_block,
                RawOp::HeaderInit | RawOp::HeaderClear => Ty::Unit,
                RawOp::HeaderSize | RawOp::HeaderNext => u64t,
            }
        }
        ExprKind::ResOp { op, op_span, args } => {
            let op = *op;
            let op_span = *op_span;
            let arity = match op {
                ResOp::AllocatorStepHeader => 3,
                ResOp::SplitOff | ResOp::Join | ResOp::OpenFileOf
                | ResOp::AllocatorTake | ResOp::AllocatorPut
                | ResOp::AllocatorTakeFree | ResOp::AllocatorPutFree
                | ResOp::AllocatorTakeHeader | ResOp::AllocatorPutHeader
                | ResOp::FreeBlockSplit | ResOp::FreeBlockJoin => 2,
                ResOp::TestWorld | ResOp::AllocatorCreate | ResOp::AllocatorDestroy
                | ResOp::FreeBlockLease | ResOp::BlockLeaseFree => 1,
            };
            if args.len() != arity {
                return Err(Diagnostic {
                    name: "type.arity".into(),
                    title: format!(
                        "`{}` takes {arity} argument(s), {} given",
                        op.name(),
                        args.len()
                    ),
                    span: op_span,
                    label: "wrong number of arguments".into(),
                    notes: vec![],
                });
            }
            match op {
                // `split_off(&mut whole, n)` — the prefix stays in the
                // borrowed token, the suffix leaves in the returned one.
                // No product type is needed: one side is written back
                // through the borrow (ADR 0024).
                ResOp::SplitOff => {
                    let want = Ty::ResRef(ResKind::RawSpan, Mutability::Mut);
                    require_explicit_borrow(ctx, &args[0], want)?;
                    let got = check_expr(ctx, &mut args[0], Some(want))?;
                    debug_assert_eq!(got, want);
                    check_expr(ctx, &mut args[1], Some(Ty::Int(IntTy::U64)))?;
                    check_borrow_conflicts(ctx, args, None)?;
                    Ty::Res(ResKind::RawSpan)
                }
                // `join(a, b)` — both are consumed; the result owns their
                // concatenation. Adjacency is a precondition, so a
                // nonadjacent join is a failed VC, not a checker error.
                ResOp::Join => {
                    let want = Ty::Res(ResKind::RawSpan);
                    // Each argument moves as it is checked, so
                    // `join(a, a)` is a use-after-move on the second
                    // occurrence. Deferring the moves to a second pass
                    // would accept it — and an empty span *is* adjacent
                    // to itself, so the adjacency VC would not catch it
                    // either: the token would be duplicated out of
                    // nothing.
                    for arg in args.iter_mut() {
                        check_expr(ctx, arg, Some(want))?;
                        mark_moved(ctx, arg)?;
                    }
                    want
                }
                // `open_file(&mut w, fd)` — the authority to use a
                // descriptor, carved out of the world that handed it out.
                // Whether the descriptor is really open is a *precondition*,
                // not a checker rule: the checker tracks tokens, not the
                // state of the outside world (ADR 0028).
                ResOp::OpenFileOf => {
                    let want = Ty::ResRef(ResKind::PosixWorld, Mutability::Mut);
                    require_explicit_borrow(ctx, &args[0], want)?;
                    check_expr(ctx, &mut args[0], Some(want))?;
                    check_expr(ctx, &mut args[1], Some(Ty::Int(IntTy::I32)))?;
                    check_borrow_conflicts(ctx, args, None)?;
                    Ty::Res(ResKind::OpenFile)
                }
                // `posix_world(script)` — the one place authority appears
                // from nothing, so it is confined to tests. A program that
                // could conjure a world could conjure any authority the
                // world hands out.
                ResOp::TestWorld => {
                    if !ctx.in_test {
                        return Err(Diagnostic {
                            name: "posix.world_outside_test".into(),
                            title: "`posix_world` exists only in tests".into(),
                            span: op_span,
                            label: "a program cannot conjure the outside world".into(),
                            notes: vec![(
                                "note".into(),
                                "outside a test the world arrives as a parameter, from \
                                 whoever is entitled to it; a program that could make \
                                 one could make any authority the world hands out"
                                    .into(),
                            )],
                        });
                    }
                    check_expr(ctx, &mut args[0], Some(Ty::Int(IntTy::U64)))?;
                    Ty::Res(ResKind::PosixWorld)
                }
                // Fold a complete raw extent into a fresh affine aggregate.
                ResOp::AllocatorCreate => {
                    let want = Ty::Res(ResKind::RawSpan);
                    check_expr(ctx, &mut args[0], Some(want))?;
                    mark_moved(ctx, &args[0])?;
                    Ty::Res(ResKind::AllocatorState)
                }
                // The aggregate may unfold only when its free map once
                // again contains the complete root; that condition is a VC.
                ResOp::AllocatorDestroy => {
                    let want = Ty::Res(ResKind::AllocatorState);
                    check_expr(ctx, &mut args[0], Some(want))?;
                    transfer(ctx, &args[0], None)?;
                    Ty::Res(ResKind::RawSpan)
                }
                ResOp::AllocatorTake => {
                    let want = Ty::ResRef(ResKind::AllocatorState, Mutability::Mut);
                    require_explicit_borrow(ctx, &args[0], want)?;
                    check_expr(ctx, &mut args[0], Some(want))?;
                    check_expr(ctx, &mut args[1], Some(Ty::Int(IntTy::U64)))?;
                    check_borrow_conflicts(ctx, args, None)?;
                    Ty::Res(ResKind::BlockLease)
                }
                ResOp::AllocatorPut => {
                    let state = Ty::ResRef(ResKind::AllocatorState, Mutability::Mut);
                    require_explicit_borrow(ctx, &args[0], state)?;
                    check_expr(ctx, &mut args[0], Some(state))?;
                    let lease = Ty::Res(ResKind::BlockLease);
                    check_expr(ctx, &mut args[1], Some(lease))?;
                    transfer(ctx, &args[1], None)?;
                    check_borrow_conflicts(ctx, args, None)?;
                    Ty::Unit
                }
                ResOp::AllocatorTakeFree => {
                    let want = Ty::ResRef(ResKind::AllocatorState, Mutability::Mut);
                    require_explicit_borrow(ctx, &args[0], want)?;
                    check_expr(ctx, &mut args[0], Some(want))?;
                    check_expr(ctx, &mut args[1], Some(Ty::Int(IntTy::U64)))?;
                    check_borrow_conflicts(ctx, args, None)?;
                    Ty::Res(ResKind::FreeBlock)
                }
                ResOp::AllocatorPutFree => {
                    let state = Ty::ResRef(ResKind::AllocatorState, Mutability::Mut);
                    require_explicit_borrow(ctx, &args[0], state)?;
                    check_expr(ctx, &mut args[0], Some(state))?;
                    let block = Ty::Res(ResKind::FreeBlock);
                    check_expr(ctx, &mut args[1], Some(block))?;
                    transfer(ctx, &args[1], None)?;
                    check_borrow_conflicts(ctx, args, None)?;
                    Ty::Unit
                }
                ResOp::AllocatorTakeHeader => {
                    let want = Ty::ResRef(ResKind::AllocatorState, Mutability::Mut);
                    require_explicit_borrow(ctx, &args[0], want)?;
                    check_expr(ctx, &mut args[0], Some(want))?;
                    check_expr(ctx, &mut args[1], Some(Ty::Int(IntTy::U64)))?;
                    check_borrow_conflicts(ctx, args, None)?;
                    Ty::Res(ResKind::FreeHeader)
                }
                ResOp::AllocatorPutHeader => {
                    let state = Ty::ResRef(ResKind::AllocatorState, Mutability::Mut);
                    require_explicit_borrow(ctx, &args[0], state)?;
                    check_expr(ctx, &mut args[0], Some(state))?;
                    let header = Ty::Res(ResKind::FreeHeader);
                    check_expr(ctx, &mut args[1], Some(header))?;
                    transfer(ctx, &args[1], None)?;
                    check_borrow_conflicts(ctx, args, None)?;
                    Ty::Unit
                }
                ResOp::AllocatorStepHeader => {
                    let want = Ty::ResRef(ResKind::AllocatorState, Mutability::Mut);
                    require_explicit_borrow(ctx, &args[0], want)?;
                    check_expr(ctx, &mut args[0], Some(want))?;
                    check_expr(ctx, &mut args[1], Some(Ty::Int(IntTy::U64)))?;
                    check_expr(ctx, &mut args[2], Some(Ty::Int(IntTy::U64)))?;
                    check_borrow_conflicts(ctx, args, None)?;
                    Ty::Res(ResKind::FreeHeader)
                }
                ResOp::FreeBlockSplit => {
                    let block = Ty::ResRef(ResKind::FreeBlock, Mutability::Mut);
                    require_explicit_borrow(ctx, &args[0], block)?;
                    check_expr(ctx, &mut args[0], Some(block))?;
                    check_expr(ctx, &mut args[1], Some(Ty::Int(IntTy::U64)))?;
                    check_borrow_conflicts(ctx, args, None)?;
                    Ty::Res(ResKind::FreeBlock)
                }
                ResOp::FreeBlockJoin => {
                    let block = Ty::Res(ResKind::FreeBlock);
                    for arg in args.iter_mut() {
                        check_expr(ctx, arg, Some(block))?;
                        transfer(ctx, arg, None)?;
                    }
                    Ty::Res(ResKind::FreeBlock)
                }
                ResOp::FreeBlockLease => {
                    let block = Ty::Res(ResKind::FreeBlock);
                    check_expr(ctx, &mut args[0], Some(block))?;
                    transfer(ctx, &args[0], None)?;
                    Ty::Res(ResKind::BlockLease)
                }
                ResOp::BlockLeaseFree => {
                    let lease = Ty::Res(ResKind::BlockLease);
                    check_expr(ctx, &mut args[0], Some(lease))?;
                    transfer(ctx, &args[0], None)?;
                    Ty::Res(ResKind::FreeBlock)
                }
            }
        }
        ExprKind::AllocArray { elem, len, init } => {
            let elem = *elem;
            check_expr(ctx, len, Some(Ty::Int(IntTy::U64)))?;
            check_expr(ctx, init, Some(Ty::Int(elem)))?;
            Ty::Array(elem, Mutability::Owned)
        }
        ExprKind::SelfField { field } => {
            let fty = ctx.self_field_ty(field, span, false)?;
            if matches!(fty, Ty::Array(..)) {
                return Err(Diagnostic {
                    name: "type.array_field_value".into(),
                    title: format!("array field `{field}` used as a value"),
                    span,
                    label: "use `self.{field}[i]` or `self.{field}.len`".into(),
                    notes: vec![],
                });
            }
            if ctx.in_init {
                ctx.require_field_init(field, span)?;
            }
            fty
        }
        ExprKind::SelfFieldLen { field } => {
            let fty = ctx.self_field_ty(field, span, false)?;
            if !matches!(fty, Ty::Array(..)) {
                return Err(Diagnostic {
                    name: "type.not_an_array".into(),
                    title: format!("field `{field}` is not an array"),
                    span,
                    label: format!("this has type `{}`", fty.name()),
                    notes: vec![],
                });
            }
            if ctx.in_init {
                ctx.require_field_init(field, span)?;
            }
            Ty::Int(IntTy::U64)
        }
        ExprKind::SelfFieldIndex { field, index } => {
            let fty = ctx.self_field_ty(field, span, false)?;
            let Ty::Array(elem, _) = fty else {
                return Err(Diagnostic {
                    name: "type.not_an_array".into(),
                    title: format!("field `{field}` is not an array"),
                    span,
                    label: format!("this has type `{}`", fty.name()),
                    notes: vec![],
                });
            };
            if ctx.in_init {
                ctx.require_field_init(field, span)?;
            }
            check_expr(ctx, index, Some(Ty::Int(IntTy::U64)))?;
            Ty::Int(elem)
        }
        ExprKind::CtorCall {
            class,
            class_span,
            type_args,
            init,
            args,
        } => {
            debug_assert!(
                type_args.is_empty(),
                "type arguments must be consumed by monomorphization"
            );
            let Some(ci) = ctx.class_metas.iter().position(|m| m.name == *class) else {
                return Err(Diagnostic {
                    name: "type.unknown_class".into(),
                    title: format!("unknown class `{class}`"),
                    span: *class_span,
                    label: "not defined in this module".into(),
                    notes: vec![],
                });
            };
            let Some((_, params)) = ctx.class_metas[ci]
                .inits
                .iter()
                .find(|(n, _)| n == init)
                .cloned()
                .map(|(n, p)| (n, p))
            else {
                return Err(Diagnostic {
                    name: "type.unknown_init".into(),
                    title: format!("`{class}` has no init `{init}`"),
                    span,
                    label: "not declared in the class".into(),
                    notes: vec![],
                });
            };
            if args.len() != params.len() {
                return Err(Diagnostic {
                    name: "type.arity".into(),
                    title: format!(
                        "`{class}::{init}` takes {} argument(s), {} given",
                        params.len(),
                        args.len()
                    ),
                    span,
                    label: "wrong number of arguments".into(),
                    notes: vec![],
                });
            }
            let launders = class_holds_storage(ctx.class_metas, ci, 0);
            for (arg, p) in args.iter_mut().zip(&params) {
                // A constructor returns a class, and a class may hold
                // resource fields (ADR 0029) — so it is exactly a container
                // a brand could leave in.
                let escapes = launders.then(|| ("be passed to a constructor", arg.span));
                match p.ty {
                    Ty::Array(elem, m) => {
                        if !matches!(arg.kind, ExprKind::Borrow { .. }) {
                            return Err(Diagnostic {
                                name: "type.array_arg_borrow".into(),
                                title: "array arguments are passed by explicit borrow".into(),
                                span: arg.span,
                                label: format!(
                                    "write `{}name`",
                                    if m == Mutability::Mut { "&mut " } else { "&" }
                                ),
                                notes: vec![],
                            });
                        }
                        let got = check_expr(ctx, arg, None)?;
                        if got != Ty::Array(elem, m) {
                            return Err(Diagnostic {
                                name: "type.mismatch".into(),
                                title: format!(
                                    "expected `{}`, found `{}`",
                                    Ty::Array(elem, m).name(),
                                    got.name()
                                ),
                                span: arg.span,
                                label: "borrow with the required mutability".into(),
                                notes: vec![],
                            });
                        }
                    }
                    Ty::ClassRef(..) | Ty::ResRef(..) => {
                        require_explicit_borrow(ctx, arg, p.ty)?;
                        check_expr(ctx, arg, Some(p.ty))?;
                    }
                    _ => {
                        check_expr(ctx, arg, Some(p.ty))?;
                    }
                }
                transfer(ctx, arg, escapes)?;
            }
            check_borrow_conflicts(ctx, args, None)?;
            ctx.calls.push(format!("{class}::{init}"));
            Ty::Class(ci)
        }
        ExprKind::MethodCall {
            recv,
            recv_span,
            method,
            method_span,
            args,
        } => {
            // The receiver is an owned local or a class borrow; a shared
            // borrow only receives `&self` methods (checked below).
            let (ci, recv_mut, recv_owned) = match ctx.vars.get(recv.as_str()) {
                Some(VarInfo {
                    ty: Ty::Class(ci),
                    mutable,
                    ..
                }) => (*ci, *mutable, true),
                Some(VarInfo {
                    ty: Ty::ClassRef(ci, m),
                    ..
                }) => (*ci, *m == Mutability::Mut, false),
                Some(v) => {
                    return Err(Diagnostic {
                        name: "type.not_a_class".into(),
                        title: format!("`{recv}` is not a class value"),
                        span: *recv_span,
                        label: format!("this has type `{}`", v.ty.name()),
                        notes: vec![],
                    });
                }
                None => {
                    return Err(Diagnostic {
                        name: "type.unknown_variable".into(),
                        title: format!("unknown variable `{recv}`"),
                        span: *recv_span,
                        label: "not declared".into(),
                        notes: vec![],
                    });
                }
            };
            let Some((_, params, ret, self_kind)) = ctx.class_metas[ci]
                .methods
                .iter()
                .find(|(n, _, _, _)| n == method)
                .cloned()
            else {
                return Err(Diagnostic {
                    name: "type.unknown_method".into(),
                    title: format!("`{}` has no method `{method}`", ctx.class_metas[ci].name),
                    span: *method_span,
                    label: "not declared in the class".into(),
                    notes: vec![],
                });
            };
            if args.len() != params.len() {
                return Err(Diagnostic {
                    name: "type.arity".into(),
                    title: format!(
                        "`{method}` takes {} argument(s), {} given",
                        params.len(),
                        args.len()
                    ),
                    span,
                    label: "wrong number of arguments".into(),
                    notes: vec![],
                });
            }
            if self_kind == SelfKind::Mut && !recv_mut {
                return if recv_owned {
                    Err(Diagnostic {
                        name: "mut.method_immutable".into(),
                        title: format!("`&mut` method on immutable local `{recv}`"),
                        span: *recv_span,
                        label: format!("`{method}` mutates its receiver; declare `{recv}` `mut`"),
                        notes: vec![],
                    })
                } else {
                    Err(Diagnostic {
                        name: "mut.method_shared_borrow".into(),
                        title: format!("`&mut` method on the shared borrow `{recv}`"),
                        span: *recv_span,
                        label: format!("`{method}` mutates its receiver"),
                        notes: vec![(
                            "note".into(),
                            format!(
                                "take the parameter as `&mut {}` to mutate through it \
                                 (ADR 0023)",
                                ctx.class_metas[ci].name
                            ),
                        )],
                    })
                };
            }
            // A method is a callee like any other: it can launder a brand
            // only if its signature can give storage back.
            let launders = match ret {
                Ty::Raw(_) | Ty::Res(_) | Ty::ResRef(..) => true,
                Ty::Class(ci) => class_holds_storage(ctx.class_metas, ci, 0),
                _ => false,
            };
            for (arg, p) in args.iter_mut().zip(&params) {
                check_expr(ctx, arg, Some(p.ty))?;
                transfer(ctx, arg, launders.then(|| ("be passed to a method", arg.span)))?;
            }
            check_borrow_conflicts(
                ctx,
                args,
                Some((
                    Place::local(recv),
                    self_kind == SelfKind::Mut,
                    *recv_span,
                )),
            )?;
            ctx.calls
                .push(format!("{}::{method}", ctx.class_metas[ci].name));
            ret
        }
        ExprKind::ArrayLit(elems) => match expected {
            Some(Ty::Array(t, Mutability::Owned)) => {
                for el in elems {
                    check_expr(ctx, el, Some(Ty::Int(t)))?;
                }
                Ty::Array(t, Mutability::Owned)
            }
            _ => {
                return Err(Diagnostic {
                    name: "type.array_literal_position".into(),
                    title: "array literal outside an owned-array declaration".into(),
                    span,
                    label: "write `[i32] a = [ ... ];`".into(),
                    notes: vec![],
                });
            }
        },
        ExprKind::Borrow {
            array,
            field,
            mutable,
        } => {
            // Borrowing is a use, so it needs the place alive: `&o` and
            // `&o.f` are both dead once `o` has moved. Reading a name
            // goes through `ExprKind::Var`; this is the other door.
            {
                let mut p = Place::local(array);
                if let Some(f) = field {
                    p.fields.push(f.clone());
                }
                if ctx.is_moved(&p) {
                    return Err(moved_out(ctx, &p, span, "borrow"));
                }
            }
            // `&x.f` / `&self.f` — borrowing a field as a place
            // (ADR 0020). The base must name a class; the field is
            // either class-typed or array-typed.
            if let Some(fname) = field {
                // A destructor is the one place a mutable field borrow is
                // sound: the invariant holds on entry and is not
                // re-established, so there is nothing for the callee to
                // break (ADR 0029). Everywhere else this stays deferred,
                // and the reason is exactly that invariant.
                if *mutable && !(ctx.in_deinit && array == "self") {
                    return Err(Diagnostic {
                        name: "class.mut_field_borrow".into(),
                        title: format!("cannot mutably borrow the field `{array}.{fname}`"),
                        span,
                        label: "field borrows are shared".into(),
                        notes: vec![(
                            "note".into(),
                            "a callee handed `&mut a.f` could not re-establish the \
                             invariant of `a`, which may constrain `f` alongside its \
                             other fields; mutate through a method of `a` instead \
                             (ADR 0023)"
                                .into(),
                        )],
                    });
                }
                let base = if array == "self" {
                    match ctx.in_class {
                        Some((ci, _)) => Ty::ClassRef(ci, Mutability::Shared),
                        None => {
                            return Err(Diagnostic {
                                name: "type.self_outside_class".into(),
                                title: "`self` outside a class member".into(),
                                span,
                                label: "no receiver here".into(),
                                notes: vec![],
                            });
                        }
                    }
                } else {
                    match ctx.vars.get(array.as_str()).map(|v| v.ty) {
                        Some(t) => t,
                        None => {
                            return Err(Diagnostic {
                                name: "type.unknown_name".into(),
                                title: format!("unknown name `{array}`"),
                                span,
                                label: "not in scope".into(),
                                notes: vec![],
                            });
                        }
                    }
                };
                let (Ty::Class(bci) | Ty::ClassRef(bci, _)) = base else {
                    return Err(Diagnostic {
                        name: "type.not_a_class".into(),
                        title: format!("`{array}` is not a class value"),
                        span,
                        label: "field borrows need a class base".into(),
                        notes: vec![],
                    });
                };
                let fld = ctx.class_metas[bci]
                    .fields
                    .iter()
                    .find(|(n, _)| n == fname)
                    .ok_or_else(|| Diagnostic {
                        name: "type.unknown_field".into(),
                        title: format!("class has no field `{fname}`"),
                        span,
                        label: "unknown field".into(),
                        notes: vec![],
                    })?;
                return match fld.1 {
                    Ty::Class(fci) => Ok(Ty::ClassRef(fci, Mutability::Shared)),
                    // A resource field is a place too. Its mutability is
                    // the borrow's: shared anywhere, and unique only in a
                    // destructor, where the invariant it could break no
                    // longer has to hold (ADR 0029).
                    Ty::Res(k) => Ok(Ty::ResRef(
                        k,
                        if *mutable {
                            Mutability::Mut
                        } else {
                            Mutability::Shared
                        },
                    )),
                    // An owned array field is a place too: `&x.limbs`
                    // borrows the array itself, shared.
                    Ty::Array(elem, _) => Ok(Ty::Array(elem, Mutability::Shared)),
                    _ => Err(Diagnostic {
                        name: "type.not_a_place".into(),
                        title: format!("field `{fname}` is not a borrowable place"),
                        span,
                        label: "only class- and array-valued fields are borrowed this way".into(),
                        notes: vec![],
                    }),
                };
            }
            // `&s` / `&mut s` of a resource local or parameter, or a
            // re-borrow of one passed along to a callee (ADR 0024). The
            // rules are the class rules: unique access is only ever
            // narrowed, and a mutable borrow needs a `mut` local.
            if let Some(v) = ctx.vars.get(array.as_str()) {
                if let Ty::Res(k) | Ty::ResRef(k, _) = v.ty {
                    let (src_mut, is_local) = match v.ty {
                        Ty::ResRef(_, m) => (m, false),
                        _ => (Mutability::Mut, true),
                    };
                    let declared_mut = v.mutable;
                    if *mutable {
                        if src_mut != Mutability::Mut {
                            return Err(Diagnostic {
                                name: "type.mut_borrow_shared".into(),
                                title: format!(
                                    "cannot mutably borrow `{array}` through `resource &{}`",
                                    k.name()
                                ),
                                span,
                                label: "this parameter is a shared borrow".into(),
                                notes: vec![],
                            });
                        }
                        if is_local && !declared_mut {
                            return Err(Diagnostic {
                                name: "mut.borrow_immutable".into(),
                                title: format!("`&mut` borrow of immutable local `{array}`"),
                                span,
                                label: "declare it `mut` to allow mutable borrows".into(),
                                notes: vec![],
                            });
                        }
                    }
                    return Ok(Ty::ResRef(
                        k,
                        if *mutable {
                            Mutability::Mut
                        } else {
                            Mutability::Shared
                        },
                    ));
                }
            }
            // `&c` / `&mut c` of a class local, or a re-borrow of a class
            // parameter passed along to a callee (ADR 0010, ADR 0023).
            // A shared re-borrow of a `&mut C` is fine; the other
            // direction would manufacture unique access out of shared.
            if let Some(v) = ctx.vars.get(array.as_str()) {
                if let Ty::Class(ci) | Ty::ClassRef(ci, _) = v.ty {
                    let (src_mut, is_local) = match v.ty {
                        Ty::ClassRef(_, m) => (m, false),
                        _ => (Mutability::Mut, true),
                    };
                    let declared_mut = v.mutable;
                    if *mutable {
                        if src_mut != Mutability::Mut {
                            return Err(Diagnostic {
                                name: "type.mut_borrow_shared".into(),
                                title: format!("cannot mutably borrow `{array}` through `&{}`",
                                    ctx.class_metas[ci].name),
                                span,
                                label: "this parameter is a shared borrow".into(),
                                notes: vec![],
                            });
                        }
                        if is_local && !declared_mut {
                            return Err(Diagnostic {
                                name: "mut.borrow_immutable".into(),
                                title: format!("`&mut` borrow of immutable local `{array}`"),
                                span,
                                label: "declare it `mut` to allow mutable borrows".into(),
                                notes: vec![],
                            });
                        }
                    }
                    return Ok(Ty::ClassRef(
                        ci,
                        if *mutable {
                            Mutability::Mut
                        } else {
                            Mutability::Shared
                        },
                    ));
                }
            }
            let elem = array_elem_ty(ctx, array, span)?;
            let src_mut = match ctx.vars.get(array.as_str()).map(|v| v.ty) {
                Some(Ty::Array(_, m)) => m,
                _ => unreachable!("array_elem_ty checked"),
            };
            if *mutable
                && src_mut == Mutability::Owned
                && !ctx.vars.get(array.as_str()).is_some_and(|v| v.mutable)
            {
                return Err(Diagnostic {
                    name: "mut.borrow_immutable".into(),
                    title: format!("`&mut` borrow of immutable local `{array}`"),
                    span,
                    label: "declare it `mut` to allow mutable borrows".into(),
                    notes: vec![],
                });
            }
            if *mutable && src_mut == Mutability::Shared {
                return Err(Diagnostic {
                    name: "type.mut_borrow_shared".into(),
                    title: format!("cannot mutably borrow `{array}` through `&[_]`"),
                    span,
                    label: "a shared borrow cannot be reborrowed as `&mut`".into(),
                    notes: vec![],
                });
            }
            Ty::Array(
                elem,
                if *mutable {
                    Mutability::Mut
                } else {
                    Mutability::Shared
                },
            )
        }
        ExprKind::SomeE(inner) => match expected {
            Some(Ty::Option(t)) => {
                check_expr(ctx, inner, Some(Ty::Int(t)))?;
                Ty::Option(t)
            }
            _ => {
                return Err(Diagnostic {
                    name: "type.option_position".into(),
                    title: "`some(...)` outside an option-returning position".into(),
                    span,
                    label: "options are created only where an `option<T>` is expected".into(),
                    notes: vec![],
                });
            }
        },
        ExprKind::NoneE => match expected {
            Some(Ty::Option(t)) => Ty::Option(t),
            _ => {
                return Err(Diagnostic {
                    name: "type.option_position".into(),
                    title: "`none` outside an option-returning position".into(),
                    span,
                    label: "options are created only where an `option<T>` is expected".into(),
                    notes: vec![],
                });
            }
        },
        ExprKind::Unary { op, operand } => match op {
            UnOp::Neg => {
                let t = check_expr(ctx, operand, expected)?;
                match t {
                    Ty::Int(it) if it.signed() => t,
                    Ty::Int(_) => {
                        return Err(Diagnostic {
                            name: "type.neg_unsigned".into(),
                            title: "unary minus on an unsigned value".into(),
                            span,
                            label: "operand is unsigned".into(),
                            notes: vec![(
                                "note".into(),
                                "unsigned negation is modular; use `wrap()` when it lands".into(),
                            )],
                        });
                    }
                    _ => {
                        return Err(Diagnostic {
                            name: "type.mismatch".into(),
                            title: "unary minus on a non-integer".into(),
                            span,
                            label: "expected an integer".into(),
                            notes: vec![],
                        });
                    }
                }
            }
            UnOp::Not => {
                check_expr(ctx, operand, Some(Ty::Bool))?;
                Ty::Bool
            }
        },
        ExprKind::Binary {
            op,
            op_span,
            lhs,
            rhs,
        } => {
            let op = *op;
            let op_span = *op_span;
            // Operator sugar (ADR 0012): both operands are named class
            // values → rewrite to the bound call (comparisons via the
            // cmp binding against 0) and re-infer. Downstream stages
            // only ever see the ordinary call.
            let class_of = |ctx: &Ctx, e: &Expr| match &e.kind {
                ExprKind::Var(n) => match ctx.vars.get(n.as_str()).map(|v| v.ty) {
                    Some(Ty::Class(ci)) | Some(Ty::ClassRef(ci, _)) => Some((n.clone(), ci)),
                    _ => None,
                },
                _ => None,
            };
            let lc = class_of(ctx, lhs);
            let rc = class_of(ctx, rhs);
            if let (Some((ln, lci)), Some((rn, rci))) = (lc, rc) {
                if lci != rci {
                    return Err(Diagnostic {
                        name: "op.operand_mismatch".into(),
                        title: "operator on values of different classes".into(),
                        span: op_span,
                        label: format!(
                            "`{}` vs `{}`",
                            ctx.class_metas[lci].name, ctx.class_metas[rci].name
                        ),
                        notes: vec![],
                    });
                }
                let sym = match op {
                    BinOp::Add => Some(OpSym::Add),
                    BinOp::Sub => Some(OpSym::Sub),
                    BinOp::Mul => Some(OpSym::Mul),
                    BinOp::Div => Some(OpSym::Div),
                    BinOp::Rem => Some(OpSym::Rem),
                    BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq | BinOp::Ne => {
                        Some(OpSym::Cmp)
                    }
                    BinOp::And | BinOp::Or => None,
                };
                let Some(sym) = sym else {
                    return Err(Diagnostic {
                        name: "op.unbound".into(),
                        title: format!("`{}` is not an overloadable operator", op.symbol()),
                        span: op_span,
                        label: "no operator binding applies".into(),
                        notes: vec![],
                    });
                };
                let Some(callee) = ctx.operators.get(&(sym, lci)).cloned() else {
                    return Err(Diagnostic {
                        name: "op.unbound".into(),
                        title: format!(
                            "no `operator {}` bound for class `{}`",
                            sym.symbol(),
                            ctx.class_metas[lci].name
                        ),
                        span: op_span,
                        label: "declare one at module level".into(),
                        notes: vec![(
                            "note".into(),
                            format!(
                                "`operator {} = <fn>;` binds it to a `fn (&{c}, &{c})` function",
                                sym.symbol(),
                                c = ctx.class_metas[lci].name
                            ),
                        )],
                    });
                };
                let borrow = |name: String, span: Span| Expr {
                    kind: ExprKind::Borrow {
                        array: name,
                        field: None,
                        mutable: false,
                    },
                    span,
                    ty: None,
                };
                let call = ExprKind::Call {
                    callee,
                    callee_span: op_span,
                    type_args: Vec::new(),
                    args: vec![borrow(ln, lhs.span), borrow(rn, rhs.span)],
                };
                if sym == OpSym::Cmp {
                    e.kind = ExprKind::Binary {
                        op,
                        op_span,
                        lhs: Box::new(Expr {
                            kind: call,
                            span: e.span,
                            ty: None,
                        }),
                        rhs: Box::new(Expr {
                            kind: ExprKind::IntLit(0),
                            span: op_span,
                            ty: None,
                        }),
                    };
                } else {
                    e.kind = call;
                }
                return infer_expr(ctx, e, expected);
            }
            if op.is_arith() {
                let expected_int = match expected {
                    Some(Ty::Int(_)) => expected,
                    _ => None,
                };
                let t = infer_int_pair(ctx, lhs, rhs, expected_int, op_span)?;
                if matches!(op, BinOp::Div | BinOp::Rem) && matches!(t, IntTy::TParam(_)) {
                    return Err(Diagnostic {
                        name: "concepts.template_div".into(),
                        title: "division on a type parameter".into(),
                        span: op_span,
                        label: "`/`/`%` on `T`-typed values needs signedness \
                                knowledge; not yet supported in templates \
                                (ADR 0009)"
                            .into(),
                        notes: vec![],
                    });
                }
                Ty::Int(t)
            } else if op.is_comparison() {
                let _t = infer_int_pair(ctx, lhs, rhs, None, op_span)?;
                Ty::Bool
            } else {
                check_expr(ctx, lhs, Some(Ty::Bool))?;
                check_expr(ctx, rhs, Some(Ty::Bool))?;
                Ty::Bool
            }
        }
        ExprKind::Call {
            callee,
            callee_span,
            type_args,
            args,
        } => {
            debug_assert!(
                type_args.is_empty(),
                "type arguments must be consumed by monomorphization"
            );
            let sig = match ctx.sigs.get(callee.as_str()) {
                Some(s) => s,
                None => {
                    return Err(Diagnostic {
                        name: "type.unknown_function".into(),
                        title: format!("call to unknown function `{callee}`"),
                        span: *callee_span,
                        label: "not defined in this module".into(),
                        notes: vec![],
                    });
                }
            };
            if args.len() != sig.params.len() {
                return Err(Diagnostic {
                    name: "type.arity".into(),
                    title: format!(
                        "`{callee}` takes {} argument(s), {} given",
                        sig.params.len(),
                        args.len()
                    ),
                    span,
                    label: "wrong number of arguments".into(),
                    notes: vec![],
                });
            }
            if callee.starts_with("test_") {
                return Err(Diagnostic {
                    name: "type.call_test".into(),
                    title: format!("`{callee}` is a test and cannot be called"),
                    span: *callee_span,
                    label: "tests are entry points for `sable test` only".into(),
                    notes: vec![],
                });
            }
            if *callee == ctx.current_fn && !ctx.current_has_variant {
                return Err(Diagnostic {
                    name: "type.recursion_needs_variant".into(),
                    title: format!("`{callee}` calls itself without a `variant`",),
                    span: *callee_span,
                    label: "recursion requires a decreasing measure (design §8)".into(),
                    notes: vec![(
                        "note".into(),
                        "add `/// variant <ghost nat expression>` to the function's contract \
                         block or between the signature and `{`"
                            .into(),
                    )],
                });
            }
            let param_tys: Vec<Ty> = sig.params.iter().map(|p| p.ty).collect();
            let ret = sig.ret;
            // Only a signature that *returns* storage can launder a brand
            // out — and since ADR 0029 a class counts, because it may have
            // resource fields.
            //
            // Why a returnless signature is enough differs by callee, and
            // the difference is the audited boundary (ADR 0027/0030). For a
            // *verified* callee the argument is compiler-checked: Sable has
            // no globals, so a pointer it cannot give back dies with its
            // frame. For an `extern` it is an audited promise — nothing
            // stops C stashing the pointer in a foreign global — and it is
            // part of what the contract's audit id covers.
            let launders = match ret {
                Ty::Raw(_) | Ty::Res(_) | Ty::ResRef(..) => true,
                Ty::Class(ci) => class_holds_storage(ctx.class_metas, ci, 0),
                _ => false,
            };
            for (arg, pty) in args.iter_mut().zip(param_tys) {
                let escapes = launders.then(|| ("be passed to a function", arg.span));
                match pty {
                    Ty::Bool => {
                        return Err(Diagnostic {
                            name: "type.bool_arg".into(),
                            title: "bool-typed call arguments are not supported yet".into(),
                            span: arg.span,
                            label: "bool argument".into(),
                            notes: vec![],
                        });
                    }
                    Ty::Array(elem, m) => {
                        if !matches!(arg.kind, ExprKind::Borrow { .. }) {
                            return Err(Diagnostic {
                                name: "type.array_arg_borrow".into(),
                                title: "array arguments are passed by explicit borrow".into(),
                                span: arg.span,
                                label: format!(
                                    "write `{}name`",
                                    if m == Mutability::Mut { "&mut " } else { "&" }
                                ),
                                notes: vec![],
                            });
                        }
                        let got = check_expr(ctx, arg, None)?;
                        if got != Ty::Array(elem, m) {
                            return Err(Diagnostic {
                                name: "type.mismatch".into(),
                                title: format!(
                                    "expected `{}`, found `{}`",
                                    Ty::Array(elem, m).name(),
                                    got.name()
                                ),
                                span: arg.span,
                                label: "borrow with the required mutability".into(),
                                notes: vec![],
                            });
                        }
                    }
                    Ty::ClassRef(..) | Ty::ResRef(..) => {
                        require_explicit_borrow(ctx, arg, pty)?;
                        check_expr(ctx, arg, Some(pty))?;
                    }
                    _ => {
                        check_expr(ctx, arg, Some(pty))?;
                    }
                }
                transfer(ctx, arg, escapes)?;
            }
            check_borrow_conflicts(ctx, args, None)?;
            if *callee != ctx.current_fn {
                ctx.calls.push(callee.clone());
            }
            ret
        }
    };
    e.ty = Some(ty);
    Ok(ty)
}

/// A place: a local (or `self`), optionally projected through fields.
/// Ownership and borrowing are questions about places, not names — a
/// field is a place in its own right (ADR 0020, ADR 0022).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct Place {
    root: String,
    fields: Vec<String>,
}

impl Place {
    fn local(name: &str) -> Place {
        Place {
            root: name.to_string(),
            fields: Vec::new(),
        }
    }

    /// `self` contains `other`: same root, and `self`'s field path is a
    /// prefix of `other`'s. `o` contains `o.inner`; not conversely.
    fn contains(&self, other: &Place) -> bool {
        self.root == other.root
            && self.fields.len() <= other.fields.len()
            && self.fields[..] == other.fields[..self.fields.len()]
    }

    /// Two places overlap when either contains the other. `o` overlaps
    /// `o.inner`; `o.a` and `o.b` do not.
    fn overlaps(&self, other: &Place) -> bool {
        self.contains(other) || other.contains(self)
    }

    fn render(&self) -> String {
        let mut s = self.root.clone();
        for f in &self.fields {
            s.push('.');
            s.push_str(f);
        }
        s
    }

    /// The `VarInfo` entry that carries this place's flow state. Fields
    /// of `self` are represented as pseudo-variables (`self.f`), so using
    /// only `root` would ask for `self`, an entry that does not exist.
    fn state_key(&self) -> String {
        self.render()
    }
}

/// The place an argument borrows, and whether the borrow is mutable. A
/// bare name that is already a class borrow counts too: it hands the
/// borrowed place on without an `&` at the call site.
fn borrow_place(ctx: &Ctx, arg: &Expr) -> Option<(Place, bool)> {
    match &arg.kind {
        ExprKind::Borrow {
            array,
            field,
            mutable,
        } => {
            let mut p = Place::local(array);
            if let Some(f) = field {
                p.fields.push(f.clone());
            }
            Some((p, *mutable))
        }
        ExprKind::Var(n) => match ctx.vars.get(n.as_str()).map(|v| v.ty) {
            Some(Ty::ClassRef(_, m)) | Some(Ty::ResRef(_, m)) => {
                Some((Place::local(n), m == Mutability::Mut))
            }
            _ => None,
        },
        _ => None,
    }
}

/// Within one call, a mutable borrow must not overlap any other borrow.
/// VCgen havocs the mutable argument into a fresh symbol and keeps the
/// other arguments' pre-call symbols, so overlapping borrows would let
/// the caller assume a contract framed over storage the callee actually
/// changed — unsound, not merely imprecise.
fn check_borrow_conflicts(
    ctx: &Ctx,
    args: &[Expr],
    receiver: Option<(Place, bool, Span)>,
) -> CResult<()> {
    let mut borrows: Vec<(Place, bool, Span)> = Vec::new();
    if let Some(r) = receiver {
        borrows.push(r);
    }
    for a in args {
        if let Some((p, m)) = borrow_place(ctx, a) {
            borrows.push((p, m, a.span));
        }
    }
    for i in 0..borrows.len() {
        for j in (i + 1)..borrows.len() {
            let (pi, mi, _) = &borrows[i];
            let (pj, mj, sj) = &borrows[j];
            if (*mi || *mj) && pi.overlaps(pj) {
                return Err(Diagnostic {
                    name: "borrow.conflict".into(),
                    title: format!("conflicting borrows of `{}` in one call", pi.render()),
                    span: *sj,
                    label: format!("this overlaps the borrow of `{}`", pi.render()),
                    notes: vec![(
                        "note".into(),
                        "a mutable borrow must not overlap another borrow in the same \
                         call: the callee's contract frames them as distinct storage"
                            .into(),
                    )],
                });
            }
        }
    }
    Ok(())
}

/// Handing a *value* over to a borrow is written at the call site, with
/// its mutability, so a reader sees where access — and, for `&mut`,
/// unique access — is given up. This is the rule array borrows already
/// follow (ADR 0023, ADR 0024). Passing along a borrow already held at
/// the same mutability hands over nothing new and needs no `&`.
fn require_explicit_borrow(ctx: &Ctx, arg: &Expr, pty: Ty) -> CResult<()> {
    let (m, owner, flipped) = match pty {
        Ty::ClassRef(ci, m) => (
            m,
            ctx.class_metas[ci].name.clone(),
            Ty::ClassRef(ci, flip(m)),
        ),
        Ty::ResRef(k, m) => (m, k.name().to_string(), Ty::ResRef(k, flip(m))),
        _ => return Ok(()),
    };
    // Passing along a *shared* borrow already held under the same type:
    // nothing is handed over that the caller did not already have, and
    // no `&` announces anything. Unique access is different — `&mut` is
    // always written, so every mutable borrow argument is visible at the
    // call site (which conflict detection and the caller's post-call
    // havoc both rely on).
    if m == Mutability::Shared {
        if let ExprKind::Var(n) = &arg.kind {
            if ctx.vars.get(n.as_str()).map(|v| v.ty) == Some(pty) {
                return Ok(());
            }
        }
    }
    let want = if m == Mutability::Mut { "&mut " } else { "&" };
    match arg.kind {
        ExprKind::Borrow { mutable, .. } if mutable == (m == Mutability::Mut) => Ok(()),
        ExprKind::Borrow { .. } => Err(Diagnostic {
            name: "type.borrow_mutability".into(),
            title: format!("expected `{}`, found `{}`", pty.name(), flipped.name()),
            span: arg.span,
            label: format!("write `{want}name`"),
            notes: vec![(
                "note".into(),
                "a borrow's mutability is written at the call site, not \
                 inferred from the parameter"
                    .into(),
            )],
        }),
        _ => Err(Diagnostic {
            name: "type.arg_borrow".into(),
            title: format!("`{owner}` is borrowed here, not moved"),
            span: arg.span,
            label: format!("write `{want}name`"),
            notes: vec![(
                "note".into(),
                "a borrow is written at the call site, so a reader sees where \
                 access is given up"
                    .into(),
            )],
        }),
    }
}

fn flip(m: Mutability) -> Mutability {
    match m {
        Mutability::Mut => Mutability::Shared,
        _ => Mutability::Mut,
    }
}

/// A class value passed by value is moved out of the local that named
/// it (ADR 0020). Only a plain name can be moved: a borrow keeps the
/// value, and a call result is already a temporary.
fn mark_moved(ctx: &mut Ctx, arg: &Expr) -> CResult<()> {
    match &arg.kind {
        ExprKind::Var(name) => {
            if ctx
                .vars
                .get(name.as_str())
                .is_some_and(|v| is_affine(v.ty))
            {
                ctx.moved.insert(Place::local(name));
            }
        }
        // `self.f` handed on by value: the *field* is the place that dies,
        // not the object. The object becomes partially moved, which is what
        // lets a `deinit` pass one field on and still read another
        // (ADR 0029).
        ExprKind::SelfField { field } => {
            let fty = ctx.in_class.and_then(|(ci, _)| {
                ctx.class_metas[ci]
                    .fields
                    .iter()
                    .find(|(n, _)| n == field)
                    .map(|(_, t)| *t)
            });
            if fty.is_some_and(is_affine) {
                ctx.moved.insert(Place {
                    root: "self".to_string(),
                    fields: vec![field.clone()],
                });
            }
        }
        _ => {}
    }
    Ok(())
}

/// Values that can be transferred but not duplicated: class values and
/// resources, and owned arrays, whose element storage is shared by every
/// name that reaches it.
fn is_affine(ty: Ty) -> bool {
    matches!(
        ty,
        Ty::Class(_) | Ty::Res(_) | Ty::Array(_, Mutability::Owned)
    )
}

fn mandatory_ty(ty: Ty) -> bool {
    matches!(ty, Ty::Res(kind) if kind.must_consume())
}

/// The one ownership sink.
///
/// Every construct that takes a value *by value* — a declaration, an
/// assignment, a field assignment, a call or constructor argument, a
/// return — ends here, so what a transfer means is written once: the
/// source place dies, and a loan brand may not cross a sink that outlives
/// the exposure it came from.
///
/// `escapes` names the sink for the escape diagnostic, and is `None` for a
/// sink that cannot outlive the body: a callee that has no way to give
/// storage back, or a local that inherits the brand instead.
///
/// Call it *after* the expression has been checked: a moved-from place is
/// unreadable, and the escape rule needs the expression's type.
/// Returns whether the value carries a mandatory-consumption obligation,
/// so a sink that is itself a place can keep it travelling. An owned
/// argument moves the authority into a callee whose parameter inherits
/// a type-level obligation; a return moves it to a caller whose receiving
/// place derives the same obligation from the result type.
fn transfer(ctx: &mut Ctx, e: &Expr, escapes: Option<(&str, Span)>) -> CResult<bool> {
    if let Some((how, span)) = escapes {
        reject_brand_escape(ctx, e, how, span)?;
    }
    let source = match &e.kind {
        ExprKind::Var(n) => Some(Place::local(n).state_key()),
        ExprKind::SelfField { field } => Some(
            Place {
                root: "self".to_string(),
                fields: vec![field.clone()],
            }
            .state_key(),
        ),
        _ => None,
    };
    // A fresh result of a mandatory resource type starts with an
    // obligation even though it has no source place. A move normally
    // finds the same obligation on its source; deriving it from the type
    // as well makes returns and compiler-sealed resource producers obey
    // the same rule without one-off minting hooks.
    let mut carries = e.ty.is_some_and(mandatory_ty);
    if let Some(name) = source {
        if let Some(v) = ctx.vars.get_mut(name.as_str()) {
            carries |= v.obligation;
            // The obligation goes with the token. Whether it is discharged
            // or merely relocated is the *sink's* answer, and the source
            // no longer owes it either way.
            v.obligation = false;
        }
    }
    mark_moved(ctx, e)?;
    Ok(carries)
}

/// No `#[must_consume]` fields: the marker list outside a class member.
const MARKED_NONE: &[(String, Span)] = &[];

/// Everything the checker knows about a place, as one value.
///
/// Branch joins and loop backedge checks use this rather than a chosen
/// subset, so a fact added later travels with the rest instead of leaking
/// out of whichever path was walked last (ADR 0030). Move state is the
/// exception and lives in `Ctx::moved`, because it is keyed by `Place`
/// rather than by name — a field is a place its object's name cannot
/// describe.
#[derive(Clone)]
struct PlaceState {
    initialized: bool,
    branded: bool,
    obligation: bool,
}

fn snapshot(ctx: &Ctx) -> HashMap<String, PlaceState> {
    ctx.vars
        .iter()
        .map(|(k, v)| {
            (
                k.clone(),
                PlaceState {
                    initialized: v.initialized,
                    branded: v.branded,
                    obligation: v.obligation,
                },
            )
        })
        .collect()
}

fn snapshot_has_place(snap: &HashMap<String, PlaceState>, place: &Place) -> bool {
    snap.contains_key(&place.state_key())
}

fn restore(ctx: &mut Ctx, snap: &HashMap<String, PlaceState>) {
    for (name, v) in ctx.vars.iter_mut() {
        if let Some(st) = snap.get(name) {
            v.initialized = st.initialized;
            v.branded = st.branded;
            v.obligation = st.obligation;
        } else {
            // Declared inside the block that is being unwound: it exists
            // only where it was declared.
            v.initialized = false;
        }
    }
}

/// An exposure is a real scope: its bindings and body locals disappear
/// when the loan closes. A must-consume token may not disappear with a
/// local, though; it must be consumed inside the exposure or moved into a
/// place that survives it.
fn reject_scoped_obligations(
    ctx: &Ctx,
    declared_before: &HashSet<String>,
    span: Span,
) -> CResult<()> {
    let mut abandoned: Vec<&String> = ctx
        .vars
        .iter()
        .filter(|(name, v)| !declared_before.contains(*name) && v.obligation)
        .map(|(name, _)| name)
        .collect();
    abandoned.sort();
    let Some(name) = abandoned.first() else {
        return Ok(());
    };
    Err(Diagnostic {
        name: "resource.abandoned".into(),
        title: format!("closing the exposure abandons `{name}`"),
        span,
        label: "this local scope ends with a must-consume token".into(),
        notes: vec![(
            "note".into(),
            "consume the authority inside the exposure or move it into a place that \
             survives the closing brace"
                .into(),
        )],
    })
}

/// Whether a field carries either the legacy per-field marker or a
/// resource type's mandatory-consumption property.
fn marked_field(marked: &[(String, Span)], field: &str) -> bool {
    marked.iter().any(|(name, _)| name == field)
}

/// At the end of a body, nothing may still be holding an obligation that
/// this frame was the last chance to discharge.
///
/// The obligation travels with the token, so this asks about every place
/// that holds one and not only about the field: moving it into a local
/// and dropping the local abandons the authority exactly as leaving it in
/// the field does. A type-mandatory resource follows owned parameters and
/// returns across verified calls; only an audited `#[consumes]` extern is
/// a terminal sink. The older field marker still means the authority must
/// leave the owning class's destructor.
///
/// `fields` says whether a marked field still holding its authority is an
/// abandonment. In a `deinit` it is — the object is ending, and nothing
/// after this will consume it. In an `init` or a method it is the normal
/// state of affairs: the class holds the authority, which is what the
/// field is *for*.
fn reject_outstanding_obligations(
    ctx: &Ctx,
    marked: &[(String, Span)],
    class_span: Span,
    member: &str,
    fields: bool,
) -> CResult<()> {
    let mut outstanding: Vec<&String> = ctx
        .vars
        .iter()
        .filter(|(_, v)| v.obligation)
        .map(|(name, _)| name)
        .collect();
    outstanding.sort();
    for name in outstanding {
        let field = name.strip_prefix("self.");
        if field.is_some() && !fields {
            continue;
        }
        let mandatory = ctx
            .vars
            .get(name.as_str())
            .is_some_and(|v| mandatory_ty(v.ty));
        let sealed_release = ctx
            .vars
            .get(name.as_str())
            .is_some_and(|v| matches!(v.ty, Ty::Res(ResKind::SystemDealloc)));
        let (span, label) = match field {
            Some(f) => (
                marked
                    .iter()
                    .find(|(name, _)| name == f)
                    .map_or(class_span, |(_, span)| *span),
                if mandatory {
                    "this field's resource type requires consumption"
                } else {
                    "this field is `#[must_consume]`"
                },
            ),
            None => (
                class_span,
                if mandatory {
                    "this resource type requires consumption"
                } else {
                    "this holds the authority of a `#[must_consume]` field"
                },
            ),
        };
        return Err(Diagnostic {
            name: "resource.abandoned".into(),
            title: format!("`{member}` abandons `{name}`"),
            span,
            label: label.into(),
            notes: vec![("note".into(), if sealed_release {
                "return the full allocation to raw authority and pass it with the base \
                 pointer to `unsafe system_dealloc`"
                    .into()
            } else if mandatory {
                "hand the authority through verified owned parameters until it reaches \
                 an audited `#[consumes]` operation"
                    .into()
            } else {
                "hand the authority on — pass it by value to something that consumes it \
                 — or drop the field marker and accept the leak"
                    .into()
            })],
        });
    }
    Ok(())
}

/// Overwriting a place that still holds a `#[must_consume]` token
/// abandons its authority: the same leak, reached by writing over it
/// rather than by walking away. Consume it first — that leaves the place
/// empty, and an empty place may be given a new value.
fn reject_overwrite_of_obligation(ctx: &Ctx, place: &Place, span: Span) -> CResult<()> {
    let name = place.render();
    let holds = ctx.vars.get(name.as_str()).is_some_and(|v| v.obligation);
    if !holds {
        return Ok(());
    }
    Err(Diagnostic {
        name: "resource.abandoned".into(),
        title: format!("assigning to `{name}` abandons its authority"),
        span,
        label: "this holds a `#[must_consume]` token".into(),
        notes: vec![(
            "note".into(),
            "consume what is there first — passing it by value empties the place — \
             and then assign; overwriting it drops the authority on the floor"
                .into(),
        )],
    })
}

/// A member may not leave a hole in `self`.
///
/// Moving a field out is legal *inside* a body — that is what
/// `partially-moved` means — but an `init` or a method has to put
/// something back before it exits. Its caller holds a whole class value
/// and knows nothing about which fields left; the class invariant is
/// stated over all of them, and an invariant over a hole is not a
/// question with an answer (ADR 0023).
///
/// A `deinit` is the exception, and the reason is the same one: the value
/// ceases to exist, so there is no invariant left to hold and no caller
/// left to mislead (ADR 0029).
fn reject_field_holes(ctx: &Ctx, class: &str, member: &str, span: Span) -> CResult<()> {
    let mut holes: Vec<String> = ctx
        .moved
        .iter()
        .filter(|p| p.root == "self")
        .map(|p| p.render())
        .collect();
    holes.sort();
    let Some(first) = holes.first() else {
        return Ok(());
    };
    Err(Diagnostic {
        name: "class.field_not_restored".into(),
        title: format!("`{class}::{member}` leaves `{first}` moved out"),
        span,
        label: "a member must leave `self` whole".into(),
        notes: vec![(
            "note".into(),
            "assign the field again before returning — `resource R old = self.f; \
             self.f = new;` replaces authority rather than losing it. Only a \
             `deinit` may hand a field on and leave, because the value is ending"
                .into(),
        )],
    })
}

/// An assignment is an escape unless the destination is itself branded: a
/// local that belongs to the exposure body dies with it.
fn escape_sink(dest_branded: bool, span: &Span) -> Option<(&'static str, Span)> {
    if dest_branded {
        None
    } else {
        Some(("be assigned to an outer local", *span))
    }
}

impl<'a> Ctx<'a> {
    /// The type of a place. A field place is recorded as a `self.f`
    /// pseudo-var, which is where a field's type lives; nothing deeper
    /// than one projection is nameable yet.
    fn place_ty(&self, p: &Place) -> Option<Ty> {
        self.vars.get(&p.state_key()).map(|v| v.ty)
    }

    /// Whether this place names a resource.
    fn is_resource_place(&self, p: &Place) -> bool {
        self.place_ty(p).is_some_and(|t| t.is_resource())
    }

    /// Whether this place names an owned array, whose moves are affine for
    /// a different reason: the elements are shared storage, not authority.
    fn is_array_place(&self, p: &Place) -> bool {
        self.place_ty(p)
            .is_some_and(|t| matches!(t, Ty::Array(_, Mutability::Owned)))
    }

    /// Which affine category a place belongs to, as the prefix its
    /// diagnostics carry. The consequence differs — a class you can
    /// rebuild, a resource is authority somebody else now holds, an array
    /// is storage two names would reach — so the name says which.
    fn affine_kind(&self, p: &Place) -> &'static str {
        if self.is_resource_place(p) {
            "resource"
        } else if self.is_array_place(p) {
            "array"
        } else {
            "class"
        }
    }

    /// A place is dead if it, or anything containing it, has been moved
    /// out: moving `o` kills `o.inner` too.
    fn is_moved(&self, p: &Place) -> bool {
        self.moved.iter().any(|m| m.contains(p))
    }

    /// Type of `self.field` for a *use*: reading it, or writing through
    /// it. A field whose value moved away has neither.
    fn self_field_ty(&self, field: &str, span: Span, mutating: bool) -> CResult<Ty> {
        let ty = self.self_field_ty_rebind(field, span, mutating)?;
        // A field whose value was moved out is dead, and so is the whole
        // object; its untouched siblings are still readable. This is what
        // `partially-moved` means, and it is what a `deinit` body that
        // hands one field on and reads another needs (ADR 0029).
        let place = Place {
            root: "self".to_string(),
            fields: vec![field.to_string()],
        };
        if self.is_moved(&place) {
            return Err(moved_out(self, &place, span, "read"));
        }
        Ok(ty)
    }

    /// Type of `self.field` as an assignment *target*. Rebinding a field
    /// is how a member gives it a value again, so unlike every other
    /// mention of a field this one is legal on a moved-out place.
    fn self_field_ty_rebind(&self, field: &str, span: Span, mutating: bool) -> CResult<Ty> {
        let Some((ci, is_mut)) = self.in_class else {
            return Err(Diagnostic {
                name: "type.self_outside_class".into(),
                title: "`self` outside a class member".into(),
                span,
                label: "fields exist only in inits and methods".into(),
                notes: vec![],
            });
        };
        if mutating && !is_mut {
            return Err(Diagnostic {
                name: "type.mutate_shared_self".into(),
                title: "a `&self` method cannot mutate fields".into(),
                span,
                label: "take `&mut self` to write".into(),
                notes: vec![],
            });
        }
        self.class_metas[ci]
            .fields
            .iter()
            .find(|(n, _)| n == field)
            .map(|(_, t)| *t)
            .ok_or_else(|| Diagnostic {
                name: "type.unknown_field".into(),
                title: format!("`{}` has no field `{field}`", self.class_metas[ci].name),
                span,
                label: "not declared in the class".into(),
                notes: vec![],
            })
    }

    fn require_field_init(&self, field: &str, span: Span) -> CResult<()> {
        if let Some(v) = self.vars.get(&format!("self.{field}")) {
            if !v.initialized {
                return Err(Diagnostic {
                    name: "type.uninitialized".into(),
                    title: format!("field `{field}` may be read before initialization"),
                    span,
                    label: "not assigned on every path to this point".into(),
                    notes: vec![],
                });
            }
        }
        Ok(())
    }
}

/// Whether values of this class can *hold* raw or resource storage,
/// directly or through a class field.
///
/// This is what decides whether a signature can launder a loan brand.
/// ADR 0027 argued that only a raw or resource return type could, because
/// Sable had no storage-typed fields — resource fields (ADR 0029) made that
/// false, and a class is now a container a brand can leave in.
fn class_holds_storage(metas: &[ClassMeta], ci: usize, depth: usize) -> bool {
    if depth > 16 {
        // Cyclic or absurdly deep: assume the worst rather than recurse.
        return true;
    }
    metas[ci].fields.iter().any(|(_, ty)| match ty {
        Ty::Raw(_) | Ty::Res(_) | Ty::ResRef(..) => true,
        Ty::Class(fci) => class_holds_storage(metas, *fci, depth + 1),
        _ => false,
    })
}

/// Whether an expression's value inherits a loan brand. Provenance is
/// what propagates: pointer arithmetic on branded storage, a split of a
/// branded span, a join involving one.
fn brand_of(ctx: &Ctx, e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Var(n) | ExprKind::Borrow { array: n, .. } => {
            ctx.vars.get(n.as_str()).is_some_and(|v| v.branded)
        }
        ExprKind::RawOp { args, .. } | ExprKind::ResOp { args, .. } => {
            args.iter().any(|a| brand_of(ctx, a))
        }
        _ => false,
    }
}

/// A branded value names storage that exists only for the body of its
/// exposure. It may be used by raw operations and the sealed resource
/// transformations, and nowhere else — returning it, assigning it to an
/// outer place, or handing it to a user function would let it outlive
/// the storage (ADR 0026).
fn reject_brand_escape(ctx: &Ctx, e: &Expr, how: &str, span: Span) -> CResult<()> {
    // The brand follows provenance, so the question is asked of the whole
    // expression: `raw_offset(p, 1)` and `split_off(&mut m, n)` name the
    // loan's storage exactly as `p` and `m` do. Asking it only of a bare
    // name would let one arithmetic operation launder it.
    if !brand_of(ctx, e) {
        return Ok(());
    }
    // A byte *loaded* from branded storage is an ordinary number: the
    // brand is about naming storage, not about having touched it.
    let ty = match &e.kind {
        // For a name the variable table is the authority: a bare
        // class- or resource-typed name is inferred without ever being
        // stamped on the expression.
        ExprKind::Var(n) | ExprKind::Borrow { array: n, .. } => {
            ctx.vars.get(n.as_str()).map(|v| v.ty)
        }
        _ => e.ty,
    };
    if !ty.is_some_and(|t| matches!(t, Ty::Raw(_) | Ty::Res(_) | Ty::ResRef(..))) {
        return Ok(());
    }
    let name = match &e.kind {
        ExprKind::Var(n) | ExprKind::Borrow { array: n, .. } => format!("`{n}`"),
        _ => "storage derived from this exposure".to_string(),
    };
    Err(Diagnostic {
        name: "expose.brand_escapes".into(),
        title: format!("{name} cannot {how}"),
        span,
        label: "this names storage borrowed for the exposure body".into(),
        notes: vec![(
            "note".into(),
            "an exposure lends the array's bytes for the body and takes them back at \
             the end; a pointer or resource that outlived it would name storage the \
             safe world owns again"
                .into(),
        )],
    })
}

/// Use of a place whose value has moved away. Classes and resources are
/// both affine and both land here; they get different diagnostic names
/// because the consequence differs — a class you can rebuild, a resource
/// is authority somebody else now holds.
fn moved_out(ctx: &Ctx, p: &Place, span: Span, how: &str) -> Diagnostic {
    let label = match how {
        "borrow" => "borrowing a moved-from place",
        "store" => "writing into a moved-from place",
        _ => "the value was passed by value earlier",
    }
    .to_string();
    if ctx.is_array_place(p) {
        return Diagnostic {
            name: "array.use_after_move".into(),
            title: format!("`{}` has been moved out", p.render()),
            span,
            label,
            notes: vec![(
                "note".into(),
                "an owned array moves into its new place: both names would reach \
                 the same elements, and the logic treats them as separate values"
                    .into(),
            )],
        };
    }
    if ctx.is_resource_place(p) {
        return Diagnostic {
            name: "resource.use_after_move".into(),
            title: format!("`{}` has been moved out", p.render()),
            span,
            label,
            notes: vec![(
                "note".into(),
                "resources are affine: passing one by value hands over the authority \
                 itself (ADR 0024); borrow with `&` to keep it"
                    .into(),
            )],
        };
    }
    Diagnostic {
        name: "class.use_after_move".into(),
        title: format!("`{}` has been moved out", p.render()),
        span,
        label,
        notes: vec![(
            "note".into(),
            "classes are affine: a by-value argument consumes the local \
             (ADR 0020), and a borrow of it is a use"
                .into(),
        )],
    }
}

/// A resource's *view* is ghost: clauses read `s.len`, program code does
/// not. That separation is what makes erasure real — a program able to
/// read the view would need it at runtime, and then the authority would
/// have a representation to forge (ADR 0024).
fn reject_view_read(ctx: &Ctx, name: &str, span: Span) -> CResult<()> {
    let Some(v) = ctx.vars.get(name) else {
        return Ok(());
    };
    let (Ty::Res(k) | Ty::ResRef(k, _)) = v.ty else {
        return Ok(());
    };
    Err(Diagnostic {
        name: "resource.view_is_ghost".into(),
        title: format!("`{name}` is a resource; its view is not program data"),
        span,
        label: format!("`{}` has no readable fields here", k.name()),
        notes: vec![(
            "note".into(),
            format!(
                "a clause may say `{name}.len`; program code may not, because \
                 resources are erased at runtime and carry nothing to read"
            ),
        )],
    })
}

fn array_elem_ty(ctx: &Ctx, array: &str, span: Span) -> CResult<IntTy> {
    reject_view_read(ctx, array, span)?;
    match ctx.vars.get(array) {
        Some(VarInfo {
            ty: Ty::Array(t, _),
            ..
        }) => Ok(*t),
        Some(v) => Err(Diagnostic {
            name: "type.not_an_array".into(),
            title: format!("`{array}` is not an array"),
            span,
            label: format!("this has type `{}`", v.ty.name()),
            notes: vec![],
        }),
        None => Err(Diagnostic {
            name: "type.unknown_variable".into(),
            title: format!("unknown variable `{array}`"),
            span,
            label: "not declared".into(),
            notes: vec![],
        }),
    }
}

/// Infer a same-typed integer pair, letting a literal side adopt the other
/// side's type (or the expected type when both need context).
fn infer_int_pair(
    ctx: &mut Ctx,
    lhs: &mut Expr,
    rhs: &mut Expr,
    expected: Option<Ty>,
    op_span: Span,
) -> CResult<IntTy> {
    let lhs_literal = is_literal_only(lhs);
    let rhs_literal = is_literal_only(rhs);
    let t = if lhs_literal && !rhs_literal {
        let t = int_of(ctx, rhs, expected, op_span)?;
        check_expr(ctx, lhs, Some(Ty::Int(t)))?;
        t
    } else {
        let t = int_of(ctx, lhs, expected, op_span)?;
        check_expr(ctx, rhs, Some(Ty::Int(t)))?;
        t
    };
    Ok(t)
}

fn int_of(ctx: &mut Ctx, e: &mut Expr, expected: Option<Ty>, op_span: Span) -> CResult<IntTy> {
    match check_expr(ctx, e, expected)? {
        Ty::Int(t) => Ok(t),
        other => Err(Diagnostic {
            name: "type.mismatch".into(),
            title: format!("arithmetic/comparison on `{}`", other.name()),
            span: op_span,
            label: "operands must be integers".into(),
            notes: vec![],
        }),
    }
}

fn is_literal_only(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::IntLit(_) => true,
        ExprKind::Unary {
            op: UnOp::Neg,
            operand,
        } => is_literal_only(operand),
        ExprKind::Binary { op, lhs, rhs, .. } if op.is_arith() => {
            is_literal_only(lhs) && is_literal_only(rhs)
        }
        _ => false,
    }
}

fn find_cycle(graph: &HashMap<String, Vec<String>>) -> Option<String> {
    #[derive(Clone, Copy, PartialEq)]
    enum State {
        Unvisited,
        InProgress,
        Done,
    }
    let mut state: HashMap<&str, State> = graph
        .keys()
        .map(|k| (k.as_str(), State::Unvisited))
        .collect();

    fn dfs<'a>(
        node: &'a str,
        graph: &'a HashMap<String, Vec<String>>,
        state: &mut HashMap<&'a str, State>,
    ) -> Option<String> {
        state.insert(node, State::InProgress);
        if let Some(callees) = graph.get(node) {
            for c in callees {
                match state.get(c.as_str()).copied() {
                    Some(State::InProgress) => return Some(c.clone()),
                    Some(State::Unvisited) => {
                        if let Some(found) = dfs(c.as_str(), graph, state) {
                            return Some(found);
                        }
                    }
                    _ => {}
                }
            }
        }
        state.insert(node, State::Done);
        None
    }

    let keys: Vec<&str> = graph.keys().map(|k| k.as_str()).collect();
    for k in keys {
        if state.get(k) == Some(&State::Unvisited) {
            if let Some(found) = dfs(k, graph, &mut state) {
                return Some(found);
            }
        }
    }
    None
}
