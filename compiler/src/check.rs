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
}

type CResult<T> = Result<T, Diagnostic>;

struct VarInfo {
    ty: Ty,
    initialized: bool,
    /// Declared `mut` (ADR 0016). Params are immutable; `self.f`
    /// pseudo-vars are governed by the receiver kind instead.
    mutable: bool,
}

struct Ctx<'a> {
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
    class_metas: &'a [ClassMeta],
    /// Template context (ADR 0009): bounded type parameter →
    /// (trait name, parameter index).
    tbounds: HashMap<String, (String, u8)>,
    /// Operator bindings (ADR 0012): (symbol, class meta index) → the
    /// bound function's name.
    operators: &'a HashMap<(OpSym, usize), String>,
    traits: &'a [TraitDecl],
}

/// The class index of a class-typed name (owned local or `&C` param).
fn class_of(ctx: &Ctx, name: &str, span: Span) -> CResult<usize> {
    match ctx.vars.get(name).map(|v| v.ty) {
        Some(Ty::Class(ci)) | Some(Ty::ClassRef(ci)) => Ok(ci),
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

pub fn check(program: &mut Program) -> CResult<CheckResult> {
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
                    // Class parameters: by value (moved in) or shared
                    // borrow (ADR 0020).
                    let ok = matches!(p.ty, Ty::Int(_) | Ty::Class(_) | Ty::ClassRef(_))
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
            if let Some(d) = &c.deinit {
                if !d.is_empty() {
                    return Err(Diagnostic {
                        name: "type.deinit_body".into(),
                        title: "`deinit` bodies must be empty for now".into(),
                        span: c.name_span,
                        label: "owned fields are freed automatically".into(),
                        notes: vec![],
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
            (Some(Ty::ClassRef(a)), Some(Ty::ClassRef(b))) if sig.params.len() == 2 => (a, b),
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
            calls: Vec::new(),
            in_class: None,
            in_init: false,
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
                },
            );
        }
        let returns = check_block(&mut ctx, &mut f.body, f.ret)?;
        if !returns && f.ret != Ty::Unit {
            return Err(Diagnostic {
                name: "type.missing_return".into(),
                title: format!("not all paths in `{}` return a value", f.name),
                span: f.name_span,
                label: "this function must return on every path".into(),
                notes: vec![],
            });
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
            calls: Vec::new(),
            in_class: None,
            in_init: false,
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
                },
            );
        }
        let returns = check_block(&mut ctx, &mut f.body, f.ret)?;
        if !returns && f.ret != Ty::Unit {
            return Err(Diagnostic {
                name: "type.missing_return".into(),
                title: format!("not all paths in `{}` return a value", f.name),
                span: f.name_span,
                label: "this function must return on every path".into(),
                notes: vec![],
            });
        }
    }
    program.fn_templates = templates;

    // Class members.
    for (ci, class) in program.classes.iter_mut().enumerate() {
        let meta = &class_metas[ci];
        for init in &mut class.inits {
            let mut ctx = Ctx {
                sigs: &sigs,
                current_fn: format!("{}::{}", meta.name, init.name),
                current_has_variant: false,
                in_test: false,
                vars: HashMap::new(),
                declared: HashSet::new(),
            moved: HashSet::new(),
                calls: Vec::new(),
                in_class: Some((ci, true)),
                in_init: true,
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
                    },
                );
            }
            check_block(&mut ctx, &mut init.body, Ty::Unit)?;
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
                calls: Vec::new(),
                in_class: Some((ci, m.self_kind == SelfKind::Mut)),
                in_init: false,
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
                    },
                );
            }
            let returns = check_block(&mut ctx, &mut m.f.body, m.f.ret)?;
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
            for init in &mut class.inits {
                let mut ctx = Ctx {
                    sigs: &sigs,
                    current_fn: format!("{}::{}", meta.name, init.name),
                    current_has_variant: false,
                    in_test: false,
                    vars: HashMap::new(),
                    declared: HashSet::new(),
            moved: HashSet::new(),
                    calls: Vec::new(),
                    in_class: Some((ci, true)),
                    in_init: true,
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
                        },
                    );
                }
                check_block(&mut ctx, &mut init.body, Ty::Unit)?;
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
                    calls: Vec::new(),
                    in_class: Some((ci, m.self_kind == SelfKind::Mut)),
                    in_init: false,
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
                        },
                    );
                }
                let returns = check_block(&mut ctx, &mut m.f.body, m.f.ret)?;
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

    Ok(CheckResult { sigs })
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
                if let Some(e) = init {
                    check_expr(ctx, e, Some(*ty))?;
                }
                ctx.vars.insert(
                    name.clone(),
                    VarInfo {
                        ty: *ty,
                        initialized: init.is_some(),
                        mutable: *mutable,
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
                if !was_mutable {
                    return Err(Diagnostic {
                        name: "mut.assign_immutable".into(),
                        title: format!("assignment to immutable local `{name}`"),
                        span: *name_span,
                        label: "declare it `mut` to allow assignment".into(),
                        notes: vec![],
                    });
                }
                if matches!(ty, Ty::Class(_)) {
                    // Reassignment of a class local is a move-in from a
                    // fresh owned value (the old value is dropped, with
                    // its RAII invariant check). Check first: operator
                    // sugar may rewrite a Binary RHS into the bound call
                    // (ADR 0012). Only call results and constructions
                    // move in; local-to-local moves would leave a
                    // moved-from name behind and stay deferred (ADR 0010).
                    check_expr(ctx, value, Some(ty))?;
                    if !matches!(
                        value.kind,
                        ExprKind::Call { .. } | ExprKind::CtorCall { .. }
                    ) {
                        return Err(Diagnostic {
                            name: "class.move_deferred".into(),
                            title: format!(
                                "class value `{name}` can only be reassigned from a call or constructor"
                            ),
                            span: *name_span,
                            label: "moves between locals are not supported yet (ADR 0010)".into(),
                            notes: vec![],
                        });
                    }
                    ctx.vars.get_mut(name.as_str()).unwrap().initialized = true;
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
                    ctx.vars.get_mut(name.as_str()).unwrap().initialized = true;
                }
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                check_expr(ctx, cond, Some(Ty::Bool))?;
                // Both flow facts are per-path: a name is initialized
                // after the `if` iff every falling-through branch
                // initialized it, and moved-out iff any of them moved
                // it. A branch that returns contributes neither.
                let snapshot = |ctx: &Ctx| -> HashMap<String, bool> {
                    ctx.vars
                        .iter()
                        .map(|(k, v)| (k.clone(), v.initialized))
                        .collect()
                };
                let before = snapshot(ctx);
                let before_moved = ctx.moved.clone();
                let then_ret = check_block(ctx, then_block, ret_ty)?;
                let after_then = snapshot(ctx);
                let after_then_moved = ctx.moved.clone();
                for (name, init) in &before {
                    if let Some(v) = ctx.vars.get_mut(name.as_str()) {
                        v.initialized = *init;
                    }
                }
                ctx.moved = before_moved.clone();
                let else_ret = match else_block {
                    Some(b) => check_block(ctx, b, ret_ty)?,
                    None => false,
                };
                let after_else = snapshot(ctx);
                let after_else_moved = ctx.moved.clone();
                // Reaching branches only: a branch that returns
                // contributes nothing to the fall-through state.
                let mut reaching_init: Vec<&HashMap<String, bool>> = Vec::new();
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
                    let was = before.get(name).copied().unwrap_or(false);
                    v.initialized = if reaching_init.is_empty() {
                        was
                    } else {
                        reaching_init
                            .iter()
                            .all(|m| m.get(name).copied().unwrap_or(was))
                    };
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
                let before: HashMap<String, bool> = ctx
                    .vars
                    .iter()
                    .map(|(k, v)| (k.clone(), v.initialized))
                    .collect();
                let _body_ret = check_block(ctx, body, ret_ty)?;
                for (name, v) in ctx.vars.iter_mut() {
                    v.initialized = before.get(name).copied().unwrap_or(false);
                }
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
                    }
                }
                returned = true;
            }
            Stmt::ExprStmt(e) => {
                check_expr(ctx, e, None)?;
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
                let t = check_expr(ctx, init, None)?;
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
                    },
                );
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
                let fty = ctx.self_field_ty(field, *field_span, true)?;
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
                check_expr(ctx, index, Some(Ty::Int(IntTy::U64)))?;
                check_expr(ctx, value, Some(Ty::Int(elem)))?;
            }
        }
    }
    Ok(returned)
}

fn stmt_span(stmt: &Stmt) -> Span {
    match stmt {
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
                    return Err(Diagnostic {
                        name: "class.use_after_move".into(),
                        title: format!("`{name}` has been moved out"),
                        span,
                        label: "the value was passed by value earlier".into(),
                        notes: vec![(
                            "note".into(),
                            "classes are affine: a by-value argument consumes the local                              (ADR 0020); borrow with `&` to keep it"
                                .into(),
                        )],
                    });
                }
                if matches!(v.ty, Ty::Class(_)) {
                    // Class values move: out through `return`, or into
                    // a by-value parameter (ADR 0010/0020).
                    if matches!(expected, Some(Ty::Class(_))) {
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
                Some(Ty::Class(_)) | Some(Ty::ClassRef(_))
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
            for (arg, p) in args.iter_mut().zip(&params) {
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
                    Ty::Class(_) => {
                        check_expr(ctx, arg, Some(p.ty))?;
                        mark_moved(ctx, arg)?;
                    }
                    _ => check_expr(ctx, arg, Some(p.ty)).map(|_| ())?,
                }
            }
            check_borrow_conflicts(args, None)?;
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
            let ci = match ctx.vars.get(recv.as_str()) {
                Some(VarInfo {
                    ty: Ty::Class(ci), ..
                }) => *ci,
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
            if self_kind == SelfKind::Mut
                && matches!(
                    ctx.vars.get(recv.as_str()).map(|v| v.ty),
                    Some(Ty::Class(_))
                )
                && !ctx.vars.get(recv.as_str()).is_some_and(|v| v.mutable)
            {
                return Err(Diagnostic {
                    name: "mut.method_immutable".into(),
                    title: format!("`&mut` method on immutable local `{recv}`"),
                    span: *recv_span,
                    label: format!("`{method}` mutates its receiver; declare `{recv}` `mut`"),
                    notes: vec![],
                });
            }
            for (arg, p) in args.iter_mut().zip(&params) {
                check_expr(ctx, arg, Some(p.ty))?;
            }
            check_borrow_conflicts(
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
                    return Err(Diagnostic {
                        name: "class.use_after_move".into(),
                        title: format!("`{}` has been moved out", p.render()),
                        span,
                        label: "borrowing a moved-from place".into(),
                        notes: vec![(
                            "note".into(),
                            "classes are affine: a by-value argument consumes the \
                             local (ADR 0020), and a borrow of it is a use"
                                .into(),
                        )],
                    });
                }
            }
            // `&x.f` / `&self.f` — borrowing a field as a place
            // (ADR 0020). The base must name a class; the field is
            // either class-typed or array-typed.
            if let Some(fname) = field {
                if *mutable {
                    return Err(Diagnostic {
                        name: "class.mut_borrow_deferred".into(),
                        title: "`&mut` class borrows are not supported yet".into(),
                        span,
                        label: "shared borrows only (ADR 0010)".into(),
                        notes: vec![],
                    });
                }
                let base = if array == "self" {
                    match ctx.in_class {
                        Some((ci, _)) => Ty::ClassRef(ci),
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
                let (Ty::Class(bci) | Ty::ClassRef(bci)) = base else {
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
                    Ty::Class(fci) => Ok(Ty::ClassRef(fci)),
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
            // `&c` of a class local, or a shared re-borrow of a `&C`
            // parameter passed along to a callee (ADR 0010).
            if let Some(Ty::Class(ci) | Ty::ClassRef(ci)) =
                ctx.vars.get(array.as_str()).map(|v| v.ty)
            {
                if *mutable {
                    return Err(Diagnostic {
                        name: "class.mut_borrow_deferred".into(),
                        title: "`&mut` class borrows are not supported yet".into(),
                        span,
                        label: "shared borrows only (ADR 0010)".into(),
                        notes: vec![],
                    });
                }
                return Ok(Ty::ClassRef(ci));
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
                    Some(Ty::Class(ci)) | Some(Ty::ClassRef(ci)) => Some((n.clone(), ci)),
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
            for (arg, pty) in args.iter_mut().zip(param_tys) {
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
                    Ty::Class(_) => {
                        check_expr(ctx, arg, Some(pty))?;
                        mark_moved(ctx, arg)?;
                    }
                    _ => check_expr(ctx, arg, Some(pty)).map(|_| ())?,
                }
            }
            check_borrow_conflicts(args, None)?;
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
}

/// The place an argument borrows, and whether the borrow is mutable.
fn borrow_place(arg: &Expr) -> Option<(Place, bool)> {
    let ExprKind::Borrow {
        array,
        field,
        mutable,
    } = &arg.kind
    else {
        return None;
    };
    let mut p = Place::local(array);
    if let Some(f) = field {
        p.fields.push(f.clone());
    }
    Some((p, *mutable))
}

/// Within one call, a mutable borrow must not overlap any other borrow.
/// VCgen havocs the mutable argument into a fresh symbol and keeps the
/// other arguments' pre-call symbols, so overlapping borrows would let
/// the caller assume a contract framed over storage the callee actually
/// changed — unsound, not merely imprecise.
fn check_borrow_conflicts(
    args: &[Expr],
    receiver: Option<(Place, bool, Span)>,
) -> CResult<()> {
    let mut borrows: Vec<(Place, bool, Span)> = Vec::new();
    if let Some(r) = receiver {
        borrows.push(r);
    }
    for a in args {
        if let Some((p, m)) = borrow_place(a) {
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

/// A class value passed by value is moved out of the local that named
/// it (ADR 0020). Only a plain name can be moved: a borrow keeps the
/// value, and a call result is already a temporary.
fn mark_moved(ctx: &mut Ctx, arg: &Expr) -> CResult<()> {
    if let ExprKind::Var(name) = &arg.kind {
        if ctx
            .vars
            .get(name.as_str())
            .is_some_and(|v| matches!(v.ty, Ty::Class(_)))
        {
            ctx.moved.insert(Place::local(name));
        }
    }
    Ok(())
}

impl<'a> Ctx<'a> {
    /// A place is dead if it, or anything containing it, has been moved
    /// out: moving `o` kills `o.inner` too.
    fn is_moved(&self, p: &Place) -> bool {
        self.moved.iter().any(|m| m.contains(p))
    }

    /// Some strict sub-place has been moved out. The whole can no
    /// longer move or be borrowed, but the untouched siblings are
    /// still readable. Nothing produces field moves yet (U7a); the
    /// query exists so the joins are already right when they do.
    #[allow(dead_code)]
    fn is_partially_moved(&self, p: &Place) -> bool {
        self.moved.iter().any(|m| p.contains(m) && m != p)
    }

    /// Type of `self.field`; `mutating` additionally requires an
    /// `init` or `&mut self` context.
    fn self_field_ty(&self, field: &str, span: Span, mutating: bool) -> CResult<Ty> {
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

fn array_elem_ty(ctx: &Ctx, array: &str, span: Span) -> CResult<IntTy> {
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
