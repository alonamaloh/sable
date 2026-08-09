//! Typechecking for the M1 subset: exact-width integer types with no
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
}

struct Ctx<'a> {
    sigs: &'a HashMap<String, FnSig>,
    current_fn: String,
    current_has_variant: bool,
    /// `test_*` functions: dynamic-only, excluded from verification,
    /// allowed owned arrays / borrows / array-passing (design §9).
    in_test: bool,
    vars: HashMap<String, VarInfo>,
    /// M1 rule: locals and parameters have pairwise-distinct names
    /// (keeps path-splitting and havoc in the VC generator scope-free).
    declared: HashSet<String>,
    /// Non-self callees (for mutual-recursion detection).
    calls: Vec<String>,
    /// Class-member context: (class meta index, self is &mut).
    in_class: Option<(usize, bool)>,
    /// Inside an `init`: fields start uninitialized, `return` forbidden.
    in_init: bool,
    class_metas: &'a [ClassMeta],
}

pub fn check(program: &mut Program) -> CResult<CheckResult> {
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
                label: "arrays are parameters only in M1".into(),
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
            let scalar_params = |params: &[Param]| -> CResult<()> {
                for p in params {
                    if !matches!(p.ty, Ty::Int(_)) {
                        return Err(Diagnostic {
                            name: "type.m5_member_param".into(),
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
                scalar_params(&i.params)?;
                inits.push((i.name.clone(), i.params.clone()));
            }
            let mut methods = Vec::new();
            for m in &c.methods {
                scalar_params(&m.f.params)?;
                methods.push((m.f.name.clone(), m.f.params.clone(), m.f.ret, m.self_kind));
            }
            if let Some(d) = &c.deinit {
                if !d.is_empty() {
                    return Err(Diagnostic {
                        name: "type.m5_deinit_body".into(),
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
                title: format!("`{}` is a test but has parameters, a return type, or contracts", f.name),
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
            calls: Vec::new(),
            in_class: None,
            in_init: false,
            class_metas: &class_metas,
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
                    name: "type.m1_option_param".into(),
                    title: "option-typed parameters are not supported yet".into(),
                    span: p.span,
                    label: "`option<T>` is a return type in M1".into(),
                    notes: vec![],
                });
            }
            ctx.vars.insert(
                p.name.clone(),
                VarInfo {
                    ty: p.ty,
                    initialized: true,
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
                calls: Vec::new(),
                in_class: Some((ci, true)),
                in_init: true,
                class_metas: &class_metas,
            };
            for p in &init.params {
                ctx.declared.insert(p.name.clone());
                ctx.vars.insert(
                    p.name.clone(),
                    VarInfo {
                        ty: p.ty,
                        initialized: true,
                    },
                );
            }
            for (fname, fty) in &meta.fields {
                ctx.vars.insert(
                    format!("self.{fname}"),
                    VarInfo {
                        ty: *fty,
                        initialized: false,
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
                calls: Vec::new(),
                in_class: Some((ci, m.self_kind == SelfKind::Mut)),
                in_init: false,
                class_metas: &class_metas,
            };
            for p in &m.f.params {
                ctx.declared.insert(p.name.clone());
                ctx.vars.insert(
                    p.name.clone(),
                    VarInfo {
                        ty: p.ty,
                        initialized: true,
                    },
                );
            }
            for (fname, fty) in &meta.fields {
                ctx.vars.insert(
                    format!("self.{fname}"),
                    VarInfo {
                        ty: *fty,
                        initialized: true,
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
            } => {
                if !ctx.declared.insert(name.clone()) {
                    return Err(Diagnostic {
                        name: "type.duplicate_name".into(),
                        title: format!("duplicate variable name `{name}`"),
                        span: *name_span,
                        label: "already declared in this function".into(),
                        notes: vec![(
                            "note".into(),
                            "M1 requires all locals in a function to have distinct names".into(),
                        )],
                    });
                }
                let alloc_init = matches!(
                    init.as_ref().map(|e| &e.kind),
                    Some(ExprKind::AllocArray { .. })
                );
                if matches!(ty, Ty::Array(_, Mutability::Owned)) && !ctx.in_test && !alloc_init {
                    return Err(Diagnostic {
                        name: "type.owned_array_outside_test".into(),
                        title: "owned arrays exist only in test functions for now".into(),
                        span: *name_span,
                        label: "allocation design is a scheduled deliverable (goals doc, Tier 2)"
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
                    },
                );
            }
            Stmt::Assign {
                name,
                name_span,
                value,
            } => {
                let ty = match ctx.vars.get(name.as_str()) {
                    Some(v) => v.ty,
                    None => {
                        return Err(Diagnostic {
                            name: "type.unknown_variable".into(),
                            title: format!("assignment to undeclared variable `{name}`"),
                            span: *name_span,
                            label: "not declared".into(),
                            notes: vec![],
                        })
                    }
                };
                if matches!(ty, Ty::Class(_)) {
                    return Err(Diagnostic {
                        name: "type.class_assign".into(),
                        title: format!("cannot assign to class value `{name}`"),
                        span: *name_span,
                        label: "class values cannot be reassigned".into(),
                        notes: vec![],
                    });
                }
                if matches!(ty, Ty::Array(..)) {
                    return Err(Diagnostic {
                        name: "type.array_assign".into(),
                        title: format!("cannot assign to array `{name}`"),
                        span: *name_span,
                        label: "borrowed arrays are read-only in M1".into(),
                        notes: vec![],
                    });
                }
                check_expr(ctx, value, Some(ty))?;
                ctx.vars.get_mut(name.as_str()).unwrap().initialized = true;
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                check_expr(ctx, cond, Some(Ty::Bool))?;
                let before: HashMap<String, bool> =
                    ctx.vars.iter().map(|(k, v)| (k.clone(), v.initialized)).collect();
                let then_ret = check_block(ctx, then_block, ret_ty)?;
                let after_then: HashMap<String, bool> =
                    ctx.vars.iter().map(|(k, v)| (k.clone(), v.initialized)).collect();
                for (name, init) in &before {
                    if let Some(v) = ctx.vars.get_mut(name.as_str()) {
                        v.initialized = *init;
                    }
                }
                let else_ret = match else_block {
                    Some(b) => check_block(ctx, b, ret_ty)?,
                    None => false,
                };
                // Initialized after the `if` iff initialized on every path
                // that falls through (returning branches contribute none).
                let after_else: HashMap<String, bool> =
                    ctx.vars.iter().map(|(k, v)| (k.clone(), v.initialized)).collect();
                for (name, v) in ctx.vars.iter_mut() {
                    let was = before.get(name).copied().unwrap_or(false);
                    let mut reaching = Vec::new();
                    if !then_ret {
                        reaching.push(after_then.get(name).copied().unwrap_or(false));
                    }
                    if !else_ret {
                        reaching.push(match else_block {
                            Some(_) => after_else.get(name).copied().unwrap_or(false),
                            None => was,
                        });
                    }
                    v.initialized = if reaching.is_empty() {
                        was
                    } else {
                        reaching.iter().all(|b| *b)
                    };
                }
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
                let before: HashMap<String, bool> =
                    ctx.vars.iter().map(|(k, v)| (k.clone(), v.initialized)).collect();
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
                        })
                    }
                    (None, _) => {
                        return Err(Diagnostic {
                            name: "type.missing_return_value".into(),
                            title: format!("`return;` in a function returning `{}`", ret_ty.name()),
                            span: *span,
                            label: "a value is required".into(),
                            notes: vec![],
                        })
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
                    },
                );
            }
            Stmt::FieldAssign {
                field,
                field_span,
                value,
            } => {
                let fty = ctx.self_field_ty(field, *field_span, true)?;
                check_expr(ctx, value, Some(fty))?;
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
                let (elem, mutability) = match ctx.vars.get(array.as_str()) {
                    Some(VarInfo {
                        ty: Ty::Array(t, m),
                        ..
                    }) => (*t, *m),
                    Some(v) => {
                        return Err(Diagnostic {
                            name: "type.not_an_array".into(),
                            title: format!("`{array}` is not an array"),
                            span: *array_span,
                            label: format!("this has type `{}`", v.ty.name()),
                            notes: vec![],
                        })
                    }
                    None => {
                        return Err(Diagnostic {
                            name: "type.unknown_variable".into(),
                            title: format!("unknown variable `{array}`"),
                            span: *array_span,
                            label: "not declared".into(),
                            notes: vec![],
                        })
                    }
                };
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
                    })
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
                    })
                }
            };
            if *n < t.min() || *n > t.max() {
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
                if matches!(v.ty, Ty::Class(_)) {
                    return Err(Diagnostic {
                        name: "type.class_value".into(),
                        title: format!("class value `{name}` used as a value"),
                        span,
                        label: "class values cannot be copied or moved yet; call methods on \
                                them (`{name}.method(...)`)"
                            .into(),
                        notes: vec![],
                    });
                }
                if matches!(v.ty, Ty::Array(..)) {
                    return Err(Diagnostic {
                        name: "type.m1_array_value".into(),
                        title: format!("array `{name}` used as a value"),
                        span,
                        label: "arrays support only `a[i]` and `a.len` in M1".into(),
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
                })
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
                    })
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
                        "narrowing (`narrow<T>`, with a fits-VC) lands in M2".into(),
                    )],
                });
            }
            Ty::Int(*target)
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
            init,
            args,
        } => {
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
                check_expr(ctx, arg, Some(p.ty))?;
            }
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
                    })
                }
                None => {
                    return Err(Diagnostic {
                        name: "type.unknown_variable".into(),
                        title: format!("unknown variable `{recv}`"),
                        span: *recv_span,
                        label: "not declared".into(),
                        notes: vec![],
                    })
                }
            };
            let Some((_, params, ret, _)) = ctx.class_metas[ci]
                .methods
                .iter()
                .find(|(n, _, _, _)| n == method)
                .cloned()
            else {
                return Err(Diagnostic {
                    name: "type.unknown_method".into(),
                    title: format!(
                        "`{}` has no method `{method}`",
                        ctx.class_metas[ci].name
                    ),
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
            for (arg, p) in args.iter_mut().zip(&params) {
                check_expr(ctx, arg, Some(p.ty))?;
            }
            ctx.calls
                .push(format!("{}::{method}", ctx.class_metas[ci].name));
            ret
        }
        ExprKind::ArrayLit(elems) => match expected {
            Some(Ty::Array(t, Mutability::Owned)) => {
                if !ctx.in_test {
                    return Err(Diagnostic {
                        name: "type.owned_array_outside_test".into(),
                        title: "array literals exist only in test functions for now".into(),
                        span,
                        label: "see docs/PLAN.md (M3)".into(),
                        notes: vec![],
                    });
                }
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
                })
            }
        },
        ExprKind::Borrow { array, mutable } => {
            if !ctx.in_test {
                return Err(Diagnostic {
                    name: "type.borrow_outside_test".into(),
                    title: "borrow expressions exist only in test functions for now".into(),
                    span,
                    label: "passing borrowed arrays between verified functions lands in M4"
                        .into(),
                    notes: vec![],
                });
            }
            let elem = array_elem_ty(ctx, array, span)?;
            let owned = matches!(
                ctx.vars.get(array.as_str()).map(|v| v.ty),
                Some(Ty::Array(_, Mutability::Owned))
            );
            if !owned {
                return Err(Diagnostic {
                    name: "type.borrow_non_owned".into(),
                    title: format!("cannot borrow `{array}`"),
                    span,
                    label: "only owned test arrays can be borrowed".into(),
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
                    name: "type.m1_option_position".into(),
                    title: "`some(...)` outside an option-returning position".into(),
                    span,
                    label: "options are created only where an `option<T>` is expected".into(),
                    notes: vec![],
                })
            }
        },
        ExprKind::NoneE => match expected {
            Some(Ty::Option(t)) => Ty::Option(t),
            _ => {
                return Err(Diagnostic {
                    name: "type.m1_option_position".into(),
                    title: "`none` outside an option-returning position".into(),
                    span,
                    label: "options are created only where an `option<T>` is expected".into(),
                    notes: vec![],
                })
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
                        })
                    }
                    _ => {
                        return Err(Diagnostic {
                            name: "type.mismatch".into(),
                            title: "unary minus on a non-integer".into(),
                            span,
                            label: "expected an integer".into(),
                            notes: vec![],
                        })
                    }
                }
            }
            UnOp::Not => {
                check_expr(ctx, operand, Some(Ty::Bool))?;
                Ty::Bool
            }
        },
        ExprKind::Binary { op, op_span, lhs, rhs } => {
            let op = *op;
            let op_span = *op_span;
            if op.is_arith() {
                let expected_int = match expected {
                    Some(Ty::Int(_)) => expected,
                    _ => None,
                };
                let t = infer_int_pair(ctx, lhs, rhs, expected_int, op_span)?;
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
            args,
        } => {
            let sig = match ctx.sigs.get(callee.as_str()) {
                Some(s) => s,
                None => {
                    return Err(Diagnostic {
                        name: "type.unknown_function".into(),
                        title: format!("call to unknown function `{callee}`"),
                        span: *callee_span,
                        label: "not defined in this module".into(),
                        notes: vec![],
                    })
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
                    title: format!("`{callee}` calls itself without a `variant`", ),
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
                            name: "type.m0_bool_arg".into(),
                            title: "bool-typed call arguments are not supported yet".into(),
                            span: arg.span,
                            label: "bool argument".into(),
                            notes: vec![],
                        })
                    }
                    Ty::Array(elem, m) => {
                        if !ctx.in_test {
                            return Err(Diagnostic {
                                name: "type.m1_array_arg".into(),
                                title: "array-typed call arguments are not supported yet \
                                        outside tests"
                                    .into(),
                                span: arg.span,
                                label: "verified array-passing lands in M4".into(),
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
                    _ => check_expr(ctx, arg, Some(pty)).map(|_| ())?,
                }
            }
            if *callee != ctx.current_fn {
                ctx.calls.push(callee.clone());
            }
            ret
        }
    };
    e.ty = Some(ty);
    Ok(ty)
}

impl<'a> Ctx<'a> {
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
                title: format!(
                    "`{}` has no field `{field}`",
                    self.class_metas[ci].name
                ),
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
            ty: Ty::Array(t, _), ..
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
    let mut state: HashMap<&str, State> =
        graph.keys().map(|k| (k.as_str(), State::Unvisited)).collect();

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
