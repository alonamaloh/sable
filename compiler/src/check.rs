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

#[derive(Clone)]
pub struct RecordMeta {
    pub name: String,
    pub fields: Vec<(String, Ty)>,
    pub layout: StorageLayout,
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
    /// Arrays whose bytes are on loan to an open exposure body, keyed by
    /// the owner's name and carrying the loan's pointer and resource
    /// names for the refusal. While a name is here the loan is the
    /// storage's only name: reading, writing, borrowing, measuring, or
    /// re-exposing the owner is refused (`expose.owner_frozen`,
    /// ADR 0073).
    exposed: HashMap<String, (String, String)>,
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
    record_metas: &'a [RecordMeta],
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
    ctx.vars
        .get(name)
        .and_then(|v| v.ty.class_index())
        .ok_or_else(|| Diagnostic {
            name: "type.mismatch".into(),
            title: format!("`{name}` is not a class value"),
            span,
            label: "field access needs a class-typed receiver".into(),
            notes: vec![],
        })
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

/// `uart-poll-v1` has one physical UART0 and one corresponding root
/// authority. Until a later profile gives capabilities device identities,
/// accepting two UART parameters would let VCgen reason about independent
/// views while both executable semantics operate on the singleton device.
fn check_uart_params(params: &[Param]) -> CResult<()> {
    let mut first: Option<&Param> = None;
    for param in params
        .iter()
        .filter(|param| param.ty.res_kind() == Some(ResKind::Uart))
    {
        if let Some(first) = first {
            return Err(Diagnostic {
                name: "uart.multiple_authority".into(),
                title: "`uart-poll-v1` provides one UART authority".into(),
                span: param.span,
                label: "second UART parameter".into(),
                notes: vec![(
                    "first UART parameter".into(),
                    format!(
                        "`{}` is the singleton profile capability; pass or return that token instead of accepting another",
                        first.name
                    ),
                )],
            });
        }
        first = Some(param);
    }
    Ok(())
}

/// Trait calls are currently modeled as pure integer operations in template
/// verification. In particular, they have no resource-view transition with
/// which to model a UART borrow or owned UART result. Keep the singleton
/// profile capability out of trait interfaces until that contract machinery
/// is resource-aware instead of accepting a signature that later VCgen cannot
/// represent.
fn check_uart_trait_methods(traits: &[TraitDecl]) -> CResult<()> {
    for tr in traits {
        for method in &tr.methods {
            if let Some(param) = method
                .params
                .iter()
                .find(|param| param.ty.res_kind() == Some(ResKind::Uart))
            {
                return Err(Diagnostic {
                    name: "uart.trait_unsupported".into(),
                    title: "UART authority is not supported in trait methods".into(),
                    span: param.span,
                    label: "keep `resource Uart` out of trait method signatures".into(),
                    notes: vec![(
                        "note".into(),
                        "trait calls are verified through abstract integer contracts; they do \
                         not yet model a UART state transition"
                            .into(),
                    )],
                });
            }
            if method.ret.res_kind() == Some(ResKind::Uart) {
                return Err(Diagnostic {
                    name: "uart.trait_unsupported".into(),
                    title: "UART authority is not supported in trait methods".into(),
                    span: method.name_span,
                    label: "a trait method may not return `resource Uart`".into(),
                    notes: vec![(
                        "note".into(),
                        "the `uart-poll-v1` capability is a singleton passed explicitly through \
                         ordinary functions; trait contracts do not yet model its state transition"
                            .into(),
                    )],
                });
            }
        }
    }
    Ok(())
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
        let what = match &f.ret {
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
        if let Some(kind) = p.ty.res_kind().filter(|kind| kind.sealed_terminal()) {
            return Err(Diagnostic {
                name: "resource.release_sealed".into(),
                title: format!("{} authority may not cross an extern boundary", kind.name()),
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
        // Explicit resource whitelist: a new resource kind must make a
        // deliberate ABI decision. In particular, device-profile authority
        // is meaningful only to compiler intrinsics and may not cross FFI.
        let ok = match p.ty.res_kind() {
            Some(kind) => kind.extern_abi_allowed(),
            None => matches!(p.ty, Ty::Int(_) | Ty::Raw(_) | Ty::RawRecord(_)),
        };
        if !ok {
            return Err(Diagnostic {
                name: "extern.param_abi".into(),
                title: format!("`{}` is not an ABI type", p.ty.clone().name()),
                span: p.span,
                label: "not in the explicit extern ABI whitelist".into(),
                notes: vec![(
                    "note".into(),
                    "extern parameters are integers, raw pointers, or the explicitly \
                     supported RawSpan, OpenFile, and PosixWorld resources; a safe array, \
                     class, or machine-profile capability needs semantics this ABI does \
                     not provide"
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
    validate_declared_aggregate_payloads(program)?;
    let mut unsafe_regions = 0usize;
    let traits_c: Vec<TraitDecl> = program.traits.clone();
    check_uart_trait_methods(&traits_c)?;
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
        if f.extern_info.is_none() {
            check_uart_params(&f.params)?;
        }
        sigs.insert(
            f.name.clone(),
            FnSig {
                params: f.params.clone(),
                ret: f.ret.clone(),
            },
        );
    }

    // POD record signatures and explicit layout validation (ADR 0054).
    // This is intentionally independent of class validation: the two
    // categories share a source namespace, not ownership semantics.
    let mut record_metas: Vec<RecordMeta> = Vec::new();
    {
        let mut seen: HashSet<String> = sigs.keys().cloned().collect();
        for r in &program.records {
            if !seen.insert(r.name.clone()) {
                return Err(Diagnostic {
                    name: "record.duplicate".into(),
                    title: format!("`{}` is defined twice", r.name),
                    span: r.name_span,
                    label: "functions, classes, and records share one namespace".into(),
                    notes: vec![],
                });
            }
            if r.layout.size <= 0
                || r.layout.align <= 0
                || (r.layout.align & (r.layout.align - 1)) != 0
            {
                return Err(Diagnostic {
                    name: "record.bad_layout".into(),
                    title: format!("record `{}` has an invalid layout", r.name),
                    span: r.layout_span,
                    label: "size must be positive; alignment must be a positive power of two"
                        .into(),
                    notes: vec![(
                        "note".into(),
                        "layout establishes storage geometry only; it does not grant a byte \
                         representation"
                            .into(),
                    )],
                });
            }
            let mut fields = Vec::new();
            let mut field_names = HashSet::new();
            let mut extents: Vec<(i128, i128, &str, Span)> = Vec::new();
            for field in &r.fields {
                if !field_names.insert(field.name.clone()) {
                    return Err(Diagnostic {
                        name: "record.duplicate_field".into(),
                        title: format!("duplicate field `{}`", field.name),
                        span: field.span,
                        label: "already declared in this record".into(),
                        notes: vec![],
                    });
                }
                let field_layout = record_field_layout(&field.ty, &field.name, field.span)?;
                let end =
                    field
                        .offset
                        .checked_add(field_layout.size)
                        .ok_or_else(|| Diagnostic {
                            name: "record.field_out_of_bounds".into(),
                            title: format!("field `{}` extent overflows", field.name),
                            span: field.offset_span,
                            label: "offset plus field size is not representable".into(),
                            notes: vec![],
                        })?;
                // A record value is promised aligned only to the record's
                // declared alignment.  The relative field offset therefore
                // establishes an aligned address only when the outer
                // alignment is itself compatible with the field alignment.
                // Without this check, an `align := 1` record could claim a
                // `u64` field at offset zero even though a valid record base
                // need not be u64-aligned.
                if r.layout.align % field_layout.align != 0 {
                    return Err(Diagnostic {
                        name: "record.field_alignment".into(),
                        title: format!(
                            "record `{}` is under-aligned for field `{}`",
                            r.name, field.name
                        ),
                        span: r.layout_span,
                        label: format!(
                            "record alignment {} must be a multiple of the field's alignment {}",
                            r.layout.align, field_layout.align
                        ),
                        notes: vec![(
                            "note".into(),
                            "a record base is guaranteed only the record's declared alignment; \
                             the field offset cannot repair an under-aligned base"
                                .into(),
                        )],
                    });
                }
                if field.offset < 0 || field.offset % field_layout.align != 0 || end > r.layout.size
                {
                    return Err(Diagnostic {
                        name: "record.field_out_of_bounds".into(),
                        title: format!(
                            "field `{}` does not fit its declared record layout",
                            field.name
                        ),
                        span: field.offset_span,
                        label: format!(
                            "offset {} must be {}-aligned and the {}-byte field must end by {}",
                            field.offset, field_layout.align, field_layout.size, r.layout.size
                        ),
                        notes: vec![],
                    });
                }
                if let Some((_, _, other, other_span)) = extents
                    .iter()
                    .find(|(lo, hi, _, _)| field.offset < *hi && *lo < end)
                {
                    return Err(Diagnostic {
                        name: "record.overlapping_fields".into(),
                        title: format!("fields `{other}` and `{}` overlap", field.name),
                        span: field.offset_span,
                        label: "record fields must occupy disjoint half-open extents".into(),
                        notes: vec![(
                            "note".into(),
                            format!(
                                "the earlier field's offset is declared at byte {}",
                                other_span.start
                            ),
                        )],
                    });
                }
                extents.push((field.offset, end, field.name.as_str(), field.offset_span));
                fields.push((field.name.clone(), field.ty.clone()));
            }
            record_metas.push(RecordMeta {
                name: r.name.clone(),
                fields,
                layout: r.layout,
            });
        }
    }

    // Class signatures + validation.
    let mut class_metas: Vec<ClassMeta> = Vec::new();
    {
        let mut seen = HashSet::new();
        for c in &program.classes {
            if !seen.insert(c.name.clone())
                || sigs.contains_key(&c.name)
                || program.records.iter().any(|r| r.name == c.name)
            {
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
                if fld.ty.res_kind() == Some(ResKind::Uart) {
                    return Err(Diagnostic {
                        name: "uart.field_unsupported".into(),
                        title: "the singleton UART capability may not be stored in a class".into(),
                        span: fld.span,
                        label: "keep `resource Uart` as an explicit parameter or local".into(),
                        notes: vec![(
                            "note".into(),
                            "device-identified profile capabilities and functional field \
                             write-back are deferred; accepting this field would make the \
                             proof and executable machine models disagree"
                                .into(),
                        )],
                    });
                }
                fields.push((fld.name.clone(), fld.ty.clone()));
            }
            let scalar_params = |params: &[Param], allow_shared_arrays: bool| -> CResult<()> {
                check_uart_params(params)?;
                for p in params {
                    member_param_ty(&p.ty, p.span, allow_shared_arrays)?;
                }
                Ok(())
            };
            let mut inits = Vec::new();
            for i in &c.inits {
                scalar_params(&i.params, true)?;
                inits.push((i.name.clone(), i.params.clone()));
            }
            let mut methods = Vec::new();
            for m in &c.methods {
                scalar_params(&m.f.params, false)?;
                methods.push((
                    m.f.name.clone(),
                    m.f.params.clone(),
                    m.f.ret.clone(),
                    m.self_kind,
                ));
            }
            if c.deinit.is_none() {
                if let Some(f) = c
                    .fields
                    .iter()
                    .find(|f| f.must_consume || mandatory_ty(f.ty.clone()))
                {
                    let mandatory = mandatory_ty(f.ty.clone());
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
            sig.params.first().map(|p| p.ty.clone()),
            sig.params.get(1).map(|p| p.ty.clone()),
        ) {
            (Some(a), Some(b))
                if sig.params.len() == 2
                    && matches!(
                        (a.as_class_borrow(), b.as_class_borrow()),
                        (Some((_, Mutability::Shared)), Some((_, Mutability::Shared)))
                    ) =>
            {
                (
                    a.class_index()
                        .expect("a shared class borrow names a class"),
                    b.class_index()
                        .expect("a shared class borrow names a class"),
                )
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
            exposed: HashMap::new(),
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
            record_metas: &record_metas,
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
            ctx.vars.insert(
                p.name.clone(),
                VarInfo {
                    ty: p.ty.clone(),
                    initialized: true,
                    mutable: false,
                    branded: false,
                    obligation: mandatory_ty(p.ty.clone()),
                },
            );
        }
        let returns = check_block(&mut ctx, &mut f.body, f.ret.clone())?;
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
            reject_outstanding_obligations(&ctx, MARKED_NONE, f.name_span, &f.name, true)?;
        }
        call_graph.insert(f.name.clone(), ctx.calls);
    }

    // Fn templates (ADR 0009): typecheck against the abstract integer
    // model. `Ty::Param` stays distinct from `IntTy`; parameter-specific
    // gates (literals, conversions, division) fire explicitly on the way.
    let mut templates = std::mem::take(&mut program.fn_templates);
    for f in &mut templates {
        check_uart_params(&f.params)?;
        let mut ctx = Ctx {
            sigs: &sigs,
            current_fn: f.name.clone(),
            current_has_variant: f.variant.is_some(),
            in_test: false,
            vars: HashMap::new(),
            exposed: HashMap::new(),
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
            record_metas: &record_metas,
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
                    ty: p.ty.clone(),
                    initialized: true,
                    mutable: false,
                    branded: false,
                    obligation: mandatory_ty(p.ty.clone()),
                },
            );
        }
        let returns = check_block(&mut ctx, &mut f.body, f.ret.clone())?;
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
            reject_outstanding_obligations(&ctx, MARKED_NONE, f.name_span, &f.name, true)?;
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
            .filter(|f| f.must_consume || mandatory_ty(f.ty.clone()))
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
                exposed: HashMap::new(),
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
                record_metas: &record_metas,
                tbounds: HashMap::new(),
                operators: &operators,
                traits: &traits_c,
            };
            for p in &init.params {
                ctx.declared.insert(p.name.clone());
                ctx.vars.insert(
                    p.name.clone(),
                    VarInfo {
                        ty: p.ty.clone(),
                        initialized: true,
                        mutable: false,
                        branded: false,
                        obligation: mandatory_ty(p.ty.clone()),
                    },
                );
            }
            for (fname, fty) in &meta.fields {
                ctx.vars.insert(
                    format!("self.{fname}"),
                    VarInfo {
                        ty: fty.clone(),
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
                exposed: HashMap::new(),
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
                record_metas: &record_metas,
                tbounds: HashMap::new(),
                operators: &operators,
                traits: &traits_c,
            };
            for p in &m.f.params {
                ctx.declared.insert(p.name.clone());
                ctx.vars.insert(
                    p.name.clone(),
                    VarInfo {
                        ty: p.ty.clone(),
                        initialized: true,
                        mutable: false,
                        branded: false,
                        obligation: mandatory_ty(p.ty.clone()),
                    },
                );
            }
            for (fname, fty) in &meta.fields {
                ctx.vars.insert(
                    format!("self.{fname}"),
                    VarInfo {
                        ty: fty.clone(),
                        initialized: true,
                        mutable: true,
                        branded: false,
                        obligation: marked_field(&marked, fname),
                    },
                );
            }
            let returns = check_block(&mut ctx, &mut m.f.body, m.f.ret.clone())?;
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
                exposed: HashMap::new(),
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
                record_metas: &record_metas,
                tbounds: HashMap::new(),
                operators: &operators,
                traits: &traits_c,
            };
            for (fname, fty) in &meta.fields {
                ctx.vars.insert(
                    format!("self.{fname}"),
                    VarInfo {
                        ty: fty.clone(),
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
    // abstract integer model; `Ty::Param` stays distinct from `IntTy`. Template
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
                if fld.ty.res_kind() == Some(ResKind::Uart) {
                    return Err(Diagnostic {
                        name: "uart.field_unsupported".into(),
                        title: "the singleton UART capability may not be stored in a class".into(),
                        span: fld.span,
                        label: "keep `resource Uart` as an explicit parameter or local".into(),
                        notes: vec![(
                            "note".into(),
                            "device-identified profile capabilities and functional field \
                             write-back are deferred"
                                .into(),
                        )],
                    });
                }
                fields.push((fld.name.clone(), fld.ty.clone()));
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
                    .map(|m| {
                        (
                            m.f.name.clone(),
                            m.f.params.clone(),
                            m.f.ret.clone(),
                            m.self_kind,
                        )
                    })
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
                .filter(|f| f.must_consume || mandatory_ty(f.ty.clone()))
                .map(|f| (f.name.clone(), f.span))
                .collect();
            let class_span = class.name_span;
            for init in &mut class.inits {
                check_uart_params(&init.params)?;
                let mut ctx = Ctx {
                    sigs: &sigs,
                    current_fn: format!("{}::{}", meta.name, init.name),
                    current_has_variant: false,
                    in_test: false,
                    vars: HashMap::new(),
                    exposed: HashMap::new(),
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
                    record_metas: &record_metas,
                    tbounds: ctb.clone(),
                    operators: &operators,
                    traits: &traits_c,
                };
                for p in &init.params {
                    ctx.declared.insert(p.name.clone());
                    ctx.vars.insert(
                        p.name.clone(),
                        VarInfo {
                            ty: p.ty.clone(),
                            initialized: true,
                            mutable: false,
                            branded: false,
                            obligation: mandatory_ty(p.ty.clone()),
                        },
                    );
                }
                for (fname, fty) in &meta.fields {
                    ctx.vars.insert(
                        format!("self.{fname}"),
                        VarInfo {
                            ty: fty.clone(),
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
                check_uart_params(&m.f.params)?;
                let mut ctx = Ctx {
                    sigs: &sigs,
                    current_fn: format!("{}::{}", meta.name, m.f.name),
                    current_has_variant: false,
                    in_test: false,
                    vars: HashMap::new(),
                    exposed: HashMap::new(),
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
                    record_metas: &record_metas,
                    tbounds: ctb.clone(),
                    operators: &operators,
                    traits: &traits_c,
                };
                for p in &m.f.params {
                    ctx.declared.insert(p.name.clone());
                    ctx.vars.insert(
                        p.name.clone(),
                        VarInfo {
                            ty: p.ty.clone(),
                            initialized: true,
                            mutable: false,
                            branded: false,
                            obligation: mandatory_ty(p.ty.clone()),
                        },
                    );
                }
                for (fname, fty) in &meta.fields {
                    ctx.vars.insert(
                        format!("self.{fname}"),
                        VarInfo {
                            ty: fty.clone(),
                            initialized: true,
                            mutable: true,
                            branded: false,
                            obligation: marked_field(&marked, fname),
                        },
                    );
                }
                let returns = check_block(&mut ctx, &mut m.f.body, m.f.ret.clone())?;
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
                    exposed: HashMap::new(),
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
                    record_metas: &record_metas,
                    tbounds: ctb.clone(),
                    operators: &operators,
                    traits: &traits_c,
                };
                for (fname, fty) in &meta.fields {
                    ctx.vars.insert(
                        format!("self.{fname}"),
                        VarInfo {
                            ty: fty.clone(),
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
                if let Some(payload) = ty.as_affine_option_payload() {
                    affine_option_payload(payload, *name_span)?;
                    if !*mutable {
                        return Err(Diagnostic {
                            name: "mut.option_take_immutable".into(),
                            title: format!("affine-option local `{name}` is immutable"),
                            span: *name_span,
                            label: "write `mut option<...>` so `.take` may leave `none` behind"
                                .into(),
                            notes: vec![(
                                "note".into(),
                                "taking an owned payload changes the option's value even though it preserves the local's initialized state".into(),
                            )],
                        });
                    }
                    if init.is_none() {
                        return Err(Diagnostic {
                            name: "option.affine_initializer".into(),
                            title: format!("affine-option local `{name}` needs an initializer"),
                            span: *name_span,
                            label: "initialize it with `none` or `some(alloc_array<bool>(...))`"
                                .into(),
                            notes: vec![],
                        });
                    }
                } else {
                    validate_aggregate_ty(ty.clone(), *name_span)?;
                }
                if *ty == Ty::array(Ty::Bool) && init.is_none() {
                    return Err(Diagnostic {
                        name: "type.bool_array_initializer".into(),
                        title: format!("Boolean array local `{name}` needs an initializer"),
                        span: *name_span,
                        label: "initialize it with a Boolean array literal or `alloc_array<bool>`"
                            .into(),
                        notes: vec![],
                    });
                }
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
                // Diagnose an attempted affine payload copy at the operation
                // that is actually illegal.  The owned-array provenance gate
                // below would otherwise mask `.value` before expression
                // checking gets a chance to explain that affine extraction
                // must use the atomic `.take` transition.
                let affine_value_copy = init.as_ref().is_some_and(|e| {
                    matches!(
                        &e.kind,
                        ExprKind::OptValue { operand }
                            if matches!(
                                &operand.kind,
                                ExprKind::Var(option)
                                    if ctx
                                        .vars
                                        .get(option.as_str())
                                        .is_some_and(|info| info.ty.is_affine_option())
                            )
                    )
                });
                if affine_value_copy {
                    let e = init.as_mut().expect("affine value copy has an initializer");
                    check_expr(ctx, e, Some(ty.clone()))?;
                    unreachable!("affine-option `.value` must be rejected")
                }
                // Where an owned array may come from. A call joins the
                // allocation and the literal because a verified callee hands
                // its owner over (ADR 0085) — which is what makes the result
                // storage this declaration may name, rather than a second
                // name for something the caller already holds.
                let owner_init = matches!(
                    init.as_ref().map(|e| &e.kind),
                    Some(ExprKind::AllocArray { .. })
                        | Some(ExprKind::ArrayLit(_))
                        | Some(ExprKind::OptTake { .. })
                        | Some(ExprKind::Call { .. })
                );
                if matches!(ty, Ty::Array(_)) && !ctx.in_test && !owner_init {
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
                    match (ty.clone(), &e.kind) {
                        // The owning family is routed away from the copy
                        // rules by the payload, and it is routed first: the
                        // arms below build a copyable value out of whatever
                        // the initializer evaluates to.
                        (option, _) if option.is_affine_option() => {
                            check_affine_option_initializer(ctx, e, &option)?;
                        }
                        (owned, ExprKind::OptTake { .. }) if owned.is_owned_array_of(&Ty::Bool) => {
                            check_affine_option_take(ctx, e)?;
                        }
                        (_, ExprKind::OptTake { .. }) => {
                            return Err(option_take_position(e.span));
                        }
                        _ => {
                            check_expr(ctx, e, Some(ty.clone()))?;
                        }
                    }
                    // A local initialized from branded storage is branded
                    // — but only if it *names* storage. A byte loaded out
                    // of raw memory is an ordinary number, and branding it
                    // would forbid returning the very thing the raw
                    // operations exist to produce.
                    branded = matches!(
                        ty,
                        Ty::Raw(_)
                            | Ty::RawRecord(_)
                            | Ty::OptionRaw(_)
                            | Ty::Record(_)
                            | Ty::Res(_)
                    ) && brand_of(ctx, e);
                    // `resource RawSpan t = s;` — a local-to-local move,
                    // the same rule classes follow (ADR 0020/0024). A
                    // declaration is not an escape: the new local inherits
                    // the brand rather than laundering it.
                    must_consume = transfer(ctx, e, None)?;
                }
                ctx.vars.insert(
                    name.clone(),
                    VarInfo {
                        ty: ty.clone(),
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
                reject_exposed_owner(ctx, name, *name_span)?;
                let (ty, was_mutable) = match ctx.vars.get(name.as_str()) {
                    Some(v) => (v.ty.clone(), v.mutable),
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
                if ty.is_affine_option() {
                    return Err(Diagnostic {
                        name: "option.affine_assign".into(),
                        title: format!("cannot assign a whole affine option to `{name}`"),
                        span: *name_span,
                        label: "construct the option once, inspect `.is_some`, and extract with `.take`"
                            .into(),
                        notes: vec![(
                            "note".into(),
                            "whole-option replacement needs an explicit rule for dropping the previous conditional owner".into(),
                        )],
                    });
                }
                let dest_branded = ctx.vars.get(name.as_str()).is_some_and(|v| v.branded);
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
                    if ty.as_array().is_some() {
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
                let then_ret = check_block(ctx, then_block, ret_ty.clone())?;
                let after_then = snapshot(ctx);
                let after_then_moved = ctx.moved.clone();
                restore(ctx, &before);
                ctx.moved = before_moved.clone();
                let else_ret = match else_block {
                    Some(b) => check_block(ctx, b, ret_ty.clone())?,
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
                    reaching_moved
                        .iter()
                        .flat_map(|s| s.iter().cloned())
                        .collect()
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
                // Snapshot the actual loop head before evaluating the
                // condition. Conditions are expressions, but they may still
                // move affine arguments or mutate ownership state through a
                // call. Those effects recur on every trip around the loop and
                // therefore belong to the backedge comparison.
                let head = snapshot(ctx);
                let head_moved = ctx.moved.clone();
                check_expr(ctx, cond, Some(Ty::Bool))?;

                // The body may run zero times, but the condition always runs
                // once. Preserve its flow state for the false/exit path while
                // checking condition + body against the pre-condition head.
                let after_cond = snapshot(ctx);
                let after_cond_moved = ctx.moved.clone();
                let _body_ret = check_block(ctx, body, ret_ty.clone())?;
                // Affine shape must be preserved at the backedge
                // (ADR 0024): a value consumed by the condition or body is
                // not there for the next condition evaluation, and a
                // resource created per iteration and never consumed leaks
                // one per turn. Views may change freely — that is what the
                // loop invariant is for; the *shape* is what must come back.
                // Only values live at the loop head are part of the
                // shape. One declared and consumed inside the body is
                // per-iteration scratch, not something the backedge owes.
                if let Some(p) = ctx.moved.symmetric_difference(&head_moved).find(|p| {
                    ctx.place_ty(p).as_ref().is_some_and(is_affine) && snapshot_has_place(&head, p)
                }) {
                    return Err(Diagnostic {
                        name: format!("{}.loop_shape", ctx.affine_kind(p)),
                        title: format!("the loop iteration consumes `{}`", p.render()),
                        span: *kw_span,
                        label: "the next condition evaluation would not have it".into(),
                        notes: vec![(
                            "note".into(),
                            "the condition and body together must leave the same values live at \
                             the backedge as at the head; an invariant carries what they are, \
                             not whether they are still there"
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
                for (name, was) in &head {
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
                            title: format!("the loop changes the must-consume state of `{name}`"),
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
                // The body may run zero times, but the condition does not:
                // continuation is its false path. Restore the post-condition
                // flow state, not the pre-condition head. Any condition/body
                // path that reaches a backedge with a different affine shape
                // was already rejected above.
                ctx.moved = after_cond_moved;
                restore(ctx, &after_cond);
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
                match (value, ret_ty.clone()) {
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
                        check_expr(ctx, e, Some(ret_ty.clone()))?;
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
                // An owned array always has a place. Discarding one would
                // leave an owner with no name and no lexical death, which is
                // the one thing every array's storage story depends on
                // (ADR 0085) — so a returned owner has to be bound, exactly
                // as a literal or an allocation does.
                if matches!(ty, Ty::Array(_)) {
                    return Err(Diagnostic {
                        name: "type.array_temporary".into(),
                        title: format!("discarding an owned `{}` temporary", ty.clone().name()),
                        span: e.span,
                        label: "bind it to an owned local".into(),
                        notes: vec![(
                            "note".into(),
                            "an owned array has no temporary form: it is named, or it is \
                             handed to something that names it"
                                .into(),
                        )],
                    });
                }
                if mandatory_ty(ty.clone()) {
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
                // Parser-produced inferred bindings start with no cached
                // type, but public/preconstructed ASTs may provide one.
                // Validate it before inference can overwrite it, otherwise
                // an affine aggregate could be relabelled as its scalar
                // initializer and bypass the explicit affine-option boundary.
                if let Some(cached) = ty {
                    if cached.is_affine_option() {
                        return Err(Diagnostic {
                            name: "option.affine_inferred".into(),
                            title: "an affine-option binding cannot be inferred".into(),
                            span: *name_span,
                            label: "write an explicit `mut option<...>` declaration".into(),
                            notes: vec![],
                        });
                    }
                    validate_aggregate_ty(cached.clone(), *name_span)?;
                }
                let some_of_class_local = matches!(
                    &init.kind,
                    ExprKind::SomeE(inner)
                        if matches!(
                            &inner.kind,
                            ExprKind::Var(v)
                                if matches!(
                                    ctx.vars.get(v.as_str()).map(|i| &i.ty),
                                    Some(Ty::Class(_))
                                )
                        )
                );
                if some_of_class_local
                    || matches!(
                        &init.kind,
                        ExprKind::SomeE(inner)
                            if matches!(
                                &inner.kind,
                                ExprKind::AllocArray { .. }
                                    | ExprKind::ArrayLit(_)
                                    | ExprKind::CtorCall { .. }
                            )
                    )
                {
                    return Err(Diagnostic {
                        name: "option.affine_inferred".into(),
                        title: "an affine-option binding cannot be inferred".into(),
                        span: *name_span,
                        label: "write an explicit `mut option<...>` declaration for an \
                                ownership-bearing option"
                            .into(),
                        notes: vec![(
                            "note".into(),
                            "the explicit ownership-bearing type keeps this binding out of the copy-option inference path".into(),
                        )],
                    });
                }
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
                    ExprKind::Var(src) => match ctx.vars.get(src.as_str()).map(|v| v.ty.clone()) {
                        Some(Ty::Class(ci)) => Some(ci),
                        _ => None,
                    },
                    ExprKind::SelfField { field } => {
                        match ctx
                            .vars
                            .get(format!("self.{field}").as_str())
                            .map(|v| v.ty.clone())
                        {
                            Some(Ty::Class(ci)) => Some(ci),
                            _ => None,
                        }
                    }
                    _ => None,
                };
                // `var t = o.take;` — atomic extraction of an owned class
                // payload into a fresh owner. The array family keeps its
                // typed-declaration route; a class local is var-introduced,
                // so its take is too.
                let take_class = match &init.kind {
                    ExprKind::OptTake { option, .. } => ctx
                        .vars
                        .get(option.as_str())
                        .and_then(|v| v.ty.as_affine_option_payload())
                        .and_then(|p| match p {
                            Ty::Class(ci) => Some(*ci),
                            _ => None,
                        }),
                    _ => None,
                };
                let t = if take_class.is_some() {
                    check_affine_option_take(ctx, init)?
                } else {
                    match moved_from {
                        Some(ci) => {
                            check_expr(ctx, init, Some(Ty::Class(ci)))?;
                            Ty::Class(ci)
                        }
                        None => check_expr(ctx, init, None)?,
                    }
                };
                local_ty(&t, init.span)?;
                // A declaration takes the value like any other sink, and
                // is not an escape: the new local inherits the brand
                // rather than laundering it — which only works if the
                // brand is actually computed here, exactly as a typed
                // declaration computes it.
                let branded = matches!(
                    t,
                    Ty::Raw(_) | Ty::RawRecord(_) | Ty::OptionRaw(_) | Ty::Record(_) | Ty::Res(_)
                ) && brand_of(ctx, init);
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
                *ty = Some(t.clone());
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
                let r = check_block(ctx, body, ret_ty.clone());
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
                    ctx.vars.insert(
                        name.to_string(),
                        VarInfo {
                            ty,
                            initialized: true,
                            mutable,
                            branded: false,
                            obligation: false,
                        },
                    );
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
                            ty: ty.clone(),
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
                ptr, res, release, ..
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
                // A nested exposure of an already-exposed array would open
                // a second loan on one buffer.
                reject_exposed_owner(ctx, array, *array_span)?;
                let (elem, src_mut, declared_mut) = match ctx.vars.get(array.as_str()) {
                    Some(v) => match &v.ty {
                        borrowed_or_owned if borrowed_or_owned.as_array().is_some() => {
                            let (element, mode) = borrowed_or_owned
                                .as_array()
                                .expect("the arm's guard already matched this shape");
                            (element, mode, v.mutable)
                        }
                        owning if owning.is_affine_option() => {
                            return Err(Diagnostic {
                                name: "option.affine_expose".into(),
                                title: format!("cannot expose affine option `{array}`"),
                                span: *array_span,
                                label: "extract the array with `.take` before opening an exposure"
                                    .into(),
                                notes: vec![(
                                    "note".into(),
                                    "an option may be `none`; exposure requires a concrete live array owner".into(),
                                )],
                            });
                        }
                        _ => {
                            return Err(Diagnostic {
                                name: "expose.not_an_array".into(),
                                title: format!("`{array}` is not an array"),
                                span: *array_span,
                                label: format!("this has type `{}`", v.ty.clone().name()),
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
                validate_array_payload(elem, *array_span)?;
                if *elem != Ty::Int(IntTy::U8) {
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
                    if src_mut == BindingMode::Shared {
                        return Err(Diagnostic {
                            name: "expose.mutate_shared".into(),
                            title: format!("cannot expose `{array}` mutably"),
                            span: *array_span,
                            label: "this array is a shared borrow".into(),
                            notes: vec![],
                        });
                    }
                    if src_mut == BindingMode::Owned && !declared_mut {
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
                // The owner's bytes are on loan for the body: freeze its
                // name, so the loan is the storage's only name until the
                // exit puts the bytes back.
                ctx.exposed
                    .insert(array.clone(), (ptr.clone(), res.clone()));
                // Raw operations are legal in an exposure body without a
                // nested `unsafe`: `unsafe expose` already said the word.
                let outer = ctx.in_unsafe;
                ctx.in_unsafe = true;
                ctx.unsafe_blocks += 1;
                let r = check_block(ctx, body, ret_ty.clone());
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
                // The loan ends with the body: the owner's name thaws.
                ctx.exposed.remove(array.as_str());
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
                // — Vec growth) or a fresh allocation. This path cannot use
                // ordinary array-expression checking, because a whole-array
                // read is legal only at this consuming boundary; it therefore
                // performs the moved-place check explicitly before stamping
                // the contextual owned type.
                let mut checked = false;
                if let Ty::Array(ref elem) = fty {
                    match &value.kind {
                        ExprKind::Var(name) => {
                            reject_exposed_owner(ctx, name, value.span)?;
                            let source = Place::local(name);
                            if ctx.is_moved(&source) {
                                return Err(moved_out(ctx, &source, value.span, "move"));
                            }
                            match ctx.vars.get(name.as_str()).map(|v| v.ty.clone()) {
                                Some(Ty::Array(e2)) if e2 == *elem => {
                                    value.ty = Some(Ty::Array(e2));
                                    checked = true;
                                }
                                _ => {
                                    return Err(Diagnostic {
                                        name: "type.field_array_move".into(),
                                        title: format!(
                                            "`{name}` cannot move into array field `{field}`"
                                        ),
                                        span: value.span,
                                        label: "needs an owned array of the same element type"
                                            .into(),
                                        notes: vec![],
                                    });
                                }
                            }
                        }
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
                let Ty::Array(elem) = fty else {
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
                validate_array_payload(&elem, *field_span)?;
                check_expr(ctx, value, Some(*elem))?;
            }
            Stmt::Store {
                array,
                array_span,
                index,
                value,
            } => {
                reject_exposed_owner(ctx, array, *array_span)?;
                let (elem, mutability, arr_mutable) = match ctx.vars.get(array.as_str()) {
                    Some(VarInfo { ty, mutable, .. }) if ty.as_array().is_some() => {
                        let (element, mode) = ty
                            .as_array()
                            .expect("the arm's guard already matched this shape");
                        (element.clone(), mode, *mutable)
                    }
                    Some(v) => {
                        return Err(Diagnostic {
                            name: "type.not_an_array".into(),
                            title: format!("`{array}` is not an array"),
                            span: *array_span,
                            label: format!("this has type `{}`", v.ty.clone().name()),
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
                if mutability == BindingMode::Owned && !arr_mutable {
                    return Err(Diagnostic {
                        name: "mut.store_immutable".into(),
                        title: format!("store into immutable local `{array}`"),
                        span: *array_span,
                        label: "declare it `mut` to allow element stores".into(),
                        notes: vec![],
                    });
                }
                if mutability == BindingMode::Shared {
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
                if !ctx
                    .vars
                    .get(array.as_str())
                    .is_some_and(|info| info.initialized)
                {
                    return Err(Diagnostic {
                        name: "type.uninitialized".into(),
                        title: format!("array `{array}` may be used before initialization"),
                        span: *array_span,
                        label: "not initialized on every path to this point".into(),
                        notes: vec![],
                    });
                }
                check_expr(ctx, index, Some(Ty::Int(IntTy::U64)))?;
                validate_array_payload(&elem, *array_span)?;
                check_expr(ctx, value, Some(elem))?;
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
        ExprKind::Var(name) => ctx.vars.get(name.as_str()).map(|v| v.ty.clone()),
        ExprKind::SelfField { field } => ctx
            .vars
            .get(format!("self.{field}").as_str())
            .map(|v| v.ty.clone()),
        ExprKind::Borrow { array, field, .. } => {
            let key = field
                .as_ref()
                .map_or_else(|| array.clone(), |f| format!("{array}.{f}"));
            ctx.vars.get(key.as_str()).map(|v| v.ty.clone())
        }
        _ => e.ty.clone(),
    }?;
    ty.res_kind()
}

fn noncanonical_aggregate_payload(span: Span) -> Diagnostic {
    Diagnostic {
        name: "type.aggregate_payload_noncanonical".into(),
        title: "legacy integer type-parameter storage is not valid in an aggregate".into(),
        span,
        label: "aggregate parameters must use the explicit declaration-parameter form".into(),
        notes: vec![],
    }
}

/// May a value of this type be an array element.
///
/// This is a *gate*, not a traversal: an allow-list ending in a named
/// refusal, which never calls itself — a gate that recursed would admit
/// arbitrary nesting. It answers yes or a named error and nothing else, so
/// there is exactly one entry point: an array holds a full `Ty`, and the type
/// of one element is the payload its holder already has.
///
/// It is load-bearing well beyond the shapes it names. Indexing and element
/// stores neither move the value nor re-brand it, and they are sound only
/// because every payload admitted here is copyable. Refusing every owning
/// payload by name is what keeps that true, and it is the real gate, not the
/// parser's admissibility table: `Place` is a root plus a field path with no
/// index component, so an owner living in an array element could not be
/// tracked at all.
///
/// It is deliberately independent of where the array occurs: position policy
/// below keeps Boolean arrays owned and local, while element checking can
/// preserve their exact `bool` identity.
pub(crate) fn validate_array_payload(payload: &Ty, span: Span) -> CResult<()> {
    match payload.payload_family() {
        PayloadFamily::Noncanonical => Err(noncanonical_aggregate_payload(span)),
        // A record element is stored, copied, and compared in place like an
        // integer: value semantics with a checked constructor behind it.
        PayloadFamily::Value | PayloadFamily::Record | PayloadFamily::Param => Ok(()),
        // An element is a place a store can name one of; an option element
        // would need per-element option storage no stage has. Arrays of
        // options stay closed while option nesting opens.
        PayloadFamily::OptionOfValue | PayloadFamily::Unsupported => Err(Diagnostic {
            name: "type.array_payload_unsupported".into(),
            title: format!(
                "array payload type `{}` is not supported yet",
                payload.name()
            ),
            span,
            label: "array operations currently support integers and `bool`".into(),
            notes: vec![(
                "note".into(),
                "an element is stored, copied, and compared in place, so a payload needs \
                     a layout, a copy rule, and — if it owns anything — a place path that can \
                     name one element"
                    .into(),
            )],
        }),
    }
}

/// May a value of this type be a copyable option payload, and if so, what is
/// the type of the present case.
///
/// A gate on the same terms as `validate_array_payload`, over the recursive
/// family: an option payload is a value or such an option itself, at any
/// depth. It answers with the present case's type rather than a bare
/// yes, because a caller needs that type. Copyable is the whole
/// rule — an option duplicates its payload whenever it is duplicated, so the
/// owning payloads are the separate `option<[T]>` and `option<raw<Record>>`
/// families. Retained declaration parameters keep the ADR 0009
/// abstract-integer semantics.
pub(crate) fn option_payload_ty(payload: Ty, span: Span) -> CResult<Ty> {
    match payload.payload_family() {
        PayloadFamily::Noncanonical => Err(noncanonical_aggregate_payload(span)),
        // The recursive family: an option nests wherever an option goes,
        // at any depth, because everything an option needs of its payload
        // (a Lean type, a junk default, a runtime value) an option has.
        PayloadFamily::Value | PayloadFamily::OptionOfValue | PayloadFamily::Param => Ok(payload),
        // A POD-record option needs its representation, proof, and runtime
        // semantics enabled together; the record family stays out here.
        PayloadFamily::Record | PayloadFamily::Unsupported => Err(Diagnostic {
            name: "type.option_payload_unsupported".into(),
            title: format!(
                "option payload type `{}` is not supported yet",
                payload.name()
            ),
            span,
            label: "value options hold integers, `bool`, or such options".into(),
            notes: vec![(
                "note".into(),
                "POD record options need their representation, proof, and runtime semantics \
                 enabled together"
                    .into(),
            )],
        }),
    }
}

/// Fallback fence for an ownership-bearing option that reaches a context with
/// no ownership rule. Source-facing boundaries use the more specific
/// diagnostics below; retaining this last gate keeps preconstructed ASTs from
/// falling into the ordinary copy-option implementation.
fn affine_option_unsupported(ty: Ty, span: Span) -> Diagnostic {
    Diagnostic {
        name: "type.affine_option_unsupported".into(),
        title: format!("affine option `{}` is not supported yet", ty.name()),
        span,
        label: "this context has no affine-option ownership rule".into(),
        notes: vec![(
            "note".into(),
            "an affine option is an explicit mutable local inspected with `.is_some` and emptied with atomic `.take`; it never uses the ordinary copy-option path"
                .into(),
        )],
    }
}

/// May an owning option carry this payload. A gate: an allow-list ending in a
/// named refusal, because each owned payload kind needs matching proof,
/// interpreter, formal-machine, and native destruction semantics.
pub(crate) fn affine_option_payload(payload: &Ty, span: Span) -> CResult<()> {
    if payload.is_owned_array_of(&Ty::Bool) || matches!(payload, Ty::Class(_)) {
        return Ok(());
    }
    Err(Diagnostic {
        name: "type.affine_option_payload".into(),
        title: format!(
            "affine option payload `{}` is not supported yet",
            payload.name()
        ),
        span,
        label: "the affine-option family owns `option<[bool]>` and `option<class>`".into(),
        notes: vec![(
            "note".into(),
            "each owned payload kind needs matching proof, interpreter, SVM, and native destruction semantics".into(),
        )],
    })
}

fn affine_option_boundary(ty: Ty, span: Span, boundary: &str) -> Diagnostic {
    let (name, title, label) = match boundary {
        "parameter" => (
            "type.affine_option_param",
            format!("affine option `{}` cannot be a parameter", ty.name()),
            "keep the owning option as an explicit local; call transport is deferred",
        ),
        "return" => (
            "type.affine_option_return",
            format!("affine option `{}` cannot be returned", ty.name()),
            "extract the owned array into a local; return transport is deferred",
        ),
        "field" => (
            "type.affine_option_field",
            format!("affine option `{}` cannot be stored in a field", ty.name()),
            "keep the owning option as a local; aggregate field storage is deferred",
        ),
        "trait" => (
            "type.affine_option_trait",
            format!("affine option `{}` cannot appear in a trait", ty.name()),
            "trait proof reuse does not model ownership-bearing options",
        ),
        "generic" => (
            "type.affine_option_generic",
            format!(
                "affine option `{}` cannot appear in a generic template",
                ty.name()
            ),
            "use the concrete owning-option local surface in a non-generic function",
        ),
        _ => unreachable!("known affine-option boundary"),
    };
    Diagnostic {
        name: name.into(),
        title,
        span,
        label: label.into(),
        notes: vec![(
            "note".into(),
            "an affine option has no ABI, field layout, or generic ownership substitution".into(),
        )],
    }
}

/// The payload rules for one type's own containers.
///
/// One-level dispatch, exhaustive with no wildcard on purpose: a wildcard
/// here is fail-open, because a shape nested under a constructor nobody
/// thought about would be admitted without any gate seeing it. A new
/// constructor must be a compile error, not a silent `Ok`. One level is
/// enough because the payload gate it hands off to answers from the
/// payload family, whose one recursive case (option nesting) classifies
/// the whole chain itself.
fn validate_container_payloads(ty: Ty, span: Span) -> CResult<()> {
    match ty {
        Ty::Array(payload) => validate_array_payload(&payload, span),
        Ty::Option(payload) => option_payload_ty(*payload, span).map(|_| ()),
        // A borrow holds no payload of its own; `validate_aggregate_ty` is
        // what strips the borrow marker before this runs.
        Ty::Borrow(..)
        | Ty::Int(_)
        | Ty::Bool
        | Ty::Param(_)
        | Ty::Class(_)
        | Ty::Record(_)
        | Ty::OptionRaw(_)
        | Ty::Res(_)
        | Ty::Raw(_)
        | Ty::RawRecord(_)
        | Ty::Unit => Ok(()),
    }
}

/// Check every container payload inside a type.
pub(crate) fn validate_aggregate_ty(ty: Ty, span: Span) -> CResult<()> {
    // An option that owns its present case is routed away from the copyable
    // gate before the dispatch below, and by the payload's shape rather than
    // by a constructor. Falling through would report the copyable family's
    // refusal for a shape the copyable rules never handle.
    if ty.is_affine_option() {
        return Err(affine_option_unsupported(ty, span));
    }
    // A borrow carries no payload of its own, so what this gates is the
    // referent's: `&[[u64]]` must meet the array payload rule exactly as
    // `[[u64]]` does. Whether a borrow may sit where it was written is a
    // position question, and `parameter_ty` asks it.
    validate_container_payloads(ty.referent().clone(), span)
}

/// May a record field hold this type, and if so with what storage geometry.
///
/// A gate: an allow-list ending in a named refusal. A record field is a raw
/// byte extent, so only a type that has chosen a width and a copy rule has a
/// field form; `Ty::storage_layout` is that allow-list.
pub(crate) fn record_field_layout(ty: &Ty, field: &str, span: Span) -> CResult<StorageLayout> {
    ty.storage_layout().ok_or_else(|| Diagnostic {
        name: "record.field_type".into(),
        title: format!("field `{field}` has non-raw-storable type `{}`", ty.name()),
        span,
        label: "records initially hold integers and nullable/non-null raw record pointers".into(),
        notes: vec![(
            "note".into(),
            "classes, resources, arrays, and nested records need separate ownership or layout \
             decisions"
                .into(),
        )],
    })
}

/// What a borrow may name.
///
/// A gate: an allow-list ending in a named refusal, and it never calls
/// itself — a borrow of a borrow names storage the callee was never handed.
/// Binding mode is orthogonal to shape in the representation, so this is the
/// rule that says which referents a `&` may be written on, and without it
/// every shape would be borrowable.
///
/// It carries the name `Parser::admits` uses at `TyPos::BorrowParam`, because
/// a reader asking "what may `&` be written on" should get one answer
/// whichever rule happened to answer it (ADR 0063).
fn borrow_referent_ty(borrowed: &Ty, referent: &Ty, span: Span) -> CResult<()> {
    match referent {
        // `&Nat` / `&mut Nat` (ADRs 0010, 0023), `&[T]` / `&mut [T]`
        // (ADR 0023), and `resource &K` / `resource &mut K` (ADR 0024).
        Ty::Class(_) | Ty::Array(_) | Ty::Res(_) => Ok(()),
        Ty::Int(_)
        | Ty::Bool
        | Ty::Param(_)
        | Ty::Record(_)
        | Ty::Option(_)
        | Ty::OptionRaw(_)
        | Ty::Raw(_)
        | Ty::RawRecord(_)
        | Ty::Borrow(..)
        | Ty::Unit => Err(Diagnostic {
            name: "type.borrow_param_unsupported".into(),
            title: format!("`{}` is not admitted as a parameter type", borrowed.name()),
            span,
            label: "expected `&C`/`&mut C`, `&[T]`/`&mut [T]`, or `resource &K`/`resource &mut K`"
                .into(),
            notes: vec![(
                "note".into(),
                "a borrow is a second name for storage the caller keeps; only arrays, classes, \
                 and resource authority have one"
                    .into(),
            )],
        }),
    }
}

/// May a parameter carry this type. A position gate: the payload traversal
/// decides what the type may contain, and these refusals decide what the call
/// boundary may transport, which is a separate question with a separate
/// answer for the same type.
/// The rule for a local binding's type.
///
/// A borrow is an argument form and a parameter binding mode; it is not a
/// local binding (ADR 0072). Every stage that reasons about borrowed storage
/// — the symbolic environment, the call-site and loop-head havoc, the `old`
/// snapshots, the ownership `Place`s — keys that storage by the *name* it
/// arrives under, and each such name is assumed to be the only one. A borrow
/// local is a second name for storage that already has one: the two entries
/// then carry independent state and both are believed, which is a false
/// contract with a proof behind it.
///
/// The rule is keyed on the binding mode, not on the referent, so it holds
/// for an array of any payload, a class, a class field, a resource, and any
/// reborrow of those. `Ty::binding_mode` is the whole test.
pub(crate) fn local_ty(ty: &Ty, span: Span) -> CResult<()> {
    if ty.binding_mode() == BindingMode::Owned {
        return Ok(());
    }
    Err(Diagnostic {
        name: "type.borrow_local_unsupported".into(),
        title: "a borrow cannot be bound to a local".into(),
        span,
        label: "this is a borrow, not a value".into(),
        notes: vec![(
            "note".into(),
            "write the borrow where it is used — `f(&mut a)` at the call — and read or \
             write the storage through the name that owns it, `a[i]` and `a.len`; the \
             compiler tracks storage by that one name (ADR 0072)"
                .into(),
        )],
    })
}

pub(crate) fn parameter_ty(ty: &Ty, span: Span) -> CResult<()> {
    if ty.is_affine_option() {
        return Err(affine_option_boundary(ty.clone(), span, "parameter"));
    }
    // Before the payload traversal: what a borrow may name is a question
    // about the borrow, and reporting an inner payload rule for `&record`
    // would name a rule the reader did not break.
    if let Some((_, referent)) = ty.as_borrow() {
        borrow_referent_ty(ty, referent, span)?;
    }
    validate_aggregate_ty(ty.clone(), span)?;
    // A copyable option with a concrete value payload crosses the call
    // boundary by value, exactly as it is returned. The type-parameter
    // payload stays out: a template option parameter would need the
    // abstract-payload call model that trait-bounded substitution does
    // not have, so it keeps the named refusal.
    if let Ty::Option(payload) = ty {
        if matches!(payload.as_ref(), Ty::Param(_)) {
            return Err(Diagnostic {
                name: "type.option_param".into(),
                title: "generic option-typed parameters are not supported yet".into(),
                span,
                label: "an `option` parameter takes a concrete integer or `bool` payload".into(),
                notes: vec![(
                    "note".into(),
                    "`option<u64>`-family and `option<bool>` parameters are supported; a \
                     template payload has no abstract option transport across a call"
                        .into(),
                )],
            });
        }
    }
    Ok(())
}

/// The declared type of a class `init` or method parameter.
///
/// Copyable values — integers, `bool`, and options with a concrete value
/// payload — cross the member boundary by value exactly as they cross a
/// function call. Class parameters: by value (moved in) or borrowed
/// (ADR 0020, ADR 0023), and resources — a class that owns authority takes
/// it in through an init (ADR 0029). Inits additionally take `&[T]` (the
/// bignum from_prefix shape: build a class value from computed limbs);
/// methods do not.
///
/// The option arm matches the owned `Ty::Option` directly — never through a
/// borrow-transparent accessor — so `&option<u64>` stays refused here, and
/// its payload test is `option_payload_ty`'s minus the type parameter: an
/// abstract payload has no member-call transport.
pub(crate) fn member_param_ty(ty: &Ty, span: Span, allow_shared_arrays: bool) -> CResult<()> {
    let value_option = match ty {
        Ty::Option(payload) => match payload.as_ref() {
            Ty::Int(IntTy::TParam(_)) => false,
            Ty::Int(_) | Ty::Bool => true,
            _ => false,
        },
        _ => false,
    };
    let ok = matches!(ty, Ty::Int(_) | Ty::Bool)
        || value_option
        || ty.class_index().is_some()
        || ty.is_resource()
        || (allow_shared_arrays && matches!(ty.as_array_borrow(), Some((_, Mutability::Shared))));
    if !ok {
        return Err(Diagnostic {
            name: "type.member_param".into(),
            title: "this type cannot be an init or method parameter yet".into(),
            span,
            label: format!("this has type `{}`", ty.clone().name()),
            notes: vec![(
                "note".into(),
                "init/method parameters take integers, `bool`, options of those, \
                 class values, and resources; an init additionally takes `&[T]`"
                    .into(),
            )],
        });
    }
    Ok(())
}

/// The declared return type of an ordinary function or class method.
pub(crate) fn return_ty(ty: &Ty, fn_name: &str, span: Span) -> CResult<()> {
    if ty.is_affine_option() {
        return Err(affine_option_boundary(ty.clone(), span, "return"));
    }
    validate_aggregate_ty(ty.clone(), span)?;
    // A returned borrow would name storage the callee's frame stops keeping,
    // which is the parser's `TyPos::Return` row and its name. Saying it here
    // too is not redundancy: an owned array is returnable (ADR 0085), so the
    // arm that used to refuse every array is gone, and a rule that reads
    // `Ty::Array` is not borrow-transparent — leaving the referent to decide
    // would make `&[T]` returnable the moment this function stopped looking.
    if ty.as_borrow().is_some() {
        return Err(Diagnostic {
            name: "type.return_unsupported".into(),
            title: format!("function `{fn_name}` returns a borrow"),
            span,
            label: format!("`{}` names storage it does not own", ty.clone().name()),
            notes: vec![(
                "note".into(),
                "a returned borrow would name storage that the callee's frame stops \
                 keeping at the return; return the owner instead"
                    .into(),
            )],
        });
    }
    Ok(())
}

/// The declared type of a class field.
pub(crate) fn class_field_ty(ty: &Ty, span: Span) -> CResult<()> {
    if ty.is_affine_option() {
        return Err(affine_option_boundary(ty.clone(), span, "field"));
    }
    validate_aggregate_ty(ty.clone(), span)?;
    // A copyable option with a concrete value payload is stored-field
    // state exactly as it is a parameter or a return. The type-parameter
    // payload stays out: mono instantiates template fields before this
    // gate runs, so this arm is the only fence between an abstract
    // option field and stages with no abstract-option field state.
    if let Ty::Option(payload) = ty {
        let concrete_value = match payload.as_ref() {
            Ty::Int(IntTy::TParam(_)) => false,
            Ty::Int(_) | Ty::Bool => true,
            _ => false,
        };
        if !concrete_value {
            return Err(Diagnostic {
                name: "type.option_field".into(),
                title: "an option field takes a concrete integer or `bool` payload".into(),
                span,
                label: format!("this has type `{}`", ty.clone().name()),
                notes: vec![(
                    "note".into(),
                    "`option<u64>`-family and `option<bool>` fields are supported; an \
                     abstract payload has no stored-field state"
                        .into(),
                )],
            });
        }
    }
    Ok(())
}

/// The declared type of a trait-method parameter.
///
/// An abstract trait call evaluates each argument as an integer proof
/// value, so a parameter whose value is not one has no meaning at the
/// call. An array is included in any binding mode: `&[T]` lifts to a
/// `Sable.Seq T`, which is exactly what the abstract call cannot pass.
/// A value option is included on the same terms: its proof value is
/// `Option Int` / `Option Bool`, not an integer.
pub(crate) fn trait_param_ty(ty: &Ty, span: Span) -> CResult<()> {
    if ty.is_affine_option() {
        return Err(affine_option_boundary(ty.clone(), span, "trait"));
    }
    parameter_ty(ty, span)?;
    if matches!(ty, Ty::Bool | Ty::Record(_) | Ty::Option(_)) || ty.as_array().is_some() {
        return Err(Diagnostic {
            name: "type.trait_param_unsupported".into(),
            title: "trait calls do not transport Boolean, POD-record, array, or option \
                    parameters"
                .into(),
            span,
            label: format!(
                "`{}` is not supported in a trait method parameter",
                ty.clone().name()
            ),
            notes: vec![(
                "note".into(),
                "ordinary functions may transport Boolean, POD-record, borrowed-array, and \
                 value-option arguments, but a retained trait call substitutes integer \
                 arguments into an abstract contract and has no model for these"
                    .into(),
            )],
        });
    }
    Ok(())
}

/// The declared result type of a trait method.
pub(crate) fn trait_return_ty(ty: &Ty, method_name: &str, span: Span) -> CResult<()> {
    if ty.is_affine_option() {
        return Err(affine_option_boundary(ty.clone(), span, "trait"));
    }
    return_ty(ty, method_name, span)?;
    if matches!(ty, Ty::Option(_)) {
        return Err(Diagnostic {
            name: "type.trait_option_return".into(),
            title: "trait methods may not return value options yet".into(),
            span,
            label: "trait calls retain the ADR 0009 integer proof domain".into(),
            notes: vec![(
                "note".into(),
                "ordinary functions and class methods may return `option<bool>`; trait \
                 proof reuse needs a separate widening decision"
                    .into(),
            )],
        });
    }
    // An array joins the list for the reason `type.trait_param_unsupported`
    // already gives about array parameters: an abstract trait call substitutes
    // integer arguments into the trait's contract, and a sequence is not one.
    if matches!(ty, Ty::Bool | Ty::Record(_)) || ty.as_array().is_some() {
        return Err(Diagnostic {
            name: "type.trait_return_unsupported".into(),
            title: "trait calls do not return Boolean, POD-record, or array values".into(),
            span,
            label: format!(
                "`{}` is not supported as a trait method result",
                ty.clone().name()
            ),
            notes: vec![(
                "note".into(),
                "ordinary functions may return Boolean, POD-record, and array values, but \
                 retained trait calls do not yet model those result kinds"
                    .into(),
            )],
        });
    }
    Ok(())
}

fn validate_declared_aggregate_payloads(program: &Program) -> CResult<()> {
    fn function(function: &Fn) -> CResult<()> {
        for parameter in &function.params {
            parameter_ty(&parameter.ty, parameter.span)?;
        }
        return_ty(&function.ret, &function.name, function.name_span)
    }

    fn trait_method(method: &Fn) -> CResult<()> {
        for parameter in &method.params {
            trait_param_ty(&parameter.ty, parameter.span)?;
        }
        trait_return_ty(&method.ret, &method.name, method.name_span)
    }

    fn class_method(method: &Fn) -> CResult<()> {
        function(method)?;
        // The same boundary the record refusal below names, for the same
        // reason: an ordinary function transports an owned array out
        // (ADR 0085), while a method call carries its own argument
        // reification and receiver-state machinery that no array has crossed.
        if method.ret.as_array().is_some() {
            return Err(Diagnostic {
                name: "type.member_array_return".into(),
                title: "class methods may not return arrays yet".into(),
                span: method.name_span,
                label: "return the array from an ordinary function".into(),
                notes: vec![(
                    "note".into(),
                    "method-call verification has separate receiver-state and result \
                     transport; its array-valued result boundary is not implemented yet"
                        .into(),
                )],
            });
        }
        if matches!(method.ret, Ty::Record(_)) {
            return Err(Diagnostic {
                name: "type.member_record_return".into(),
                title: "class methods may not return POD records yet".into(),
                span: method.name_span,
                label: "return the record from an ordinary function".into(),
                notes: vec![(
                    "note".into(),
                    "method-call verification has separate receiver-state and result transport; \
                     its record-valued result boundary is not implemented yet"
                        .into(),
                )],
            });
        }
        Ok(())
    }

    fn affine_decl(stmts: &[Stmt]) -> Option<(Ty, Span)> {
        for stmt in stmts {
            match stmt {
                Stmt::Decl { ty, name_span, .. } if ty.is_affine_option() => {
                    return Some((ty.clone(), *name_span));
                }
                Stmt::If {
                    then_block,
                    else_block,
                    ..
                } => {
                    if let Some(found) = affine_decl(then_block) {
                        return Some(found);
                    }
                    if let Some(found) = else_block.as_deref().and_then(affine_decl) {
                        return Some(found);
                    }
                }
                Stmt::While { body, .. } | Stmt::Unsafe { body, .. } => {
                    if let Some(found) = affine_decl(body) {
                        return Some(found);
                    }
                }
                Stmt::Expose { body, .. } => {
                    if let Some(found) = affine_decl(body) {
                        return Some(found);
                    }
                }
                _ => {}
            }
        }
        None
    }

    fn generic_function(function: &Fn) -> CResult<()> {
        if let Some(parameter) = function
            .params
            .iter()
            .find(|parameter| parameter.ty.is_affine_option())
        {
            return Err(affine_option_boundary(
                parameter.ty.clone(),
                parameter.span,
                "generic",
            ));
        }
        if function.ret.is_affine_option() {
            return Err(affine_option_boundary(
                function.ret.clone(),
                function.name_span,
                "generic",
            ));
        }
        if let Some((ty, span)) = affine_decl(&function.body) {
            return Err(affine_option_boundary(ty, span, "generic"));
        }
        Ok(())
    }

    // Retained templates go first: if mono has also emitted concrete
    // instances, the generic boundary remains the source-level reason for
    // rejection rather than whichever payload an instance happened to use.
    for function_ in &program.fn_templates {
        generic_function(function_)?;
        function(function_)?;
    }
    for function_ in &program.fns {
        function(function_)?;
    }
    for class in &program.class_templates {
        for initializer in &class.inits {
            generic_function(initializer)?;
        }
        for method in &class.methods {
            generic_function(&method.f)?;
        }
    }
    for class in program.class_templates.iter().chain(&program.classes) {
        for field in &class.fields {
            class_field_ty(&field.ty, field.span)?;
        }
        for initializer in &class.inits {
            function(initializer)?;
        }
        for method in &class.methods {
            class_method(&method.f)?;
        }
    }
    for record in &program.records {
        for field in &record.fields {
            if field.ty.is_affine_option() {
                return Err(affine_option_boundary(
                    field.ty.clone(),
                    field.span,
                    "field",
                ));
            }
            validate_aggregate_ty(field.ty.clone(), field.span)?;
        }
    }
    for trait_ in &program.traits {
        for method in &trait_.methods {
            trait_method(method)?;
        }
    }
    for implementation in &program.impls {
        for function_ in &implementation.fns {
            function(function_)?;
        }
    }
    Ok(())
}

/// Normalize the one legacy expression-only parameter representation used by
/// `widen<T>` / `narrow<T>` into the declaration-position type identity.
fn legacy_integer_ty(integer: IntTy) -> Ty {
    match integer {
        IntTy::TParam(index) => Ty::Param(TypeParamId::from_legacy(index)),
        concrete => Ty::Int(concrete),
    }
}

fn is_integer_ty(ty: Ty) -> bool {
    matches!(ty, Ty::Int(integer) if !matches!(integer, IntTy::TParam(_)))
        || matches!(ty, Ty::Param(_))
}

fn is_abstract_integer_ty(ty: Ty) -> bool {
    matches!(ty, Ty::Param(_))
}

fn option_take_position(span: Span) -> Diagnostic {
    Diagnostic {
        name: "option.take_position".into(),
        title: "`.take` is not in an owned-array initializer".into(),
        span,
        label: "use it directly as `[bool] values = option_name.take;`".into(),
        notes: vec![(
            "note".into(),
            "the restricted position makes the ownership destination explicit and gives the SVM one atomic source-to-destination transfer".into(),
        )],
    }
}

fn check_affine_option_initializer(
    ctx: &mut Ctx,
    expression: &mut Expr,
    option_ty: &Ty,
) -> CResult<Ty> {
    let payload = option_ty
        .as_affine_option_payload()
        .expect("affine-option initializer is dispatched on an owning option");
    affine_option_payload(payload, expression.span)?;
    let payload = payload.clone();
    match &mut expression.kind {
        ExprKind::NoneE => {}
        ExprKind::SomeE(inner)
            if matches!(&inner.kind, ExprKind::AllocArray { elem: Ty::Bool, .. }) =>
        {
            check_expr(ctx, inner, Some(Ty::array(Ty::Bool)))?;
        }
        // A class payload wraps an owned value: a fresh construction, or a
        // named local the wrap consumes (ADR 0030 — the move kills its
        // source). Both producers carry the class invariant, which is what
        // lets `.take` hand it back out.
        ExprKind::SomeE(inner)
            if matches!(payload, Ty::Class(_))
                && matches!(&inner.kind, ExprKind::CtorCall { .. } | ExprKind::Var(_)) =>
        {
            check_expr(ctx, inner, Some(payload.clone()))?;
            transfer(ctx, inner, None)?;
        }
        _ => {
            return Err(Diagnostic {
                name: "option.affine_initializer".into(),
                title: "unsupported affine-option initializer".into(),
                span: expression.span,
                label: "use `none`, `some(alloc_array<bool>(len, init))`, or `some(<class \
                        value>)`"
                    .into(),
                notes: vec![(
                    "note".into(),
                    "wrapping an array temporary or a compound expression is deferred until \
                     every ownership path has an atomic model"
                        .into(),
                )],
            });
        }
    }
    expression.ty = Some(option_ty.clone());
    Ok(option_ty.clone())
}

fn check_affine_option_local(
    ctx: &Ctx,
    option: &str,
    span: Span,
    operation: &str,
) -> CResult<(Ty, bool)> {
    let Some(info) = ctx.vars.get(option) else {
        return Err(Diagnostic {
            name: "type.unknown_variable".into(),
            title: format!("unknown variable `{option}`"),
            span,
            label: "not declared".into(),
            notes: vec![],
        });
    };
    let Some(payload) = info.ty.as_affine_option_payload() else {
        return Err(Diagnostic {
            name: "type.mismatch".into(),
            title: format!("`.{operation}` on `{}`", info.ty.clone().name()),
            span,
            label: "expected an owning-option local".into(),
            notes: vec![],
        });
    };
    affine_option_payload(payload, span)?;
    if !info.initialized {
        return Err(Diagnostic {
            name: "type.uninitialized".into(),
            title: format!("`{option}` may be read before initialization"),
            span,
            label: "not initialized on every path to this point".into(),
            notes: vec![],
        });
    }
    let place = Place::local(option);
    if ctx.is_moved(&place) {
        return Err(moved_out(ctx, &place, span, operation));
    }
    Ok((info.ty.clone(), info.mutable))
}

fn check_affine_option_take(ctx: &mut Ctx, expression: &mut Expr) -> CResult<Ty> {
    let ExprKind::OptTake {
        option,
        option_span,
    } = &expression.kind
    else {
        unreachable!("take checker called for non-take expression");
    };
    let (option_ty, mutable) = check_affine_option_local(ctx, option, *option_span, "take")?;
    if !mutable {
        return Err(Diagnostic {
            name: "mut.option_take_immutable".into(),
            title: format!("cannot take from immutable local `{option}`"),
            span: *option_span,
            label: "declare the affine option with `mut`".into(),
            notes: vec![(
                "note".into(),
                "`.take` leaves `none` in the source local and therefore mutates it".into(),
            )],
        });
    }
    // The result is the option's own payload: what was wrapped is what
    // comes out, and the destination check compares against exactly this.
    let ty = option_ty
        .as_affine_option_payload()
        .expect("checked: affine-option local")
        .clone();
    expression.ty = Some(ty.clone());
    Ok(ty)
}

fn check_expr(ctx: &mut Ctx, e: &mut Expr, expected: Option<Ty>) -> CResult<Ty> {
    // Every rule below this point may duplicate the value it produces, so an
    // option whose present case owns is refused here rather than reaching one
    // of them. The owning family has its own entry points
    // (`check_affine_option_initializer`, `check_affine_option_local`), which
    // is why this fence is not a hole in them.
    if let Some(ty) = expected.as_ref().filter(|ty| ty.is_affine_option()) {
        return Err(affine_option_unsupported(ty.clone(), e.span));
    }
    if let Some(ty) = e.ty.as_ref().filter(|ty| ty.is_affine_option()) {
        return Err(affine_option_unsupported(ty.clone(), e.span));
    }
    let ty = infer_expr(ctx, e, expected.clone())?;
    if let Some(exp) = expected {
        if ty != exp {
            return Err(Diagnostic {
                name: "type.mismatch".into(),
                title: format!(
                    "type mismatch: expected `{}`, found `{}`",
                    exp.name(),
                    ty.clone().name()
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
                Some(t) if is_integer_ty(t.clone()) => t,
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
            if let Ty::Int(integer) = t {
                if !matches!(integer, IntTy::TParam(_))
                    && (*n < integer.min() || *n > integer.max())
                {
                    return Err(Diagnostic {
                        name: "type.literal_out_of_range".into(),
                        title: format!("literal `{n}` does not fit in `{}`", integer.name()),
                        span,
                        label: format!(
                            "`{}` holds {}..={}",
                            integer.name(),
                            integer.min(),
                            integer.max()
                        ),
                        notes: vec![],
                    });
                }
            }
            t
        }
        ExprKind::BoolLit(_) => Ty::Bool,
        ExprKind::Var(name) => match ctx.vars.get(name.as_str()) {
            Some(v) => {
                reject_exposed_owner(ctx, name, span)?;
                if v.ty.is_affine_option() {
                    return Err(Diagnostic {
                        name: "option.affine_temporary".into(),
                        title: format!("affine option `{name}` used as an ordinary value"),
                        span,
                        label: "inspect `.is_some` or extract the owned payload with `.take`"
                            .into(),
                        notes: vec![(
                            "note".into(),
                            "affine options cannot be copied, passed, returned, or hidden inside a temporary expression".into(),
                        )],
                    });
                }
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
                        e.ty = Some(v.ty.clone());
                        return Ok(v.ty.clone());
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
                        e.ty = Some(v.ty.clone());
                        return Ok(v.ty.clone());
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
                if v.ty.as_array().is_some() {
                    // An owned array moves where a sink asks for exactly its
                    // type — out through `return`, into an owned parameter —
                    // the same escape a class value has, and for the same
                    // reason (ADR 0085): naming the array *is* handing it
                    // over, and `transfer` kills the source place. Every
                    // other read of a whole array stays refused, including
                    // through a borrow, which owns nothing to hand over.
                    let moves_here = matches!(&expected, Some(want) if *want == v.ty)
                        && matches!(v.ty, Ty::Array(_))
                        && v.initialized;
                    if moves_here {
                        e.ty = Some(v.ty.clone());
                        return Ok(v.ty.clone());
                    }
                    return Err(Diagnostic {
                        name: "type.array_value".into(),
                        title: format!("array `{name}` used as a value"),
                        span,
                        label: "arrays support only `a[i]` and `a.len` here".into(),
                        notes: vec![(
                            "note".into(),
                            "an owned array is a value where it is handed over — returned, \
                             or passed to an owned `[T]` parameter"
                                .into(),
                        )],
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
                v.ty.clone()
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
            validate_array_payload(&elem, *array_span)?;
            elem
        }
        ExprKind::Len { array } => {
            // `a.len` on a class receiver is the FIELD named `len`
            // (ADR 0010) — rewrite and re-check.
            if ctx
                .vars
                .get(array.as_str())
                .is_some_and(|v| v.ty.class_index().is_some())
            {
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
            let target_ty = legacy_integer_ty(*target);
            let src = match check_expr(ctx, arg, None) {
                Ok(ty) if is_integer_ty(ty.clone()) => ty,
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
                        check_expr(ctx, arg, Some(target_ty.clone()))?;
                        target_ty.clone()
                    } else {
                        return Err(d);
                    }
                }
            };
            if is_abstract_integer_ty(src.clone()) || is_abstract_integer_ty(target_ty.clone()) {
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
            let (Ty::Int(src), Ty::Int(target)) = (src, target_ty) else {
                unreachable!("abstract conversion types were rejected above")
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
                        "use `narrow<T>(e)` — any-to-any conversion under a range VC".into(),
                    )],
                });
            }
            Ty::Int(target)
        }
        ExprKind::Narrow { target, arg } => {
            // Any integer type to any integer type; the range fact is a
            // proof obligation (`narrow.range`), not a typing rule.
            let target_ty = legacy_integer_ty(*target);
            match check_expr(ctx, arg, None) {
                Ok(ty) if is_integer_ty(ty.clone()) => {}
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
                        check_expr(ctx, arg, Some(target_ty.clone()))?;
                    } else {
                        return Err(d);
                    }
                }
            }
            target_ty
        }
        ExprKind::IsSome { operand } => {
            let affine_name = match &operand.kind {
                ExprKind::Var(option)
                    if ctx
                        .vars
                        .get(option.as_str())
                        .is_some_and(|info| info.ty.is_affine_option()) =>
                {
                    Some(option.clone())
                }
                _ => None,
            };
            if let Some(option) = affine_name {
                let (option_ty, _) =
                    check_affine_option_local(ctx, &option, operand.span, "is_some")?;
                operand.ty = Some(option_ty);
            } else {
                match check_expr(ctx, operand, None)? {
                    Ty::Option(_) | Ty::OptionRaw(_) => {}
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
            }
            Ty::Bool
        }
        ExprKind::OptValue { operand } => {
            if let ExprKind::Var(option) = &operand.kind {
                if ctx
                    .vars
                    .get(option.as_str())
                    .is_some_and(|info| info.ty.is_affine_option())
                {
                    return Err(Diagnostic {
                        name: "option.affine_value".into(),
                        title: format!("cannot project the owned payload of `{option}`"),
                        span,
                        label: "use `.take` in an explicit owned `[bool]` declaration".into(),
                        notes: vec![(
                            "note".into(),
                            "`.value` is a non-consuming projection for copy options; applying it here would duplicate an array owner".into(),
                        )],
                    });
                }
            }
            match check_expr(ctx, operand, None)? {
                Ty::Option(payload) => option_payload_ty(*payload, span)?,
                Ty::OptionRaw(ri) => Ty::RawRecord(ri),
                other => {
                    return Err(Diagnostic {
                        name: "type.mismatch".into(),
                        title: format!("`.value` on `{}`", other.name()),
                        span,
                        label: "expected an `option<T>` value".into(),
                        notes: vec![],
                    });
                }
            }
        }
        ExprKind::OptTake { .. } => {
            return Err(option_take_position(span));
        }
        ExprKind::ClassField {
            obj,
            obj_span,
            field,
        } => {
            if matches!(
                ctx.vars.get(obj.as_str()).map(|v| v.ty.clone()),
                Some(Ty::Record(_))
            ) {
                let record_obj = obj.clone();
                let record_obj_span = *obj_span;
                let record_field = field.clone();
                e.kind = ExprKind::RecordField {
                    obj: record_obj,
                    obj_span: record_obj_span,
                    field: record_field,
                };
                return infer_expr(ctx, e, expected);
            }
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
                Ty::Param(parameter) => Ty::Param(*parameter),
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
                        title: format!("field `{field}` has type `{}`", other.clone().name()),
                        span,
                        label: "unsupported field read".into(),
                        notes: vec![],
                    });
                }
            }
        }
        ExprKind::RecordField {
            obj,
            obj_span,
            field,
        } => {
            let Some(info) = ctx.vars.get(obj.as_str()) else {
                return Err(Diagnostic {
                    name: "type.unknown_variable".into(),
                    title: format!("unknown variable `{obj}`"),
                    span: *obj_span,
                    label: "not declared".into(),
                    notes: vec![],
                });
            };
            if !info.initialized {
                return Err(Diagnostic {
                    name: "type.uninitialized".into(),
                    title: format!("`{obj}` may be read before initialization"),
                    span: *obj_span,
                    label: "record field read needs an initialized value".into(),
                    notes: vec![],
                });
            }
            let Ty::Record(ri) = info.ty else {
                return Err(Diagnostic {
                    name: "type.mismatch".into(),
                    title: format!("`{obj}` is not a record value"),
                    span: *obj_span,
                    label: "record field access".into(),
                    notes: vec![],
                });
            };
            let meta = &ctx.record_metas[ri];
            meta.fields
                .iter()
                .find(|(name, _)| name == field)
                .map(|(_, ty)| ty.clone())
                .ok_or_else(|| Diagnostic {
                    name: "type.unknown_field".into(),
                    title: format!("`{}` has no field `{field}`", meta.name),
                    span,
                    label: "unknown record field".into(),
                    notes: vec![],
                })?
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
                Some((_, Ty::Array(el))) => el.clone(),
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
            validate_array_payload(&elem, span)?;
            *elem
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
            // In the trait, `Self` is parameter 0; in this template, the
            // bounded parameter is `pidx`. Remap both direct and aggregate
            // payload positions without turning either into an `IntTy`.
            let remap = |t: Ty| -> Ty {
                let remap_payload = |payload: Ty| match payload {
                    Ty::Param(parameter) if parameter.index() == 0 => {
                        Ty::Param(TypeParamId::from_legacy(pidx))
                    }
                    Ty::Int(IntTy::TParam(0)) => Ty::Param(TypeParamId::from_legacy(pidx)),
                    other => other,
                };
                match t {
                    Ty::Param(parameter) if parameter.index() == 0 => {
                        Ty::Param(TypeParamId::from_legacy(pidx))
                    }
                    Ty::Int(IntTy::TParam(0)) => Ty::Param(TypeParamId::from_legacy(pidx)),
                    Ty::Array(payload) => Ty::array(remap_payload(*payload)),
                    Ty::Option(payload) => Ty::Option(Box::new(remap_payload(*payload))),
                    // A borrow's referent is remapped in place: `&[<T>]` is
                    // the same remap `[<T>]` gets, one marker further out.
                    Ty::Borrow(mutability, referent) => Ty::borrow(
                        mutability,
                        match *referent {
                            Ty::Array(payload) => Ty::array(remap_payload(*payload)),
                            other => other,
                        },
                    ),
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
            let want: Vec<Ty> = m.params.iter().map(|p| remap(p.ty.clone())).collect();
            for (a, w) in args.iter_mut().zip(&want) {
                check_expr(ctx, a, Some(w.clone()))?;
            }
            check_borrow_conflicts(ctx, args, None)?;
            remap(m.ret.clone())
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
            refuse_sealed_field_borrows(op.name(), args)?;
            let raw = Ty::Raw(IntTy::U8);
            let u8t = Ty::Int(IntTy::U8);
            let u64t = Ty::Int(IntTy::U64);
            let shared = Ty::borrow(Mutability::Shared, Ty::Res(ResKind::RawSpan));
            let unique = Ty::borrow(Mutability::Mut, Ty::Res(ResKind::RawSpan));
            let span = Ty::Res(ResKind::RawSpan);
            let cell = Ty::Res(ResKind::PointsToU64);
            let cell_shared = Ty::borrow(Mutability::Shared, Ty::Res(ResKind::PointsToU64));
            let cell_unique = Ty::borrow(Mutability::Mut, Ty::Res(ResKind::PointsToU64));
            let leased = Ty::Res(ResKind::BlockLease);
            let leased_cell = Ty::Res(ResKind::LeasedPointsToU64);
            let free_block = Ty::Res(ResKind::FreeBlock);
            let free_header = Ty::Res(ResKind::FreeHeader);
            let free_header_shared = Ty::borrow(Mutability::Shared, Ty::Res(ResKind::FreeHeader));
            let free_header_unique = Ty::borrow(Mutability::Mut, Ty::Res(ResKind::FreeHeader));
            let arg_kind = |i: usize| resource_arg_kind(ctx, &args[i]);
            let cell_kind = match op {
                RawOp::IntoCellU64 => arg_kind(1),
                RawOp::FromCellU64 => arg_kind(1),
                RawOp::CellInitU64 => arg_kind(2),
                RawOp::CellReadU64 | RawOp::CellTakeU64 | RawOp::CellDropU64 => arg_kind(1),
                RawOp::IntoCellRecord(_) => arg_kind(1),
                RawOp::FromCellRecord(_) => arg_kind(1),
                RawOp::CellInitRecord(_) => arg_kind(2),
                RawOp::CellReadRecord(_) | RawOp::CellTakeRecord(_) | RawOp::CellDropRecord(_) => {
                    arg_kind(1)
                }
                _ => None,
            };
            let leased_role = matches!(
                cell_kind,
                Some(ResKind::BlockLease | ResKind::LeasedPointsToU64)
            );
            let leased_cell_shared =
                Ty::borrow(Mutability::Shared, Ty::Res(ResKind::LeasedPointsToU64));
            let leased_cell_unique =
                Ty::borrow(Mutability::Mut, Ty::Res(ResKind::LeasedPointsToU64));
            let want: Vec<Ty> = match op {
                RawOp::Offset => vec![raw.clone(), u64t.clone()],
                RawOp::Load8 => vec![raw.clone(), shared],
                RawOp::Store8 => vec![raw.clone(), u8t.clone(), unique],
                RawOp::Copy => vec![raw.clone(), raw.clone(), u64t.clone(), shared, unique],
                RawOp::IntoCellU64 => vec![
                    raw.clone(),
                    if leased_role {
                        leased.clone()
                    } else {
                        span.clone()
                    },
                ],
                RawOp::FromCellU64 => vec![
                    raw.clone(),
                    if leased_role {
                        leased_cell.clone()
                    } else {
                        cell.clone()
                    },
                ],
                RawOp::CellInitU64 => vec![
                    raw.clone(),
                    u64t.clone(),
                    if leased_role {
                        leased_cell_unique
                    } else {
                        cell_unique
                    },
                ],
                RawOp::CellReadU64 => vec![
                    raw.clone(),
                    if leased_role {
                        leased_cell_shared
                    } else {
                        cell_shared
                    },
                ],
                RawOp::CellTakeU64 | RawOp::CellDropU64 => vec![
                    raw.clone(),
                    if leased_role {
                        leased_cell_unique
                    } else {
                        cell_unique
                    },
                ],
                RawOp::IntoCellRecord(ri) => vec![Ty::RawRecord(ri), Ty::Res(ResKind::RawSpan)],
                RawOp::FromCellRecord(ri) => {
                    vec![Ty::RawRecord(ri), Ty::Res(ResKind::PointsToRecord(ri))]
                }
                RawOp::CellInitRecord(ri) => vec![
                    Ty::RawRecord(ri),
                    Ty::Record(ri),
                    Ty::borrow(Mutability::Mut, Ty::Res(ResKind::PointsToRecord(ri))),
                ],
                RawOp::CellReadRecord(ri) => vec![
                    Ty::RawRecord(ri),
                    Ty::borrow(Mutability::Shared, Ty::Res(ResKind::PointsToRecord(ri))),
                ],
                RawOp::CellTakeRecord(ri) | RawOp::CellDropRecord(ri) => vec![
                    Ty::RawRecord(ri),
                    Ty::borrow(Mutability::Mut, Ty::Res(ResKind::PointsToRecord(ri))),
                ],
                RawOp::CastRecord(_) => vec![raw.clone()],
                RawOp::PointerOffsetRecord(ri) => vec![Ty::RawRecord(ri)],
                RawOp::IntoFreeHeader => vec![raw.clone(), free_block.clone()],
                RawOp::FromFreeHeader => vec![raw.clone(), free_header.clone()],
                RawOp::HeaderInit => {
                    vec![raw.clone(), u64t.clone(), u64t.clone(), free_header_unique]
                }
                RawOp::HeaderSize | RawOp::HeaderNext => vec![raw.clone(), free_header_shared],
                RawOp::HeaderClear => vec![raw.clone(), free_header_unique],
            };
            for (arg, w) in args.iter_mut().zip(&want) {
                require_explicit_borrow(ctx, arg, w.clone())?;
                check_expr(ctx, arg, Some(w.clone()))?;
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
                RawOp::IntoCellU64 => {
                    if leased_role {
                        leased_cell
                    } else {
                        cell
                    }
                }
                RawOp::FromCellU64 => {
                    if leased_role {
                        leased
                    } else {
                        span
                    }
                }
                RawOp::CellInitU64 | RawOp::CellDropU64 => Ty::Unit,
                RawOp::CellReadU64 | RawOp::CellTakeU64 => u64t,
                RawOp::IntoCellRecord(ri) => Ty::Res(ResKind::PointsToRecord(ri)),
                RawOp::FromCellRecord(_) => span,
                RawOp::CellInitRecord(_) | RawOp::CellDropRecord(_) => Ty::Unit,
                RawOp::CellReadRecord(ri) | RawOp::CellTakeRecord(ri) => Ty::Record(ri),
                RawOp::CastRecord(ri) => Ty::RawRecord(ri),
                RawOp::PointerOffsetRecord(_) => u64t,
                RawOp::IntoFreeHeader => free_header,
                RawOp::FromFreeHeader => free_block,
                RawOp::HeaderInit | RawOp::HeaderClear => Ty::Unit,
                RawOp::HeaderSize | RawOp::HeaderNext => u64t,
            }
        }
        ExprKind::DeviceOp { op, op_span, args } => {
            let op = *op;
            let op_span = *op_span;
            if !ctx.in_unsafe {
                return Err(Diagnostic {
                    name: "device.outside_unsafe".into(),
                    title: format!("`{}` may only be called inside `unsafe`", op.name()),
                    span: op_span,
                    label: "profile-mediated device access".into(),
                    notes: vec![(
                        "note".into(),
                        "the block is the audit boundary for externally observable device effects"
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
            refuse_sealed_field_borrows(op.name(), args)?;
            let uart = Ty::borrow(Mutability::Mut, Ty::Res(ResKind::Uart));
            let want = match op {
                DeviceOp::UartStatus => vec![uart],
                DeviceOp::UartWrite => vec![Ty::Int(IntTy::U8), uart],
            };
            for (arg, expected) in args.iter_mut().zip(want) {
                require_explicit_borrow(ctx, arg, expected.clone())?;
                check_expr(ctx, arg, Some(expected))?;
            }
            check_borrow_conflicts(ctx, args, None)?;
            match op {
                DeviceOp::UartStatus => Ty::Int(IntTy::U8),
                DeviceOp::UartWrite => Ty::Unit,
            }
        }
        ExprKind::ResOp { op, op_span, args } => {
            let op = *op;
            let op_span = *op_span;
            let arity = match op {
                ResOp::AllocatorStepHeader | ResOp::ResourceMapPut => 3,
                ResOp::SplitOff
                | ResOp::Join
                | ResOp::OpenFileOf
                | ResOp::AllocatorTake
                | ResOp::AllocatorPut
                | ResOp::AllocatorTakeFree
                | ResOp::AllocatorPutFree
                | ResOp::AllocatorTakeHeader
                | ResOp::AllocatorPutHeader
                | ResOp::FreeBlockSplit
                | ResOp::FreeBlockJoin
                | ResOp::ResourceMapTake => 2,
                ResOp::TestWorld
                | ResOp::TestUart
                | ResOp::AllocatorCreate
                | ResOp::AllocatorDestroy
                | ResOp::FreeBlockLease
                | ResOp::BlockLeaseFree => 1,
                ResOp::ResourceMapEmpty => 0,
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
            refuse_sealed_field_borrows(op.name(), args)?;
            match op {
                // `split_off(&mut whole, n)` — the prefix stays in the
                // borrowed token, the suffix leaves in the returned one.
                // No product type is needed: one side is written back
                // through the borrow (ADR 0024).
                ResOp::SplitOff => {
                    let want = Ty::borrow(Mutability::Mut, Ty::Res(ResKind::RawSpan));
                    require_explicit_borrow(ctx, &args[0], want.clone())?;
                    let got = check_expr(ctx, &mut args[0], Some(want.clone()))?;
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
                        check_expr(ctx, arg, Some(want.clone()))?;
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
                    let want = Ty::borrow(Mutability::Mut, Ty::Res(ResKind::PosixWorld));
                    require_explicit_borrow(ctx, &args[0], want.clone())?;
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
                ResOp::TestUart => {
                    if !ctx.in_test {
                        return Err(Diagnostic {
                            name: "uart.profile_outside_test".into(),
                            title: "`test_uart` exists only in tests".into(),
                            span: op_span,
                            label: "a program cannot select a scripted device profile".into(),
                            notes: vec![(
                                "note".into(),
                                "outside a test, UART authority arrives from the platform profile"
                                    .into(),
                            )],
                        });
                    }
                    check_expr(ctx, &mut args[0], Some(Ty::Int(IntTy::U64)))?;
                    Ty::Res(ResKind::Uart)
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
                    let want = Ty::borrow(Mutability::Mut, Ty::Res(ResKind::AllocatorState));
                    require_explicit_borrow(ctx, &args[0], want.clone())?;
                    check_expr(ctx, &mut args[0], Some(want))?;
                    check_expr(ctx, &mut args[1], Some(Ty::Int(IntTy::U64)))?;
                    check_borrow_conflicts(ctx, args, None)?;
                    Ty::Res(ResKind::BlockLease)
                }
                ResOp::AllocatorPut => {
                    let state = Ty::borrow(Mutability::Mut, Ty::Res(ResKind::AllocatorState));
                    require_explicit_borrow(ctx, &args[0], state.clone())?;
                    check_expr(ctx, &mut args[0], Some(state))?;
                    let lease = Ty::Res(ResKind::BlockLease);
                    check_expr(ctx, &mut args[1], Some(lease))?;
                    transfer(ctx, &args[1], None)?;
                    check_borrow_conflicts(ctx, args, None)?;
                    Ty::Unit
                }
                ResOp::AllocatorTakeFree => {
                    let want = Ty::borrow(Mutability::Mut, Ty::Res(ResKind::AllocatorState));
                    require_explicit_borrow(ctx, &args[0], want.clone())?;
                    check_expr(ctx, &mut args[0], Some(want))?;
                    check_expr(ctx, &mut args[1], Some(Ty::Int(IntTy::U64)))?;
                    check_borrow_conflicts(ctx, args, None)?;
                    Ty::Res(ResKind::FreeBlock)
                }
                ResOp::AllocatorPutFree => {
                    let state = Ty::borrow(Mutability::Mut, Ty::Res(ResKind::AllocatorState));
                    require_explicit_borrow(ctx, &args[0], state.clone())?;
                    check_expr(ctx, &mut args[0], Some(state))?;
                    let block = Ty::Res(ResKind::FreeBlock);
                    check_expr(ctx, &mut args[1], Some(block))?;
                    transfer(ctx, &args[1], None)?;
                    check_borrow_conflicts(ctx, args, None)?;
                    Ty::Unit
                }
                ResOp::AllocatorTakeHeader => {
                    let want = Ty::borrow(Mutability::Mut, Ty::Res(ResKind::AllocatorState));
                    require_explicit_borrow(ctx, &args[0], want.clone())?;
                    check_expr(ctx, &mut args[0], Some(want))?;
                    check_expr(ctx, &mut args[1], Some(Ty::Int(IntTy::U64)))?;
                    check_borrow_conflicts(ctx, args, None)?;
                    Ty::Res(ResKind::FreeHeader)
                }
                ResOp::AllocatorPutHeader => {
                    let state = Ty::borrow(Mutability::Mut, Ty::Res(ResKind::AllocatorState));
                    require_explicit_borrow(ctx, &args[0], state.clone())?;
                    check_expr(ctx, &mut args[0], Some(state))?;
                    let header = Ty::Res(ResKind::FreeHeader);
                    check_expr(ctx, &mut args[1], Some(header))?;
                    transfer(ctx, &args[1], None)?;
                    check_borrow_conflicts(ctx, args, None)?;
                    Ty::Unit
                }
                ResOp::AllocatorStepHeader => {
                    let want = Ty::borrow(Mutability::Mut, Ty::Res(ResKind::AllocatorState));
                    require_explicit_borrow(ctx, &args[0], want.clone())?;
                    check_expr(ctx, &mut args[0], Some(want))?;
                    check_expr(ctx, &mut args[1], Some(Ty::Int(IntTy::U64)))?;
                    check_expr(ctx, &mut args[2], Some(Ty::Int(IntTy::U64)))?;
                    check_borrow_conflicts(ctx, args, None)?;
                    Ty::Res(ResKind::FreeHeader)
                }
                ResOp::FreeBlockSplit => {
                    let block = Ty::borrow(Mutability::Mut, Ty::Res(ResKind::FreeBlock));
                    require_explicit_borrow(ctx, &args[0], block.clone())?;
                    check_expr(ctx, &mut args[0], Some(block))?;
                    check_expr(ctx, &mut args[1], Some(Ty::Int(IntTy::U64)))?;
                    check_borrow_conflicts(ctx, args, None)?;
                    Ty::Res(ResKind::FreeBlock)
                }
                ResOp::FreeBlockJoin => {
                    let block = Ty::Res(ResKind::FreeBlock);
                    for arg in args.iter_mut() {
                        check_expr(ctx, arg, Some(block.clone()))?;
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
                ResOp::ResourceMapEmpty => match expected {
                    Some(Ty::Res(kind @ ResKind::ResourceMapPointsToU64))
                    | Some(Ty::Res(kind @ ResKind::ResourceMapPointsToRecord(_))) => Ty::Res(kind),
                    _ => Ty::Res(ResKind::ResourceMapPointsToU64),
                },
                ResOp::ResourceMapTake => {
                    let Some(
                        map_kind @ (ResKind::ResourceMapPointsToU64
                        | ResKind::ResourceMapPointsToRecord(_)),
                    ) = resource_arg_kind(ctx, &args[0])
                    else {
                        return Err(Diagnostic {
                            name: "resource.map_type".into(),
                            title: "`resource_map_take` needs a supported resource map".into(),
                            span: args[0].span,
                            label: "expected a mutable ResourceMap borrow".into(),
                            notes: vec![],
                        });
                    };
                    let map = Ty::borrow(Mutability::Mut, Ty::Res(map_kind));
                    require_explicit_borrow(ctx, &args[0], map.clone())?;
                    check_expr(ctx, &mut args[0], Some(map))?;
                    check_expr(ctx, &mut args[1], Some(Ty::Int(IntTy::U64)))?;
                    check_borrow_conflicts(ctx, args, None)?;
                    Ty::Res(match map_kind {
                        ResKind::ResourceMapPointsToU64 => ResKind::PointsToU64,
                        ResKind::ResourceMapPointsToRecord(ri) => ResKind::PointsToRecord(ri),
                        _ => unreachable!(),
                    })
                }
                ResOp::ResourceMapPut => {
                    let Some(
                        map_kind @ (ResKind::ResourceMapPointsToU64
                        | ResKind::ResourceMapPointsToRecord(_)),
                    ) = resource_arg_kind(ctx, &args[0])
                    else {
                        return Err(Diagnostic {
                            name: "resource.map_type".into(),
                            title: "`resource_map_put` needs a supported resource map".into(),
                            span: args[0].span,
                            label: "expected a mutable ResourceMap borrow".into(),
                            notes: vec![],
                        });
                    };
                    let map = Ty::borrow(Mutability::Mut, Ty::Res(map_kind));
                    require_explicit_borrow(ctx, &args[0], map.clone())?;
                    check_expr(ctx, &mut args[0], Some(map))?;
                    check_expr(ctx, &mut args[1], Some(Ty::Int(IntTy::U64)))?;
                    let cell = Ty::Res(match map_kind {
                        ResKind::ResourceMapPointsToU64 => ResKind::PointsToU64,
                        ResKind::ResourceMapPointsToRecord(ri) => ResKind::PointsToRecord(ri),
                        _ => unreachable!(),
                    });
                    check_expr(ctx, &mut args[2], Some(cell))?;
                    transfer(ctx, &args[2], None)?;
                    check_borrow_conflicts(ctx, args, None)?;
                    Ty::Unit
                }
            }
        }
        ExprKind::AllocArray { elem, len, init } => {
            let elem = elem.clone();
            check_expr(ctx, len, Some(Ty::Int(IntTy::U64)))?;
            validate_array_payload(&elem, span)?;
            check_expr(ctx, init, Some(elem.clone()))?;
            Ty::Array(Box::new(elem))
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
            let Ty::Array(elem) = fty else {
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
            validate_array_payload(&elem, span)?;
            *elem
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
                match &p.ty {
                    borrowed_array if borrowed_array.as_array_borrow().is_some() => {
                        let (_, m) = borrowed_array
                            .as_array_borrow()
                            .expect("the arm's guard already matched this shape");
                        if !matches!(arg.kind, ExprKind::Borrow { .. }) {
                            return Err(Diagnostic {
                                name: "type.array_arg_borrow".into(),
                                title: "a borrowed array parameter takes an explicit borrow".into(),
                                span: arg.span,
                                label: format!(
                                    "write `{}name`",
                                    if m == Mutability::Mut { "&mut " } else { "&" }
                                ),
                                notes: vec![(
                                    "note".into(),
                                    "an argument's form follows the parameter's binding mode: \
                                     a borrow names the caller's storage, while an owned \
                                     `[T]` parameter takes the array itself"
                                        .into(),
                                )],
                            });
                        }
                        let got = check_expr(ctx, arg, None)?;
                        if got != *borrowed_array {
                            return Err(Diagnostic {
                                name: "type.mismatch".into(),
                                title: format!(
                                    "expected `{}`, found `{}`",
                                    borrowed_array.name(),
                                    got.name()
                                ),
                                span: arg.span,
                                label: "borrow with the required mutability".into(),
                                notes: vec![],
                            });
                        }
                    }
                    borrowed if borrowed.as_borrow().is_some() => {
                        require_explicit_borrow(ctx, arg, p.ty.clone())?;
                        check_expr(ctx, arg, Some(p.ty.clone()))?;
                    }
                    _ => {
                        check_expr(ctx, arg, Some(p.ty.clone()))?;
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
                Some(VarInfo { ty, .. }) if ty.as_class_borrow().is_some() => {
                    let (ci, m) = ty
                        .as_class_borrow()
                        .expect("the arm's guard already matched this shape");
                    (ci, m == Mutability::Mut, false)
                }
                Some(v) => {
                    return Err(Diagnostic {
                        name: "type.not_a_class".into(),
                        title: format!("`{recv}` is not a class value"),
                        span: *recv_span,
                        label: format!("this has type `{}`", v.ty.clone().name()),
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
                ref ty if ty.is_resource() => true,
                Ty::Raw(_) | Ty::RawRecord(_) | Ty::OptionRaw(_) => true,
                Ty::Class(ci) => class_holds_storage(ctx.class_metas, ci, 0),
                Ty::Record(ri) => record_holds_storage(ctx.record_metas, ri),
                _ => false,
            };
            for (arg, p) in args.iter_mut().zip(&params) {
                check_expr(ctx, arg, Some(p.ty.clone()))?;
                transfer(
                    ctx,
                    arg,
                    launders.then(|| ("be passed to a method", arg.span)),
                )?;
            }
            check_borrow_conflicts(
                ctx,
                args,
                Some((Place::local(recv), self_kind == SelfKind::Mut, *recv_span)),
            )?;
            ctx.calls
                .push(format!("{}::{method}", ctx.class_metas[ci].name));
            ret
        }
        ExprKind::ArrayLit(elems) => match expected {
            Some(Ty::Array(t)) => {
                validate_array_payload(&t, span)?;
                let element_ty = (*t).clone();
                for el in elems {
                    check_expr(ctx, el, Some(element_ty.clone()))?;
                }
                Ty::Array(t)
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
            reject_exposed_owner(ctx, array, span)?;
            if field.is_none()
                && ctx
                    .vars
                    .get(array.as_str())
                    .is_some_and(|info| info.ty.is_affine_option())
            {
                return Err(Diagnostic {
                    name: "option.affine_borrow".into(),
                    title: format!("cannot borrow affine option `{array}`"),
                    span,
                    label: "inspect `.is_some` or extract the array with `.take`".into(),
                    notes: vec![(
                        "note".into(),
                        "there is no borrowed option or conditional-array borrow representation"
                            .into(),
                    )],
                });
            }
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
                        Some((ci, _)) => Ty::borrow(Mutability::Shared, Ty::Class(ci)),
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
                    match ctx.vars.get(array.as_str()).map(|v| v.ty.clone()) {
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
                let Some(bci) = base.class_index() else {
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
                let borrowed_ty = match &fld.1 {
                    Ty::Class(fci) => Ok(Ty::borrow(Mutability::Shared, Ty::Class(*fci))),
                    // A resource field is a place too. Its mutability is
                    // the borrow's: shared anywhere, and unique only in a
                    // destructor, where the invariant it could break no
                    // longer has to hold (ADR 0029).
                    Ty::Res(k) => Ok(Ty::borrow(
                        if *mutable {
                            Mutability::Mut
                        } else {
                            Mutability::Shared
                        },
                        Ty::Res(*k),
                    )),
                    // An owned array field is a place too: `&x.limbs`
                    // borrows the array itself, shared.
                    Ty::Array(elem) => Ok(Ty::borrow(Mutability::Shared, Ty::Array(elem.clone()))),
                    _ => Err(Diagnostic {
                        name: "type.not_a_place".into(),
                        title: format!("field `{fname}` is not a borrowable place"),
                        span,
                        label: "only class- and array-valued fields are borrowed this way".into(),
                        notes: vec![],
                    }),
                }?;
                e.ty = Some(borrowed_ty.clone());
                return Ok(borrowed_ty);
            }
            // `&s` / `&mut s` of a resource local or parameter, or a
            // re-borrow of one passed along to a callee (ADR 0024). The
            // rules are the class rules: unique access is only ever
            // narrowed, and a mutable borrow needs a `mut` local.
            if let Some(v) = ctx.vars.get(array.as_str()) {
                if let Some(k) = v.ty.res_kind() {
                    let (src_mut, is_local) = match v.ty.as_res_borrow() {
                        Some((_, m)) => (m, false),
                        None => (Mutability::Mut, true),
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
                    let borrowed_ty = Ty::borrow(
                        if *mutable {
                            Mutability::Mut
                        } else {
                            Mutability::Shared
                        },
                        Ty::Res(k),
                    );
                    e.ty = Some(borrowed_ty.clone());
                    return Ok(borrowed_ty);
                }
            }
            // `&c` / `&mut c` of a class local, or a re-borrow of a class
            // parameter passed along to a callee (ADR 0010, ADR 0023).
            // A shared re-borrow of a `&mut C` is fine; the other
            // direction would manufacture unique access out of shared.
            if let Some(v) = ctx.vars.get(array.as_str()) {
                if let Some(ci) = v.ty.class_index() {
                    let (src_mut, is_local) = match v.ty.as_class_borrow() {
                        Some((_, m)) => (m, false),
                        None => (Mutability::Mut, true),
                    };
                    let declared_mut = v.mutable;
                    if *mutable {
                        if src_mut != Mutability::Mut {
                            return Err(Diagnostic {
                                name: "type.mut_borrow_shared".into(),
                                title: format!(
                                    "cannot mutably borrow `{array}` through `&{}`",
                                    ctx.class_metas[ci].name
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
                    let borrowed_ty = Ty::borrow(
                        if *mutable {
                            Mutability::Mut
                        } else {
                            Mutability::Shared
                        },
                        Ty::Class(ci),
                    );
                    e.ty = Some(borrowed_ty.clone());
                    return Ok(borrowed_ty);
                }
            }
            let elem = array_elem_ty(ctx, array, span)?;
            let src_mut = match ctx.vars.get(array.as_str()).map(|v| v.ty.clone()) {
                Some(ty) if ty.as_array().is_some() => ty.binding_mode(),
                _ => unreachable!("array_elem_ty checked"),
            };
            if *mutable
                && src_mut == BindingMode::Owned
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
            if *mutable && src_mut == BindingMode::Shared {
                return Err(Diagnostic {
                    name: "type.mut_borrow_shared".into(),
                    title: format!("cannot mutably borrow `{array}` through `&[_]`"),
                    span,
                    label: "a shared borrow cannot be reborrowed as `&mut`".into(),
                    notes: vec![],
                });
            }
            Ty::array_ref(
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
                check_expr(ctx, inner, Some(option_payload_ty((*t).clone(), span)?))?;
                Ty::Option(t)
            }
            Some(Ty::OptionRaw(ri)) => {
                check_expr(ctx, inner, Some(Ty::RawRecord(ri)))?;
                Ty::OptionRaw(ri)
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
            Some(Ty::OptionRaw(ri)) => Ty::OptionRaw(ri),
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
                    Ty::Int(_) | Ty::Param(_) => {
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
                ExprKind::Var(n) => match ctx.vars.get(n.as_str()).map(|v| v.ty.clone()) {
                    Some(ty) => ty.class_index().map(|ci| (n.clone(), ci)),
                    None => None,
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
                    Some(ref ty) if is_integer_ty(ty.clone()) => expected,
                    _ => None,
                };
                let t = infer_int_pair(ctx, lhs, rhs, expected_int, op_span)?;
                if matches!(op, BinOp::Div | BinOp::Rem) && is_abstract_integer_ty(t.clone()) {
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
                t
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
            let param_tys: Vec<Ty> = sig.params.iter().map(|p| p.ty.clone()).collect();
            let ret = sig.ret.clone();
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
                ref ty if ty.is_resource() => true,
                Ty::Raw(_) | Ty::RawRecord(_) | Ty::OptionRaw(_) => true,
                Ty::Class(ci) => class_holds_storage(ctx.class_metas, ci, 0),
                Ty::Record(ri) => record_holds_storage(ctx.record_metas, ri),
                _ => false,
            };
            for (arg, pty) in args.iter_mut().zip(param_tys) {
                let escapes = launders.then(|| ("be passed to a function", arg.span));
                match pty {
                    ref borrowed_array if borrowed_array.as_array_borrow().is_some() => {
                        let (_, m) = borrowed_array
                            .as_array_borrow()
                            .expect("the arm's guard already matched this shape");
                        if !matches!(arg.kind, ExprKind::Borrow { .. }) {
                            return Err(Diagnostic {
                                name: "type.array_arg_borrow".into(),
                                title: "a borrowed array parameter takes an explicit borrow".into(),
                                span: arg.span,
                                label: format!(
                                    "write `{}name`",
                                    if m == Mutability::Mut { "&mut " } else { "&" }
                                ),
                                notes: vec![(
                                    "note".into(),
                                    "an argument's form follows the parameter's binding mode: \
                                     a borrow names the caller's storage, while an owned \
                                     `[T]` parameter takes the array itself"
                                        .into(),
                                )],
                            });
                        }
                        let got = check_expr(ctx, arg, None)?;
                        if got != *borrowed_array {
                            return Err(Diagnostic {
                                name: "type.mismatch".into(),
                                title: format!(
                                    "expected `{}`, found `{}`",
                                    borrowed_array.name(),
                                    got.name()
                                ),
                                span: arg.span,
                                label: "borrow with the required mutability".into(),
                                notes: vec![],
                            });
                        }
                    }
                    ref borrowed if borrowed.as_borrow().is_some() => {
                        require_explicit_borrow(ctx, arg, pty.clone())?;
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
        ExprKind::RecordLit {
            record,
            record_span,
            args,
        } => {
            let Some(ri) = ctx.record_metas.iter().position(|r| r.name == *record) else {
                return Err(Diagnostic {
                    name: "record.unknown_type".into(),
                    title: format!("unknown record `{record}`"),
                    span: *record_span,
                    label: "not declared".into(),
                    notes: vec![],
                });
            };
            let meta = &ctx.record_metas[ri];
            if args.len() != meta.fields.len() {
                return Err(Diagnostic {
                    name: "record.arity".into(),
                    title: format!(
                        "record `{record}` has {} field(s), {} value(s) given",
                        meta.fields.len(),
                        args.len()
                    ),
                    span,
                    label: "values are supplied in field declaration order".into(),
                    notes: vec![],
                });
            }
            let field_tys: Vec<Ty> = meta.fields.iter().map(|(_, ty)| ty.clone()).collect();
            for (arg, field_ty) in args.iter_mut().zip(field_tys) {
                check_expr(ctx, arg, Some(field_ty))?;
            }
            Ty::Record(ri)
        }
    };
    e.ty = Some(ty.clone());
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
        // A borrowed class or resource parameter is itself a place that can
        // be re-borrowed. A borrowed array is not: its element storage is
        // named by an index, which `Place` has no path for.
        ExprKind::Var(n) => match ctx.vars.get(n.as_str()).map(|v| v.ty.clone()) {
            Some(ty) => match ty.as_borrow() {
                Some((m, Ty::Class(_) | Ty::Res(_))) => {
                    Some((Place::local(n), m == Mutability::Mut))
                }
                _ => None,
            },
            None => None,
        },
        _ => None,
    }
}

/// The place an argument hands over by moving, if it does.
///
/// An owned array reaches a parameter by name (ADR 0085), and the `Var` arm
/// of `check_expr` admits that spelling only where a sink asks for exactly
/// that array type — so a `Var` argument still carrying an owned array type
/// is a move, and `Place::local` is the storage it gives away.
fn moved_place(a: &Expr) -> Option<Place> {
    match (&a.kind, a.ty.as_ref()) {
        (ExprKind::Var(name), Some(Ty::Array(_))) => Some(Place::local(name)),
        _ => None,
    }
}

/// Within one call, a mutable borrow must not overlap any other borrow, and
/// a moved owner must not overlap any borrow at all.
///
/// VCgen havocs the mutable argument into a fresh symbol and keeps the
/// other arguments' pre-call symbols, so overlapping borrows would let
/// the caller assume a contract framed over storage the callee actually
/// changed — unsound, not merely imprecise. A move is the same hazard from
/// the other side: `f(&mut a, a)` hands the callee a borrow that promises
/// the caller keeps the storage *and* the storage itself, and the callee's
/// contract frames the two as separate sequences while one write reaches
/// both. Argument order is why this needs saying: a move after a borrow
/// leaves the borrow already recorded and nothing relating them, where a
/// borrow after a move meets `array.use_after_move`.
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
    for a in args {
        let Some(moved) = moved_place(a) else {
            continue;
        };
        if let Some((borrowed, _, _)) = borrows.iter().find(|(p, _, _)| p.overlaps(&moved)) {
            return Err(Diagnostic {
                name: "array.moved_while_borrowed".into(),
                title: format!(
                    "`{}` is both lent and handed over in one call",
                    moved.render()
                ),
                span: a.span,
                label: format!(
                    "this moves `{}`, which is borrowed by another argument",
                    moved.render()
                ),
                notes: vec![(
                    "note".into(),
                    format!(
                        "a borrow promises the caller keeps `{}` for the length of the \
                         call, and a move hands it to the callee: the contract would \
                         frame one storage as two separate values",
                        borrowed.render()
                    ),
                )],
            });
        }
    }
    Ok(())
}

/// A sealed raw/resource/device operation writes its fresh state back under
/// its borrow argument's ROOT name. A *field* borrow (`&mut self.mem` — the
/// destructor's field-borrow allowance, ADR 0029) has no root of its own:
/// threading the fresh view back into the owning object is a rule no sealed
/// operation states, and keying by the root would overwrite the whole object.
/// Refuse the shape by name, before any per-operation typing (ADR 0074).
fn refuse_sealed_field_borrows(op: &str, args: &[Expr]) -> CResult<()> {
    for arg in args {
        if let ExprKind::Borrow {
            array,
            field: Some(f),
            ..
        } = &arg.kind
        {
            return Err(Diagnostic {
                name: "resource.field_borrow_op".into(),
                title: format!("`{op}` cannot borrow the field `{array}.{f}`"),
                span: arg.span,
                label: "sealed operations take whole named resources".into(),
                notes: vec![(
                    "note".into(),
                    "move the field into a local resource binding first (a destructor \
                     may move fields out); a sealed operation's fresh state is written \
                     back under the borrow's root name, and a field has no root of its \
                     own"
                    .into(),
                )],
            });
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
    // Only a class or resource borrow names an owner a diagnostic can
    // print. An array borrow is written `&`/`&mut` at the call site by its
    // own rule, and a borrow of anything else is refused before this runs.
    let (m, owner, flipped) = match pty.as_borrow() {
        Some((m, Ty::Class(ci))) => (
            m,
            ctx.class_metas[*ci].name.clone(),
            Ty::borrow(flip(m), Ty::Class(*ci)),
        ),
        Some((m, Ty::Res(k))) => (m, k.name().to_string(), Ty::borrow(flip(m), Ty::Res(*k))),
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
            if ctx.vars.get(n.as_str()).map(|v| v.ty.clone()) == Some(pty.clone()) {
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
        Mutability::Shared => Mutability::Mut,
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
                .is_some_and(|v| is_affine(&v.ty))
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
                    .map(|(_, t)| t.clone())
            });
            if fty.as_ref().is_some_and(is_affine) {
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

/// Values that can be transferred but not duplicated.
///
/// The rule lives on the type (`Ty::is_affine`), so every checker entry that
/// asks gets the same answer, and so ownership is read off the shape rather
/// than off a list of constructors kept in step by hand.
fn is_affine(ty: &Ty) -> bool {
    ty.is_affine()
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
    let mut carries = e.ty.clone().is_some_and(mandatory_ty);
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
            .is_some_and(|v| mandatory_ty(v.ty.clone()));
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
            notes: vec![(
                "note".into(),
                if sealed_release {
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
                },
            )],
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
        self.vars.get(&p.state_key()).map(|v| v.ty.clone())
    }

    /// Whether this place names a resource.
    fn is_resource_place(&self, p: &Place) -> bool {
        self.place_ty(p).is_some_and(|t| t.is_resource())
    }

    /// Whether this place names an owned array, whose moves are affine for
    /// a different reason: the elements are shared storage, not authority.
    fn is_array_place(&self, p: &Place) -> bool {
        self.place_ty(p).is_some_and(|t| matches!(t, Ty::Array(_)))
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
            .map(|(_, t)| t.clone())
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
        ty if ty.is_resource() => true,
        Ty::Raw(_) | Ty::RawRecord(_) | Ty::OptionRaw(_) => true,
        Ty::Class(fci) => class_holds_storage(metas, *fci, depth + 1),
        // Records cannot currently be class fields, but treating one as a
        // storage container is the conservative answer if that surface grows.
        Ty::Record(_) => true,
        // Pure values: nothing here can carry storage out. Option payloads
        // that could (`option<raw<R>>`) are the `OptionRaw` constructor
        // above; a borrow is not a field type, but storage-conservative if
        // one ever appears.
        Ty::Int(_) | Ty::Bool | Ty::Param(_) | Ty::Array(_) | Ty::Option(_) | Ty::Unit => false,
        Ty::Res(_) | Ty::Borrow(..) => true,
    })
}

fn record_holds_storage(metas: &[RecordMeta], ri: usize) -> bool {
    metas[ri]
        .fields
        .iter()
        .any(|(_, ty)| matches!(ty, Ty::RawRecord(_) | Ty::OptionRaw(_)))
}

/// Whether an expression's value inherits a loan brand. Provenance is
/// what propagates: pointer arithmetic on branded storage, a split of a
/// branded span, a join involving one.
fn brand_of(ctx: &Ctx, e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Var(n) | ExprKind::Borrow { array: n, .. } => {
            ctx.vars.get(n.as_str()).is_some_and(|v| v.branded)
        }
        ExprKind::RawOp { args, .. }
        | ExprKind::ResOp { args, .. }
        | ExprKind::DeviceOp { args, .. } => args.iter().any(|a| brand_of(ctx, a)),
        ExprKind::SomeE(inner)
        | ExprKind::OptValue { operand: inner }
        | ExprKind::IsSome { operand: inner } => brand_of(ctx, inner),
        ExprKind::OptTake { .. } => false,
        ExprKind::RecordLit { args, .. } => args.iter().any(|a| brand_of(ctx, a)),
        ExprKind::RecordField { obj, .. } => ctx.vars.get(obj.as_str()).is_some_and(|v| v.branded),
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
            ctx.vars.get(n.as_str()).map(|v| v.ty.clone())
        }
        _ => e.ty.clone(),
    };
    if !ty.is_some_and(|t| {
        matches!(
            t,
            Ty::Raw(_) | Ty::RawRecord(_) | Ty::OptionRaw(_) | Ty::Record(_)
        ) || t.is_resource()
    }) {
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

/// While an exposure body is open, its owner has no readable or writable
/// spelling: the loan's pointer and resource are the storage's only names
/// there. A second live name would let a direct access and a raw one
/// disagree about one buffer, with both believed (ADR 0073).
fn reject_exposed_owner(ctx: &Ctx, name: &str, span: Span) -> CResult<()> {
    let Some((ptr, res)) = ctx.exposed.get(name) else {
        return Ok(());
    };
    Err(Diagnostic {
        name: "expose.owner_frozen".into(),
        title: format!("`{name}` is exposed; its bytes are on loan here"),
        span,
        label: format!("use the raw operations on `{ptr}` and `{res}` instead"),
        notes: vec![(
            "note".into(),
            format!(
                "inside the exposure body the loan is the buffer's only \
                 name; `{name}` gets its bytes back when the body ends. If \
                 the length is needed, bind `{name}.len` to a local before \
                 the exposure"
            ),
        )],
    })
}

/// A resource's *view* is ghost: clauses read `s.len`, program code does
/// not. That separation is what makes erasure real — a program able to
/// read the view would need it at runtime, and then the authority would
/// have a representation to forge (ADR 0024).
fn reject_view_read(ctx: &Ctx, name: &str, span: Span) -> CResult<()> {
    let Some(v) = ctx.vars.get(name) else {
        return Ok(());
    };
    let Some(k) = v.ty.res_kind() else {
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

fn array_elem_ty(ctx: &Ctx, array: &str, span: Span) -> CResult<Ty> {
    reject_view_read(ctx, array, span)?;
    reject_exposed_owner(ctx, array, span)?;
    let Some(v) = ctx.vars.get(array) else {
        return Err(Diagnostic {
            name: "type.unknown_variable".into(),
            title: format!("unknown variable `{array}`"),
            span,
            label: "not declared".into(),
            notes: vec![],
        });
    };
    // Owned or borrowed: indexing reads through either, and how the array is
    // bound is the store rule's question rather than this one's.
    let Some((element, _)) = v.ty.as_array() else {
        return Err(Diagnostic {
            name: "type.not_an_array".into(),
            title: format!("`{array}` is not an array"),
            span,
            label: format!("this has type `{}`", v.ty.clone().name()),
            notes: vec![],
        });
    };
    if !v.initialized {
        return Err(Diagnostic {
            name: "type.uninitialized".into(),
            title: format!("array `{array}` may be used before initialization"),
            span,
            label: "not initialized on every path to this point".into(),
            notes: vec![],
        });
    }
    let place = Place::local(array);
    if ctx.is_moved(&place) {
        return Err(moved_out(ctx, &place, span, "array access"));
    }
    validate_array_payload(element, span)?;
    Ok(element.clone())
}

/// Infer a same-typed integer pair, letting a literal side adopt the other
/// side's type (or the expected type when both need context).
fn infer_int_pair(
    ctx: &mut Ctx,
    lhs: &mut Expr,
    rhs: &mut Expr,
    expected: Option<Ty>,
    op_span: Span,
) -> CResult<Ty> {
    let lhs_literal = is_literal_only(lhs);
    let rhs_literal = is_literal_only(rhs);
    let t = if lhs_literal && !rhs_literal {
        let t = int_of(ctx, rhs, expected, op_span)?;
        check_expr(ctx, lhs, Some(t.clone()))?;
        t
    } else {
        let t = int_of(ctx, lhs, expected, op_span)?;
        check_expr(ctx, rhs, Some(t.clone()))?;
        t
    };
    Ok(t)
}

fn int_of(ctx: &mut Ctx, e: &mut Expr, expected: Option<Ty>, op_span: Span) -> CResult<Ty> {
    match check_expr(ctx, e, expected)? {
        ty if is_integer_ty(ty.clone()) => Ok(ty),
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

#[cfg(test)]
mod concrete_aggregate_tests {
    use super::*;
    use crate::span::LineMap;

    fn parse_program(source: &str) -> Program {
        let scanned = crate::scan::scan(source);
        let tokens = crate::lexer::lex(&scanned.program_text).expect("test source should lex");
        crate::parser::parse(
            &tokens,
            &scanned.blocks,
            &LineMap::new(source),
            &scanned.program_text,
        )
        .expect("test source should parse")
    }

    fn monomorphized_program(source: &str) -> Program {
        let mut program = parse_program(source);
        crate::mono::monomorphize(&mut program).expect("test source should monomorphize");
        program
    }

    fn check_error(program: &mut Program) -> Diagnostic {
        match check(program) {
            Err(error) => error,
            Ok(_) => panic!("test source unexpectedly typechecked"),
        }
    }

    fn affine_bool_option() -> Ty {
        Ty::affine_array_option(Ty::Bool)
    }

    /// The grammar can spell a container of anything; no stage can execute,
    /// prove, or lower most of it. These types cannot be written in a source
    /// program — `Parser::admits` refuses the spelling — so this feeds them
    /// to the checker directly. The representation can hold them, so the
    /// checker's own refusal is the boundary that has to hold.
    #[test]
    fn preconstructed_nested_payloads_are_refused_by_name() {
        let span = Span::new(0, 0);
        let cases: [(Ty, &str); 8] = [
            (
                Ty::array(Ty::array(Ty::Int(IntTy::U64))),
                "type.array_payload_unsupported",
            ),
            (
                Ty::array(Ty::array(Ty::Bool)),
                "type.array_payload_unsupported",
            ),
            (Ty::array(Ty::Class(0)), "type.array_payload_unsupported"),
            (
                Ty::array(Ty::option(Ty::Int(IntTy::U64))),
                "type.array_payload_unsupported",
            ),
            (
                Ty::array(Ty::affine_array_option(Ty::Bool)),
                "type.array_payload_unsupported",
            ),
            (
                Ty::array(Ty::Res(ResKind::RawSpan)),
                "type.array_payload_unsupported",
            ),
            (
                Ty::option(Ty::option(Ty::Class(0))),
                "type.option_payload_unsupported",
            ),
            (Ty::option(Ty::Class(0)), "type.affine_option_unsupported"),
        ];
        validate_aggregate_ty(Ty::option(Ty::option(Ty::Int(IntTy::U64))), span)
            .expect("the recursive copyable family nests at any depth");
        for (ty, expected) in cases {
            let refusal = validate_aggregate_ty(ty.clone(), span)
                .expect_err(&format!("`{}` must be refused by a named gate", ty.name()));
            assert_eq!(refusal.name, expected, "for `{}`", ty.name());
            assert_eq!(refusal.span, span);
        }
    }

    /// A borrow may name a class, an array, or resource authority, and
    /// nothing else.
    ///
    /// Binding mode is orthogonal to shape in the representation, so `&T`
    /// exists for every `T` and only a rule keeps the borrowable set small.
    /// `Parser::admits` states it at `TyPos::BorrowParam` for what a program
    /// can spell; this is the same rule at the checker's parameter position,
    /// under the same machine-matchable name, for a type that reached it
    /// some other way.
    #[test]
    fn a_borrow_of_an_unborrowable_referent_is_refused_by_name() {
        let span = Span::new(0, 0);
        for referent in [
            Ty::Int(IntTy::U64),
            Ty::Bool,
            Ty::Record(0),
            Ty::option(Ty::Int(IntTy::U64)),
            Ty::OptionRaw(0),
            Ty::Raw(IntTy::U8),
            Ty::RawRecord(0),
            Ty::Unit,
            Ty::array_ref(Ty::Int(IntTy::U64), Mutability::Shared),
        ] {
            for mutability in [Mutability::Shared, Mutability::Mut] {
                let borrowed = Ty::borrow(mutability, referent.clone());
                let refusal = parameter_ty(&borrowed, span)
                    .expect_err(&format!("`{}` must be refused by name", borrowed.name()));
                assert_eq!(
                    refusal.name,
                    "type.borrow_param_unsupported",
                    "for `{}`",
                    borrowed.name()
                );
            }
        }
        // The three referents a borrow may name stay admitted.
        for referent in [
            Ty::Class(0),
            Ty::array(Ty::Int(IntTy::U64)),
            Ty::Res(ResKind::RawSpan),
        ] {
            for mutability in [Mutability::Shared, Mutability::Mut] {
                let borrowed = Ty::borrow(mutability, referent.clone());
                parameter_ty(&borrowed, span)
                    .unwrap_or_else(|_| panic!("`{}` is a borrowable referent", borrowed.name()));
            }
        }
    }

    /// Every owning payload is refused by name, and that refusal — not the
    /// parser table — is what keeps indexing and element stores sound: they
    /// neither move the value nor re-brand it, and `Place` has no index
    /// component to track an owner living in an element.
    #[test]
    fn no_owning_array_payload_is_admitted() {
        let span = Span::new(0, 0);
        for owner in [
            Ty::Class(0),
            Ty::array(Ty::Bool),
            Ty::affine_array_option(Ty::Bool),
            Ty::Res(ResKind::RawSpan),
        ] {
            assert_eq!(
                validate_array_payload(&owner, span)
                    .expect_err("an owning payload is not an array element")
                    .name,
                "type.array_payload_unsupported",
                "for `{}`",
                owner.name()
            );
        }
    }

    #[test]
    fn affine_options_keep_closed_boundaries_and_forged_ast_fences() {
        let mut return_program = monomorphized_program("fn subject() {}");
        return_program.fns[0].ret = affine_bool_option();
        assert_eq!(
            check_error(&mut return_program).name,
            "type.affine_option_return"
        );

        let mut inferred_program = monomorphized_program("fn subject() {}");
        inferred_program.fns[0].body.push(Stmt::VarDecl {
            name: "forged".into(),
            name_span: Span::new(0, 0),
            mutable: false,
            init: Expr {
                kind: ExprKind::BoolLit(true),
                span: Span::new(0, 0),
                ty: Some(Ty::Bool),
            },
            ty: Some(affine_bool_option()),
        });
        assert_eq!(
            check_error(&mut inferred_program).name,
            "option.affine_inferred"
        );

        let mut expression_program = monomorphized_program("fn subject() {}");
        expression_program.fns[0].body.push(Stmt::ExprStmt(Expr {
            kind: ExprKind::IsSome {
                operand: Box::new(Expr {
                    kind: ExprKind::NoneE,
                    span: Span::new(0, 0),
                    ty: Some(affine_bool_option()),
                }),
            },
            span: Span::new(0, 0),
            ty: Some(Ty::Bool),
        }));
        assert_eq!(
            check_error(&mut expression_program).name,
            "type.affine_option_unsupported"
        );
    }

    #[test]
    fn affine_bool_options_support_local_construction_inspection_and_take() {
        let mut program = monomorphized_program(
            r#"
fn consume(u64 count) -> bool {
    mut option<[bool]> empty = none;
    mut option<[bool]> ready = some(alloc_array<bool>(count, false));
    bool present = ready.is_some;
    [bool] values = ready.take;
    bool absent_after_take = ready.is_some;
    return present && !absent_after_take && !empty.is_some;
}
"#,
        );
        check(&mut program).expect("the narrow affine-option local surface should typecheck");

        let function = &program.fns[0];
        let Stmt::Decl {
            init: Some(ready), ..
        } = &function.body[1]
        else {
            panic!("expected ready declaration");
        };
        assert_eq!(ready.ty, Some(affine_bool_option()));
        let ExprKind::SomeE(array) = &ready.kind else {
            panic!("expected some allocation");
        };
        assert_eq!(array.ty, Some(Ty::array(Ty::Bool)));

        let Stmt::Decl {
            init: Some(take), ..
        } = &function.body[3]
        else {
            panic!("expected take destination");
        };
        assert_eq!(take.ty, Some(Ty::array(Ty::Bool)));
        assert!(matches!(
            &take.kind,
            ExprKind::OptTake { option, .. } if option == "ready"
        ));
        let Stmt::Decl {
            init: Some(after_take),
            ..
        } = &function.body[4]
        else {
            panic!("expected the post-take presence inspection");
        };
        assert!(matches!(
            &after_take.kind,
            ExprKind::IsSome { operand }
                if matches!(&operand.kind, ExprKind::Var(option) if option == "ready")
        ));
    }

    #[test]
    fn affine_option_rejections_have_context_specific_diagnostics() {
        let cases = [
            (
                "fn bad() { option<[bool]> value = none; }",
                "mut.option_take_immutable",
            ),
            (
                "fn bad() { mut option<[u8]> value = none; }",
                "type.affine_option_payload",
            ),
            ("fn bad(option<[u8]> value) {}", "type.affine_option_param"),
            (
                "fn bad() -> option<[u8]> { return none; }",
                "type.affine_option_return",
            ),
            (
                "fn bad<T>() { mut option<[bool]> value = none; }",
                "type.affine_option_generic",
            ),
            (
                "fn bad() { mut option<[bool]> value = some([true]); }",
                "option.affine_initializer",
            ),
            (
                "fn bad() { [bool] a = [true]; mut option<[bool]> value = some(a); }",
                "option.affine_initializer",
            ),
            (
                "fn bad() { mut option<[bool]> value = none; [bool] a = value.value; }",
                "option.affine_value",
            ),
            (
                "fn bad() -> bool { mut option<[bool]> value = none; return value.take; }",
                "option.take_position",
            ),
            (
                "fn bad() { mut option<[bool]> value = none; value = none; }",
                "option.affine_assign",
            ),
            (
                "fn bad(u64 n) { var value = some(alloc_array<bool>(n, false)); }",
                "option.affine_inferred",
            ),
            (
                "fn bad() { mut option<[bool]> value = none; var borrowed = &value; }",
                "option.affine_borrow",
            ),
        ];
        for (source, expected) in cases {
            let mut program = monomorphized_program(source);
            assert_eq!(check_error(&mut program).name, expected, "{source}");
        }
    }

    #[test]
    fn bool_options_work_in_the_narrow_return_local_and_accessor_surface() {
        let mut program = monomorphized_program(
            r#"
fn choose(i32 value) -> option<bool> {
    if (value > 0) {
        return some(true);
    }
    return none;
}

fn forward(i32 value) -> option<bool> {
    option<bool> r = choose(value);
    return r;
}

fn consume(i32 value) -> bool {
    mut option<bool> r = choose(value);
    r = none;
    r = some(value > 0);
    if (r.is_some) {
        return r.value;
    }
    return false;
}
"#,
        );

        check(&mut program).expect("the complete narrow option<bool> surface should typecheck");
        assert_eq!(program.fns[0].ret, Ty::option(Ty::Bool));
        assert_eq!(program.fns[1].ret, Ty::option(Ty::Bool));

        let Stmt::If { then_block, .. } = &program.fns[2].body[3] else {
            panic!("expected the accessor guard");
        };
        let Stmt::Return {
            value: Some(value), ..
        } = &then_block[0]
        else {
            panic!("expected the guarded payload return");
        };
        assert_eq!(value.ty, Some(Ty::Bool));
    }

    #[test]
    fn bool_is_an_exact_array_and_option_payload_while_records_stay_closed() {
        assert_eq!(
            option_payload_ty(Ty::Bool, Span::new(0, 1)).unwrap(),
            Ty::Bool
        );
        assert!(validate_array_payload(&Ty::Bool, Span::new(0, 1)).is_ok());

        let option_record = option_payload_ty(Ty::Record(0), Span::new(0, 1)).unwrap_err();
        assert_eq!(option_record.name, "type.option_payload_unsupported");
        assert!(validate_array_payload(&Ty::Record(0), Span::new(0, 1)).is_ok());
    }

    #[test]
    fn inferred_class_moves_cache_the_source_expression_type() {
        let mut program = monomorphized_program(
            r#"
class Box {
    u64 value;

    init new(u64 value) {
        self.value = value;
    }
}

fn move_box() -> Box {
    var first = Box::new(7);
    var second = first;
    return second;
}
"#,
        );

        check(&mut program).expect("an inferred class move should typecheck");
        let Stmt::VarDecl { init, ty, .. } = &program.fns[0].body[1] else {
            panic!("expected the moved inferred declaration");
        };
        assert_eq!(*ty, Some(Ty::Class(0)));
        assert_eq!(init.ty, Some(Ty::Class(0)));
        let Stmt::Return {
            value: Some(value), ..
        } = &program.fns[0].body[2]
        else {
            panic!("expected the moved-local return");
        };
        assert_eq!(value.ty, Some(Ty::Class(0)));
    }

    #[test]
    fn owned_local_bool_arrays_cache_exact_types_for_literals_alloc_index_len_and_store() {
        let mut program = monomorphized_program(
            r#"
fn select(u64 index) -> bool {
    mut [bool] flags = [true, false];
    var mut copy = alloc_array<bool>(flags.len, false);
    copy[index] = flags[index];
    return copy[index];
}
"#,
        );
        check(&mut program).expect("the owned-local Boolean-array surface should typecheck");

        let function = &program.fns[0];
        let array_ty = Ty::array(Ty::Bool);
        let Stmt::Decl {
            ty,
            init: Some(literal),
            ..
        } = &function.body[0]
        else {
            panic!("expected the explicit array declaration");
        };
        assert_eq!(*ty, array_ty);
        assert_eq!(literal.ty, Some(array_ty.clone()));
        let ExprKind::ArrayLit(elements) = &literal.kind else {
            panic!("expected a contextual array literal");
        };
        assert!(elements.iter().all(|element| element.ty == Some(Ty::Bool)));

        let Stmt::VarDecl { init, ty, .. } = &function.body[1] else {
            panic!("expected the inferred allocation declaration");
        };
        assert_eq!(*ty, Some(array_ty.clone()));
        assert_eq!(init.ty, Some(array_ty));
        let ExprKind::AllocArray {
            elem,
            len,
            init: fill,
        } = &init.kind
        else {
            panic!("expected alloc_array<bool>");
        };
        assert_eq!(*elem, Ty::Bool);
        assert_eq!(len.ty, Some(Ty::Int(IntTy::U64)));
        assert_eq!(fill.ty, Some(Ty::Bool));

        let Stmt::Store { index, value, .. } = &function.body[2] else {
            panic!("expected a Boolean element store");
        };
        assert_eq!(index.ty, Some(Ty::Int(IntTy::U64)));
        assert_eq!(value.ty, Some(Ty::Bool));

        let Stmt::Return {
            value: Some(value), ..
        } = &function.body[3]
        else {
            panic!("expected an indexed Boolean return");
        };
        assert_eq!(value.ty, Some(Ty::Bool));
    }

    #[test]
    fn integer_array_field_move_cannot_reuse_the_moved_source() {
        let mut program = monomorphized_program(
            r#"
class Twin {
    [u64] left;
    [u64] right;

    /// post self.right.get 0 = 7
    init make() {
        [u64] values = alloc_array<u64>(1, 7);
        self.left = values;
        self.right = values;
        self.left[0] = 99;
    }
}
"#,
        );

        let error = check_error(&mut program);
        assert_eq!(error.name, "array.use_after_move");
    }

    /// A borrowed Boolean array is an ordinary parameter, and every boundary
    /// that still refuses it refuses `&[u64]` for the same reason — the rule
    /// is about the boundary, not about the payload.
    #[test]
    fn a_borrowed_bool_array_is_a_parameter_and_closed_boundaries_say_why() {
        let mut ordinary = monomorphized_program("fn ok(&[bool] values) {}\n");
        check(&mut ordinary).expect("a borrowed Boolean array is an ordinary parameter");

        let boundaries = [
            (
                r#"
class Holder {
    init new() {}

    fn bad(&self, &[bool] values) {}
}
"#,
                "type.member_param",
            ),
            (
                r#"
trait Bad {
    fn bad(Self value, &[bool] values);
}
"#,
                "type.trait_param_unsupported",
            ),
            (
                r#"
extern "C" #[audit(id := "test.bool-array.v1", reason := "boundary stays closed")]
fn bad(&[bool] values);
"#,
                "extern.param_abi",
            ),
        ];

        for (source, expected) in boundaries {
            let mut program = monomorphized_program(source);
            let error = check_error(&mut program);
            assert_eq!(error.name, expected);
        }

        // The trait rule is about the abstract call, not the payload: an
        // integer array has no substitution into a trait contract either.
        let mut integer_trait = monomorphized_program(
            r#"
trait Bad {
    fn bad(Self value, &[u64] values);
}
"#,
        );
        assert_eq!(
            check_error(&mut integer_trait).name,
            "type.trait_param_unsupported"
        );
    }

    #[test]
    fn bool_array_fields_and_exposure_stay_closed_while_returns_open() {
        let mut field = monomorphized_program(
            r#"
class Holder {
    [bool] flags;

    init new() {
        self.flags = alloc_array<bool>(1, false);
    }
}
"#,
        );
        check(&mut field).expect("a Boolean array is a class field like any admitted payload");

        let mut exposed = monomorphized_program(
            r#"
fn bad() {
    [bool] flags = [true];
    unsafe expose &flags as (ptr, resource bytes) {}
}
"#,
        );
        assert_eq!(check_error(&mut exposed).name, "expose.element_type");

        // A return is where an owner is handed over (ADR 0085); a class
        // method's result boundary is what stays closed.
        let mut returned = monomorphized_program(
            r#"
fn good() -> [bool] {
    [bool] flags = [true];
    return flags;
}
"#,
        );
        check(&mut returned).expect("an ordinary function hands its owned array over");

        let mut member = monomorphized_program(
            r#"
class Holder {
    u64 n;

    init new() {
        self.n = 1;
    }

    fn flags(&self) -> [bool] {
        return [true];
    }
}
"#,
        );
        assert_eq!(check_error(&mut member).name, "type.member_array_return");
    }

    #[test]
    fn synthetic_bool_array_positions_fail_closed() {
        let mut record = monomorphized_program(
            r#"
record Flag #[layout(size := 1, align := 1)] {
    #[offset(0)] u8 value;
}
"#,
        );
        record.records[0].fields[0].ty = Ty::array(Ty::Bool);
        assert_eq!(check_error(&mut record).name, "record.field_type");

        let mut uninitialized = monomorphized_program("fn test_bad() { [bool] flags = [true]; }\n");
        let Stmt::Decl { init, .. } = &mut uninitialized.fns[0].body[0] else {
            panic!("expected the explicit array local");
        };
        *init = None;
        assert_eq!(
            check_error(&mut uninitialized).name,
            "type.bool_array_initializer"
        );

        let mut discarded =
            monomorphized_program("fn bad() { [bool] flags = alloc_array<bool>(1, false); }\n");
        let Stmt::Decl {
            init: Some(allocation),
            ..
        } = discarded.fns[0].body.remove(0)
        else {
            panic!("expected the array allocation declaration");
        };
        discarded.fns[0].body.push(Stmt::ExprStmt(allocation));
        assert_eq!(check_error(&mut discarded).name, "type.array_temporary");
    }

    #[test]
    fn option_parameters_fields_and_trait_returns_stay_closed() {
        // Concrete value payloads cross the boundary; the type-parameter
        // payload keeps the named refusal.
        let mut admitted = monomorphized_program(
            "fn fine(option<bool> flag, option<u64> count) -> bool { return flag.is_some; }\n",
        );
        check(&mut admitted).expect("concrete value-option parameters are admitted");
        assert_eq!(
            parameter_ty(
                &Ty::option(Ty::Param(TypeParamId::from_legacy(0))),
                Span::new(0, 0)
            )
            .expect_err("a template option payload has no parameter transport")
            .name,
            "type.option_param"
        );

        let mut field = monomorphized_program(
            r#"
class Holder {
    option<bool> value;

    init new() {
        self.value = none;
    }
}
"#,
        );
        check(&mut field).expect("a concrete-payload option class field is admitted");
        assert_eq!(
            class_field_ty(
                &Ty::option(Ty::Param(TypeParamId::from_legacy(0))),
                Span::new(0, 0)
            )
            .expect_err("a template option payload has no stored-field state")
            .name,
            "type.option_field"
        );

        let mut trait_program = parse_program(
            r#"
trait Flag {
    fn flag(Self value) -> option<bool>;
}
"#,
        );
        let error = match check(&mut trait_program) {
            Err(error) => error,
            Ok(_) => panic!("trait option returns remain unsupported"),
        };
        assert_eq!(error.name, "type.trait_option_return");
    }

    #[test]
    fn visible_record_option_is_rejected_at_the_checker_boundary() {
        let mut program = monomorphized_program(
            r#"
record Pair #[layout(size := 1, align := 1)] {
    #[offset(0)] u8 value;
}

fn unsupported() -> option<Pair> {
    return none;
}
"#,
        );
        let error = match check(&mut program) {
            Err(error) => error,
            Ok(_) => panic!("POD option values remain unsupported"),
        };
        assert_eq!(error.name, "type.option_payload_unsupported");
    }

    #[test]
    fn ordinary_bool_call_arguments_use_normal_typechecking() {
        let mut program = monomorphized_program(
            r#"
fn echo(bool value) -> bool {
    return value;
}

fn nested(i32 value) -> bool {
    return echo(echo(!(value > 0)));
}
"#,
        );
        check(&mut program).expect("ordinary calls should accept checked Bool values");

        let Stmt::Return {
            value: Some(outer), ..
        } = &program.fns[1].body[0]
        else {
            panic!("expected the nested Bool call");
        };
        let ExprKind::Call { args, .. } = &outer.kind else {
            panic!("expected an outer call");
        };
        assert_eq!(args[0].ty, Some(Ty::Bool));
        assert_eq!(outer.ty, Some(Ty::Bool));

        let mut mismatch = monomorphized_program(
            r#"
fn consume(bool value) {}

fn bad() {
    consume(1);
}
"#,
        );
        let error = match check(&mut mismatch) {
            Ok(_) => panic!("non-Bool arguments still fail normally"),
            Err(error) => error,
        };
        assert_eq!(error.name, "type.mismatch");
    }

    #[test]
    fn record_method_returns_stay_outside_the_ordinary_call_slice() {
        let mut program = monomorphized_program(
            r#"
record Pair #[layout(size := 8, align := 8)] {
    #[offset(0)] u64 value;
}

class Holder {
    u64 value;

    init new() {
        self.value = 1;
    }

    fn pair(&self) -> Pair {
        return Pair(self.value);
    }
}
"#,
        );
        let error = match check(&mut program) {
            Ok(_) => panic!("method record returns remain unsupported"),
            Err(error) => error,
        };
        assert_eq!(error.name, "type.member_record_return");
    }

    #[test]
    fn bool_and_record_trait_calls_stay_in_the_integer_model() {
        let mut bool_parameter = parse_program(
            r#"
trait Select {
    fn select(Self value, bool choose) -> u64;
}
"#,
        );
        let error = match check(&mut bool_parameter) {
            Ok(_) => panic!("retained trait calls do not reify Boolean arguments"),
            Err(error) => error,
        };
        assert_eq!(error.name, "type.trait_param_unsupported");

        let mut bool_result = parse_program(
            r#"
trait Predicate {
    fn test(Self value) -> bool;
}
"#,
        );
        let error = match check(&mut bool_result) {
            Ok(_) => panic!("retained trait calls do not return propositions"),
            Err(error) => error,
        };
        assert_eq!(error.name, "type.trait_return_unsupported");

        let mut record_result = parse_program(
            r#"
record Pair #[layout(size := 8, align := 8)] {
    #[offset(0)] u64 value;
}

trait Factory {
    fn make(Self value) -> Pair;
}
"#,
        );
        let error = match check(&mut record_result) {
            Ok(_) => panic!("retained trait calls do not return POD records"),
            Err(error) => error,
        };
        assert_eq!(error.name, "type.trait_return_unsupported");
    }
}
