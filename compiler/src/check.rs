//! Typechecking: exact-width integer types with no
//! implicit conversions (only explicit `widen`), array/option restrictions,
//! definite initialization, all-paths-return, loop variants required, and
//! recursion allowed only for self-calls with a declared measure.
//!
//! The checker writes types into the AST (`Expr::ty`) for the VC generator.

#![deny(clippy::wildcard_enum_match_arm)]

use crate::ast::*;
use crate::control::{
    BlockId, ControlOutline, ControlOutlines, ControlProgram, SlotActionKind, StatementPlanKind,
};
use crate::diag::Diagnostic;
use crate::ownership::{
    CheckedExposure, CheckedLoopEffects, CheckedMutation, CheckedOptionTake, CheckedOwnershipPlan,
    CheckedSealedArgument, CheckedSealedOperation, CheckedSealedTarget, CheckedSlotMutationKind,
    CheckedSlotTransition, CheckedSlotTransitionKind, EffectSiteKey, ValueTransfer,
    ValueTransferKey, ValueTransferKind, ValueTransferSink,
};
use crate::place::{BorrowedPlace, Place};
use crate::span::Span;
use crate::transition::{
    CallArgumentEffect, CallArgumentTransition, CallOwner, CallReceiverTransition, CallSiteKey,
    CallTarget, CallTransition, CheckedCallTransition,
};
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
    /// Checker-sealed lexical control plans for this exact typed AST.
    pub(crate) control: ControlProgram,
    /// Ephemeral, typed ownership and mutation facts read by VC generation
    /// for this exact checked AST. They are never serialized into module
    /// artifacts.
    pub(crate) ownership: CheckedOwnershipPlan,
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
    /// Semantic callable identity used by the checker-to-VC call handoff.
    /// This stays separate from `current_fn`, whose display spelling is also
    /// used by call-graph and diagnostic code.
    call_owner: CallOwner,
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
    /// Non-self callees (for mutual-recursion detection), with callable
    /// flavor retained so same-spelled member categories stay distinct.
    calls: Vec<CallOwner>,
    /// Checker-authored unique-borrow effects for free, constructor, and
    /// method calls. Every admitted call gets a record, including an empty
    /// one, so VC generation can distinguish "no effect" from "not checked".
    ownership: &'a mut CheckedOwnershipPlan,
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
    let class = ctx
        .vars
        .get(name)
        .and_then(|v| v.ty.class_index())
        .ok_or_else(|| Diagnostic {
            name: "type.mismatch".into(),
            title: format!("`{name}` is not a class value"),
            span,
            label: "field access needs a class-typed receiver".into(),
            notes: vec![],
        })?;
    let receiver = Place::local(name);
    if ctx.is_moved(&receiver) {
        return Err(moved_out(ctx, &receiver, span, "field receiver"));
    }
    Ok(class)
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
            other @ (Ty::Int(_)
            | Ty::Bool
            | Ty::Param(_)
            | Ty::Record(_)
            | Ty::Array(_)
            | Ty::Slots(_)
            | Ty::Option(_)
            | Ty::OptionRaw(_)
            | Ty::Res(_)
            | Ty::Raw(_)
            | Ty::RawRecord(_)
            | Ty::Borrow(..)
            | Ty::Unit) => format!("`{}`", other.name()),
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
        let ok = extern_parameter_abi_allowed(&p.ty);
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

/// The exact foreign-parameter whitelist, including borrowed resource views.
///
/// Keeping both axes exhaustive is important: the ABI has historically
/// admitted `resource &RawSpan` / `resource &mut RawSpan` as erased authority
/// paired with a raw pointer. A match only on the outer `Ty` silently drops
/// those established borrow forms, while a wildcard would let a future type
/// or resource kind inherit an ABI decision accidentally.
fn extern_parameter_abi_allowed(ty: &Ty) -> bool {
    fn resource(kind: ResKind) -> bool {
        match kind {
            ResKind::RawSpan | ResKind::OpenFile | ResKind::PosixWorld => true,
            ResKind::PointsToU64
            | ResKind::PointsToRecord(_)
            | ResKind::Uart
            | ResKind::SystemDealloc
            | ResKind::AllocatorState
            | ResKind::BlockLease
            | ResKind::LeasedPointsToU64
            | ResKind::FreeBlock
            | ResKind::FreeHeader
            | ResKind::ResourceMapPointsToU64
            | ResKind::ResourceMapPointsToRecord(_) => false,
        }
    }

    fn borrowed_referent(referent: &Ty) -> bool {
        match referent {
            Ty::Res(kind) => resource(*kind),
            Ty::Int(_)
            | Ty::Bool
            | Ty::Param(_)
            | Ty::Class(_)
            | Ty::Record(_)
            | Ty::Array(_)
            | Ty::Slots(_)
            | Ty::Option(_)
            | Ty::OptionRaw(_)
            | Ty::Raw(_)
            | Ty::RawRecord(_)
            | Ty::Borrow(..)
            | Ty::Unit => false,
        }
    }

    match ty {
        Ty::Int(_) | Ty::Raw(_) | Ty::RawRecord(_) => true,
        Ty::Res(kind) => resource(*kind),
        Ty::Borrow(Mutability::Shared, referent) | Ty::Borrow(Mutability::Mut, referent) => {
            borrowed_referent(referent)
        }
        Ty::Bool
        | Ty::Param(_)
        | Ty::Class(_)
        | Ty::Record(_)
        | Ty::Array(_)
        | Ty::Slots(_)
        | Ty::Option(_)
        | Ty::OptionRaw(_)
        | Ty::Unit => false,
    }
}

pub fn check(program: &mut Program) -> CResult<CheckResult> {
    // Keep the profile-specific singleton-capability diagnosis ahead of the
    // general integer-only trait-signature gate below.
    check_uart_trait_methods(&program.traits)?;
    validate_declared_aggregate_payloads(program)?;
    let mut unsafe_regions = 0usize;
    let mut ownership = CheckedOwnershipPlan::default();
    let mut control_outlines = ControlOutlines::default();
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

    // Class signatures + validation. Initializers and methods occupy distinct
    // callable flavors, so one of each may share a spelling; duplicates within
    // either flavor would make lookup and semantic owner identities ambiguous.
    let validate_member_names = |class: &ClassDecl| -> CResult<()> {
        let mut inits = HashSet::new();
        for init in &class.inits {
            if !inits.insert(init.name.clone()) {
                return Err(Diagnostic {
                    name: "type.duplicate_init".into(),
                    title: format!(
                        "class `{}` defines initializer `{}` twice",
                        class.name, init.name
                    ),
                    span: init.name_span,
                    label: "second initializer with this name".into(),
                    notes: vec![(
                        "note".into(),
                        "an initializer and a method may share a name; two initializers may not"
                            .into(),
                    )],
                });
            }
        }
        let mut methods = HashSet::new();
        for method in &class.methods {
            if !methods.insert(method.f.name.clone()) {
                return Err(Diagnostic {
                    name: "type.duplicate_method".into(),
                    title: format!(
                        "class `{}` defines method `{}` twice",
                        class.name, method.f.name
                    ),
                    span: method.f.name_span,
                    label: "second method with this name".into(),
                    notes: vec![(
                        "note".into(),
                        "an initializer and a method may share a name; two methods may not".into(),
                    )],
                });
            }
        }
        Ok(())
    };

    // Class signatures + validation.
    let mut class_metas: Vec<ClassMeta> = Vec::new();
    {
        let mut seen = HashSet::new();
        for c in &program.classes {
            validate_member_names(c)?;
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

    let mut call_graph: HashMap<CallOwner, Vec<CallOwner>> = HashMap::new();
    let mut callable_spans: HashMap<CallOwner, Span> = HashMap::new();
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
        if sig.params.len() != 2 {
            return Err(bad_sig("operators bind functions of shape `fn (&C, &C)`"));
        }
        let Some(a) = sig.params.first() else {
            return Err(bad_sig("operators bind functions of shape `fn (&C, &C)`"));
        };
        let Some(b) = sig.params.get(1) else {
            return Err(bad_sig("operators bind functions of shape `fn (&C, &C)`"));
        };
        let (Some((ci_a, Mutability::Shared)), Some((ci_b, Mutability::Shared))) =
            (checked_class_borrow(&a.ty), checked_class_borrow(&b.ty))
        else {
            return Err(bad_sig("operators bind functions of shape `fn (&C, &C)`"));
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
            OpSym::Add | OpSym::Sub | OpSym::Mul | OpSym::Div | OpSym::Rem => {
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
        let call_owner = CallOwner::Function(f.name.clone());
        let control_outline = ControlOutline::build(call_owner.clone(), f.span, &f.body);
        let mut ctx = Ctx {
            sigs: &sigs,
            current_fn: f.name.clone(),
            call_owner,
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
            ownership: &mut ownership,
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
        let returns = check_block(
            &mut ctx,
            &mut f.body,
            f.ret.clone(),
            &control_outline,
            control_outline.body_block(),
        )?;
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
        callable_spans.insert(ctx.call_owner.clone(), f.name_span);
        call_graph.insert(ctx.call_owner.clone(), ctx.calls);
        control_outlines.push(control_outline);
    }

    // Fn templates (ADR 0009): typecheck against the abstract integer
    // model. `Ty::Param` stays distinct from `IntTy`; parameter-specific
    // gates (literals, conversions, division) fire explicitly on the way.
    let mut templates = std::mem::take(&mut program.fn_templates);
    for f in &mut templates {
        check_uart_params(&f.params)?;
        let call_owner = CallOwner::Function(f.name.clone());
        let control_outline = ControlOutline::build(call_owner.clone(), f.span, &f.body);
        let mut ctx = Ctx {
            sigs: &sigs,
            current_fn: f.name.clone(),
            call_owner,
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
            ownership: &mut ownership,
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
        let returns = check_block(
            &mut ctx,
            &mut f.body,
            f.ret.clone(),
            &control_outline,
            control_outline.body_block(),
        )?;
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
        control_outlines.push(control_outline);
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
            let call_owner = CallOwner::Constructor {
                class: meta.name.clone(),
                init: init.name.clone(),
            };
            let control_outline = ControlOutline::build(call_owner.clone(), init.span, &init.body);
            let mut ctx = Ctx {
                sigs: &sigs,
                current_fn: format!("{}::{}", meta.name, init.name),
                call_owner,
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
                ownership: &mut ownership,
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
            check_block(
                &mut ctx,
                &mut init.body,
                Ty::Unit,
                &control_outline,
                control_outline.body_block(),
            )?;
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
            callable_spans.insert(ctx.call_owner.clone(), init.name_span);
            call_graph.insert(ctx.call_owner.clone(), ctx.calls);
            control_outlines.push(control_outline);
        }
        for m in &mut class.methods {
            let call_owner = CallOwner::Method {
                class: meta.name.clone(),
                method: m.f.name.clone(),
            };
            let control_outline = ControlOutline::build(call_owner.clone(), m.f.span, &m.f.body);
            let mut ctx = Ctx {
                sigs: &sigs,
                current_fn: format!("{}::{}", meta.name, m.f.name),
                call_owner,
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
                ownership: &mut ownership,
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
            let returns = check_block(
                &mut ctx,
                &mut m.f.body,
                m.f.ret.clone(),
                &control_outline,
                control_outline.body_block(),
            )?;
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
            callable_spans.insert(ctx.call_owner.clone(), m.f.name_span);
            call_graph.insert(ctx.call_owner.clone(), ctx.calls);
            control_outlines.push(control_outline);
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
            let call_owner = CallOwner::Deinitializer {
                class: meta.name.clone(),
            };
            let control_outline = ControlOutline::build(call_owner.clone(), class.span, body);
            let mut ctx = Ctx {
                sigs: &sigs,
                current_fn: format!("{}::deinit", meta.name),
                call_owner,
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
                ownership: &mut ownership,
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
            let returns = check_block(
                &mut ctx,
                body,
                Ty::Unit,
                &control_outline,
                control_outline.body_block(),
            )?;
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
            callable_spans.insert(ctx.call_owner.clone(), class.name_span);
            call_graph.insert(ctx.call_owner.clone(), ctx.calls);
            control_outlines.push(control_outline);
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
            validate_member_names(c)?;
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
                let call_owner = CallOwner::Constructor {
                    class: meta.name.clone(),
                    init: init.name.clone(),
                };
                let control_outline =
                    ControlOutline::build(call_owner.clone(), init.span, &init.body);
                let mut ctx = Ctx {
                    sigs: &sigs,
                    current_fn: format!("{}::{}", meta.name, init.name),
                    call_owner,
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
                    ownership: &mut ownership,
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
                check_block(
                    &mut ctx,
                    &mut init.body,
                    Ty::Unit,
                    &control_outline,
                    control_outline.body_block(),
                )?;
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
                control_outlines.push(control_outline);
            }
            for m in &mut class.methods {
                check_uart_params(&m.f.params)?;
                let call_owner = CallOwner::Method {
                    class: meta.name.clone(),
                    method: m.f.name.clone(),
                };
                let control_outline =
                    ControlOutline::build(call_owner.clone(), m.f.span, &m.f.body);
                let mut ctx = Ctx {
                    sigs: &sigs,
                    current_fn: format!("{}::{}", meta.name, m.f.name),
                    call_owner,
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
                    ownership: &mut ownership,
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
                let returns = check_block(
                    &mut ctx,
                    &mut m.f.body,
                    m.f.ret.clone(),
                    &control_outline,
                    control_outline.body_block(),
                )?;
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
                control_outlines.push(control_outline);
            }
            // A template's destructor is checked exactly as a monomorphic
            // one is. Skipping it would leave the one member where fields
            // may be moved out unchecked, and generic resource-owning
            // classes are the ones that need it most.
            if let Some(body) = &mut class.deinit {
                let call_owner = CallOwner::Deinitializer {
                    class: meta.name.clone(),
                };
                let control_outline = ControlOutline::build(call_owner.clone(), class.span, body);
                let mut ctx = Ctx {
                    sigs: &sigs,
                    current_fn: format!("{}::deinit", meta.name),
                    call_owner,
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
                    ownership: &mut ownership,
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
                let returns = check_block(
                    &mut ctx,
                    body,
                    Ty::Unit,
                    &control_outline,
                    control_outline.body_block(),
                )?;
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
                control_outlines.push(control_outline);
            }
        }
    }
    program.class_templates = ctemplates;

    // Mutual recursion (self-recursion with a variant is handled inline).
    if let Some(cycle_member) = find_cycle(&call_graph) {
        let span = callable_spans
            .get(&cycle_member)
            .copied()
            .unwrap_or_else(|| Span::new(0, 0));
        return Err(Diagnostic {
            name: "type.mutual_recursion".into(),
            title: format!("{} is mutually recursive", cycle_member.render()),
            span,
            label: "mutual recursion is not supported yet (self-recursion with `variant` is)"
                .into(),
            notes: vec![("note".into(), "see docs/PLAN.md".into())],
        });
    }

    let control = ControlProgram::seal(program, &control_outlines).map_err(|error| Diagnostic {
        name: "internal.check.control_plan".into(),
        title: error.message,
        span: error.span,
        label: "the checked AST could not produce one exact control plan".into(),
        notes: vec![],
    })?;
    reconcile_slot_control(&control, &ownership)?;

    Ok(CheckResult {
        sigs,
        control,
        ownership,
        unsafe_regions,
    })
}

fn reconcile_slot_control(
    control: &ControlProgram,
    ownership: &CheckedOwnershipPlan,
) -> CResult<()> {
    for body in control.iter() {
        let owner = body.owner();
        let plan = body.plan();
        let mut visited = HashSet::new();
        for action in plan.slot_actions() {
            let Some(transition) = ownership.slot_transition(action.effect_key()) else {
                return Err(Diagnostic {
                    name: "internal.check.slot_control_transition_missing".into(),
                    title: format!(
                        "control slot action in {} has no checker ownership transition",
                        owner.render()
                    ),
                    span: action.span(),
                    label: "slot actions require one exact checker-authored ownership boundary"
                        .into(),
                    notes: vec![],
                });
            };
            if !visited.insert(action.effect_key().clone()) {
                return Err(Diagnostic {
                    name: "internal.check.duplicate_slot_control_transition".into(),
                    title: "two control actions reused one slot ownership transition".into(),
                    span: action.span(),
                    label: "owner and operation span must be injective".into(),
                    notes: vec![],
                });
            }
            let exact = transition.key == *action.effect_key()
                && transition.op_span == action.op_span()
                && transition.payload == *action.payload()
                && transition.result_ty == *action.result_ty()
                && match (&transition.kind, action.kind()) {
                    (
                        CheckedSlotTransitionKind::Alloc {
                            length_ty,
                            length_span,
                        },
                        SlotActionKind::Alloc {
                            length_span: action_length,
                        },
                    ) => *length_ty == Ty::Int(IntTy::U64) && length_span == action_length,
                    (
                        CheckedSlotTransitionKind::Take {
                            container,
                            container_span,
                            index_ty,
                            index_span,
                        },
                        SlotActionKind::Take {
                            container: action_container,
                            container_span: action_container_span,
                            index_span: action_index_span,
                        },
                    ) => {
                        container == action_container
                            && container_span == action_container_span
                            && *index_ty == Ty::Int(IntTy::U64)
                            && index_span == action_index_span
                    }
                    (
                        CheckedSlotTransitionKind::Put {
                            container,
                            container_span,
                            index_ty,
                            index_span,
                            value_span,
                            value_transfer,
                        },
                        SlotActionKind::Put {
                            container: action_container,
                            container_span: action_container_span,
                            index_span: action_index_span,
                            value_span: action_value_span,
                            value_transfer: action_transfer,
                            ..
                        },
                    ) => {
                        container == action_container
                            && container_span == action_container_span
                            && *index_ty == Ty::Int(IntTy::U64)
                            && index_span == action_index_span
                            && value_span == action_value_span
                            && value_transfer == action_transfer
                    }
                    (
                        CheckedSlotTransitionKind::Alloc { .. },
                        SlotActionKind::Take { .. } | SlotActionKind::Put { .. },
                    )
                    | (
                        CheckedSlotTransitionKind::Take { .. },
                        SlotActionKind::Alloc { .. } | SlotActionKind::Put { .. },
                    )
                    | (
                        CheckedSlotTransitionKind::Put { .. },
                        SlotActionKind::Alloc { .. } | SlotActionKind::Take { .. },
                    ) => false,
                };
            if !exact {
                return Err(Diagnostic {
                    name: "internal.check.slot_control_transition_mismatch".into(),
                    title: "control and ownership disagree about a checked slot transition".into(),
                    span: action.span(),
                    label: "operation, place, types, spans, and transfer identity must all match"
                        .into(),
                    notes: vec![],
                });
            }
        }
        let owned_count = ownership.slot_transitions_for_owner(owner).count();
        if visited.len() != owned_count {
            let missing = ownership
                .slot_transitions_for_owner(owner)
                .find(|(key, _)| !visited.contains(*key))
                .map(|(key, _)| key)
                .expect("slot transition counts differ");
            return Err(Diagnostic {
                name: "internal.check.slot_control_action_missing".into(),
                title: format!(
                    "checker slot transition in {} has no retained control action",
                    owner.render()
                ),
                span: missing.span,
                label: "complete callable reconciliation visits every slot transition".into(),
                notes: vec![],
            });
        }
    }
    Ok(())
}

fn control_outline_mismatch(span: Span, detail: &str) -> Diagnostic {
    Diagnostic {
        name: "internal.check.control_outline".into(),
        title: "body changed while the checker was consuming its control outline".into(),
        span,
        label: detail.into(),
        notes: vec![],
    }
}

/// Check one block through the exact pre-check structural outline. The return
/// value is retained for existing callers, but it comes from the outline's
/// single flow fact rather than being recomputed during the type walk.
fn check_block(
    ctx: &mut Ctx,
    stmts: &mut [Stmt],
    ret_ty: Ty,
    outline: &ControlOutline,
    block: BlockId,
) -> CResult<bool> {
    let planned_block = outline.block(block);
    if planned_block.statements().len() != stmts.len() {
        return Err(control_outline_mismatch(
            planned_block.anchor(),
            "statement count differs from the pre-check structural plan",
        ));
    }
    for (index, stmt) in stmts.iter_mut().enumerate() {
        let statement_plan = outline.statement(block, index);
        if !statement_plan.entry_reachable() {
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
                local_ty(ty, *name_span)?;
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
                if matches!(ty, Ty::Slots(_)) && init.is_none() {
                    return Err(Diagnostic {
                        name: "type.slot_initializer".into(),
                        title: format!("owner-slot local `{name}` needs an initializer"),
                        span: *name_span,
                        label: "initialize it with `alloc_slots<T>(len)` or a whole-owner move"
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
                    // The owning family is routed away from the copy rules by
                    // the payload, and it is routed first: the paths below
                    // build a copyable value out of whatever the initializer
                    // evaluates to.
                    if ty.is_affine_option() {
                        check_affine_option_initializer(ctx, e, ty)?;
                    } else if matches!(&e.kind, ExprKind::OptTake { .. }) {
                        if ty.is_owned_array_of(&Ty::Bool) {
                            check_affine_option_take(ctx, e)?;
                        } else {
                            return Err(option_take_position(e.span));
                        }
                    } else {
                        check_direct_slot_expr(
                            ctx,
                            e,
                            Some(ty.clone()),
                            DirectSlotPosition::ExplicitLocal,
                        )?;
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
                    must_consume = transfer_and_record(
                        ctx,
                        e,
                        ValueTransferSink::Binding(name.clone()),
                        None,
                    )?
                    .carried_obligation;
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
                if matches!(ty, Ty::Class(_) | Ty::Res(_) | Ty::Slots(_)) {
                    // Reassignment of a class local is a move-in of an
                    // owned value; the old value is dropped, with its
                    // RAII invariant check. Check first: operator sugar
                    // may rewrite a Binary RHS into the bound call
                    // (ADR 0012). A resource local follows the same rule,
                    // and dropping the old token discards its authority
                    // rather than running anything (ADR 0024).
                    check_direct_slot_expr(ctx, value, Some(ty), DirectSlotPosition::Assignment)?;
                    // A bare name is a local-to-local move: the source
                    // place dies here (ADR 0020). Every other class-typed
                    // expression is a call or a construction — a fresh
                    // owned value that nothing else names.
                    let dest = Place::local(name);
                    reject_overwrite_of_obligation(ctx, &dest, *name_span)?;
                    let carries = transfer_and_record(
                        ctx,
                        value,
                        ValueTransferSink::Assignment(dest.clone()),
                        escape_sink(dest_branded, name_span),
                    )?
                    .carried_obligation;
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
                    check_direct_slot_expr(ctx, value, Some(ty), DirectSlotPosition::Assignment)?;
                    transfer_and_record(
                        ctx,
                        value,
                        ValueTransferSink::Assignment(Place::local(name)),
                        escape_sink(dest_branded, name_span),
                    )?;
                    ctx.vars.get_mut(name.as_str()).unwrap().initialized = true;
                }
            }

            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                let StatementPlanKind::Branch(branch_id) = statement_plan.kind() else {
                    return Err(control_outline_mismatch(
                        cond.span,
                        "an `if` no longer has its retained branch identity",
                    ));
                };
                let branch_plan = outline.branch(branch_id);
                if branch_plan.else_block().is_some() != else_block.is_some() {
                    return Err(control_outline_mismatch(
                        cond.span,
                        "the branch's else-arm presence changed during checking",
                    ));
                }
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
                check_block(
                    ctx,
                    then_block,
                    ret_ty.clone(),
                    outline,
                    branch_plan.then_block(),
                )?;
                let then_ret = outline
                    .block(branch_plan.then_block())
                    .flow()
                    .definitely_returns();
                let after_then = snapshot(ctx);
                let after_then_moved = ctx.moved.clone();
                restore(ctx, &before);
                ctx.moved = before_moved.clone();
                let else_ret = match (else_block, branch_plan.else_block()) {
                    (Some(body), Some(child)) => {
                        check_block(ctx, body, ret_ty.clone(), outline, child)?;
                        outline.block(child).flow().definitely_returns()
                    }
                    (None, None) => false,
                    (Some(_body), None) => {
                        return Err(control_outline_mismatch(
                            cond.span,
                            "the branch's retained else arm no longer matches the source",
                        ));
                    }
                    (None, Some(_child)) => {
                        return Err(control_outline_mismatch(
                            cond.span,
                            "the branch's retained else arm no longer matches the source",
                        ));
                    }
                };
                let after_else = snapshot(ctx);
                let after_else_moved = ctx.moved.clone();
                // Both arm-local lifetimes end before their states are joined.
                // `declared` remains global, so the name cannot be reused, but
                // it is no longer a source place an outer/sibling assignment
                // can resurrect.
                restore(ctx, &before);
                ctx.moved = before_moved.clone();
                // Reaching branches only: a branch that returns
                // contributes nothing to the fall-through state.
                let mut reaching_init: Vec<&HashMap<String, PlaceState>> = Vec::new();
                let mut reaching_moved: Vec<&HashSet<Place>> = Vec::new();
                if !then_ret {
                    reaching_init.push(&after_then);
                    reaching_moved.push(&after_then_moved);
                }
                if !else_ret {
                    match branch_plan.else_block() {
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
                // A moved projection rooted in an arm-local place is no more
                // visible than the local itself. Preserve projections of an
                // outer root (and the explicit `self.f` pseudo-variables),
                // but do not leak child-place identities past the join.
                ctx.moved.retain(|place| {
                    before.contains_key(&place.state_key()) || before.contains_key(place.root())
                });
            }
            Stmt::While {
                cond,
                variant,
                kw_span,
                body,
                ..
            } => {
                let StatementPlanKind::Loop(loop_id) = statement_plan.kind() else {
                    return Err(control_outline_mismatch(
                        *kw_span,
                        "a `while` no longer has its retained loop identity",
                    ));
                };
                let loop_plan = outline.loop_plan(loop_id);
                if loop_plan.keyword_span() != *kw_span || loop_plan.condition_span() != cond.span {
                    return Err(control_outline_mismatch(
                        *kw_span,
                        "the loop anchor or condition changed during checking",
                    ));
                }
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
                check_block(ctx, body, ret_ty.clone(), outline, loop_plan.body())?;
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
                let loop_effects = checked_loop_effects(ctx, *kw_span, cond, body)?;
                ctx.ownership
                    .insert_loop(loop_effects)
                    .map_err(|duplicate| Diagnostic {
                        name: "internal.check.duplicate_loop_effect".into(),
                        title: format!(
                            "duplicate loop-effect identity inside {}",
                            duplicate.owner.render()
                        ),
                        span: duplicate.span,
                        label: "owner and keyword span must identify exactly one loop".into(),
                        notes: vec![],
                    })?;
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
                match ret_ty.clone() {
                    Ty::Unit => match value {
                        None => {}
                        Some(e) => {
                            return Err(Diagnostic {
                                name: "type.return_value_in_procedure".into(),
                                title: "this function has no return type".into(),
                                span: e.span,
                                label: "remove the value (or declare `-> T`)".into(),
                                notes: vec![],
                            });
                        }
                    },
                    return_ty @ (Ty::Int(_)
                    | Ty::Bool
                    | Ty::Param(_)
                    | Ty::Class(_)
                    | Ty::Record(_)
                    | Ty::Array(_)
                    | Ty::Slots(_)
                    | Ty::Option(_)
                    | Ty::OptionRaw(_)
                    | Ty::Res(_)
                    | Ty::Raw(_)
                    | Ty::RawRecord(_)
                    | Ty::Borrow(..)) => match value {
                        None => {
                            return Err(Diagnostic {
                                name: "type.missing_return_value".into(),
                                title: format!(
                                    "`return;` in a function returning `{}`",
                                    return_ty.name()
                                ),
                                span: *span,
                                label: "a value is required".into(),
                                notes: vec![],
                            });
                        }
                        Some(e) => {
                            check_direct_slot_expr(
                                ctx,
                                e,
                                Some(return_ty),
                                DirectSlotPosition::Return,
                            )?;
                            // Returning a place consumes it: the value leaves
                            // with the caller, and a field returned this way is
                            // authority the object no longer has.
                            transfer_and_record(
                                ctx,
                                e,
                                ValueTransferSink::Return,
                                Some(("be returned", e.span)),
                            )?;
                        }
                    },
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
            }
            Stmt::ExprStmt(e) => {
                let ty = check_direct_slot_expr(ctx, e, None, DirectSlotPosition::Statement)?;
                // A discarded class *result* is a temporary and is destroyed
                // at the end of this statement. A place projection is not a
                // temporary: if an internal AST producer supplied an
                // expression statement such as `self.child;`, it would only
                // read the installed owner. Treating that read as the value to
                // drop would run its destructor while the field still named it.
                // Use the same place decoder as every ownership sink rather
                // than maintaining a second list of place-shaped expressions.
                if matches!(ty, Ty::Class(_)) {
                    if let Some(source) = Place::from_value_expr(e) {
                        return Err(Diagnostic {
                            name: "type.class_temporary_source".into(),
                            title: format!(
                                "discarding class place `{}` as a temporary",
                                source.render()
                            ),
                            span: e.span,
                            label: "only a fresh class result can be discarded".into(),
                            notes: vec![(
                                "note".into(),
                                "a discarded class result is destroyed at the end of the statement; \
                                 a named place stays live and must not be destroyed through a read"
                                    .into(),
                            )],
                        });
                    }
                }
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
                // A discarded class result is still a by-value ownership
                // boundary: the fresh value moves into a compiler-owned
                // statement temporary whose retained control action destroys
                // it before the continuation. Record that handoff only after
                // every rejection above, so a place read or inadmissible
                // affine temporary cannot leave a partial discard fact.
                if matches!(ty, Ty::Class(_)) {
                    transfer_and_record(ctx, e, ValueTransferSink::DiscardTemporary, None)?;
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
                    if matches!(cached, Ty::Slots(_)) {
                        return Err(Diagnostic {
                            name: "slots.inferred_type".into(),
                            title: "an owner-slot binding cannot use inferred-local syntax".into(),
                            span: *name_span,
                            label: "write an explicit `slots<T>` declaration for slot allocation"
                                .into(),
                            notes: vec![(
                                "note".into(),
                                "a whole-owner move may be inferred only from the live source owner"
                                    .into(),
                            )],
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
                    ExprKind::Var(src) => ctx
                        .vars
                        .get(src.as_str())
                        .map(|v| v.ty.clone())
                        .filter(|ty| matches!(ty, Ty::Class(_) | Ty::Slots(_))),
                    ExprKind::SelfField { field } => ctx
                        .vars
                        .get(format!("self.{field}").as_str())
                        .map(|v| v.ty.clone())
                        .filter(|ty| matches!(ty, Ty::Class(_) | Ty::Slots(_))),
                    ExprKind::IntLit(_)
                    | ExprKind::BoolLit(_)
                    | ExprKind::Unary { .. }
                    | ExprKind::Binary { .. }
                    | ExprKind::Call { .. }
                    | ExprKind::Index { .. }
                    | ExprKind::Len { .. }
                    | ExprKind::RawOp { .. }
                    | ExprKind::DeviceOp { .. }
                    | ExprKind::ResOp { .. }
                    | ExprKind::SlotOp { .. }
                    | ExprKind::Widen { .. }
                    | ExprKind::Narrow { .. }
                    | ExprKind::IsSome { .. }
                    | ExprKind::OptValue { .. }
                    | ExprKind::OptTake { .. }
                    | ExprKind::SomeE(_)
                    | ExprKind::NoneE
                    | ExprKind::ArrayLit(_)
                    | ExprKind::AllocArray { .. }
                    | ExprKind::SelfFieldLen { .. }
                    | ExprKind::SelfFieldIndex { .. }
                    | ExprKind::CtorCall { .. }
                    | ExprKind::ClassField { .. }
                    | ExprKind::RecordField { .. }
                    | ExprKind::ClassFieldLen { .. }
                    | ExprKind::ClassFieldIndex { .. }
                    | ExprKind::TraitCall { .. }
                    | ExprKind::MethodCall { .. }
                    | ExprKind::Borrow { .. }
                    | ExprKind::RecordLit { .. } => None,
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
                            Ty::Int(_)
                            | Ty::Bool
                            | Ty::Param(_)
                            | Ty::Record(_)
                            | Ty::Array(_)
                            | Ty::Slots(_)
                            | Ty::Option(_)
                            | Ty::OptionRaw(_)
                            | Ty::Res(_)
                            | Ty::Raw(_)
                            | Ty::RawRecord(_)
                            | Ty::Borrow(..)
                            | Ty::Unit => None,
                        }),
                    ExprKind::IntLit(_)
                    | ExprKind::BoolLit(_)
                    | ExprKind::Var(_)
                    | ExprKind::Unary { .. }
                    | ExprKind::Binary { .. }
                    | ExprKind::Call { .. }
                    | ExprKind::Index { .. }
                    | ExprKind::Len { .. }
                    | ExprKind::RawOp { .. }
                    | ExprKind::DeviceOp { .. }
                    | ExprKind::ResOp { .. }
                    | ExprKind::SlotOp { .. }
                    | ExprKind::Widen { .. }
                    | ExprKind::Narrow { .. }
                    | ExprKind::IsSome { .. }
                    | ExprKind::OptValue { .. }
                    | ExprKind::SomeE(_)
                    | ExprKind::NoneE
                    | ExprKind::ArrayLit(_)
                    | ExprKind::AllocArray { .. }
                    | ExprKind::SelfField { .. }
                    | ExprKind::SelfFieldLen { .. }
                    | ExprKind::SelfFieldIndex { .. }
                    | ExprKind::CtorCall { .. }
                    | ExprKind::ClassField { .. }
                    | ExprKind::RecordField { .. }
                    | ExprKind::ClassFieldLen { .. }
                    | ExprKind::ClassFieldIndex { .. }
                    | ExprKind::TraitCall { .. }
                    | ExprKind::MethodCall { .. }
                    | ExprKind::Borrow { .. }
                    | ExprKind::RecordLit { .. } => None,
                };
                let t = if take_class.is_some() {
                    check_affine_option_take(ctx, init)?
                } else {
                    match moved_from {
                        Some(owner_ty) => {
                            check_direct_slot_expr(
                                ctx,
                                init,
                                Some(owner_ty.clone()),
                                DirectSlotPosition::InferredLocal,
                            )?;
                            owner_ty
                        }
                        None => check_direct_slot_expr(
                            ctx,
                            init,
                            None,
                            DirectSlotPosition::InferredLocal,
                        )?,
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
                let must_consume =
                    transfer_and_record(ctx, init, ValueTransferSink::Binding(name.clone()), None)?
                        .carried_obligation;
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
                let StatementPlanKind::Unsafe(child) = statement_plan.kind() else {
                    return Err(control_outline_mismatch(
                        stmt_span(stmt),
                        "an `unsafe` block no longer has its retained block identity",
                    ));
                };
                let outer = ctx.in_unsafe;
                ctx.in_unsafe = true;
                ctx.unsafe_blocks += 1;
                let result = check_block(ctx, body, ret_ty.clone(), outline, child);
                ctx.in_unsafe = outer;
                result?;
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
                transfer_and_record(ctx, res, ValueTransferSink::SystemDeallocResource, None)?;
                check_expr(ctx, release, Some(Ty::Res(ResKind::SystemDealloc)))?;
                transfer_and_record(ctx, release, ValueTransferSink::SystemDeallocRelease, None)?;
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
                let StatementPlanKind::Exposure(exposure_id) = statement_plan.kind() else {
                    return Err(control_outline_mismatch(
                        *kw_span,
                        "an exposure no longer has its retained block identity",
                    ));
                };
                let exposure_plan = outline.exposure(exposure_id);
                if exposure_plan.keyword_span() != *kw_span {
                    return Err(control_outline_mismatch(
                        *kw_span,
                        "the exposure anchor changed during checking",
                    ));
                }
                // A nested exposure of an already-exposed array would open
                // a second loan on one buffer.
                reject_exposed_owner(ctx, array, *array_span)?;
                let (elem, src_mut, declared_mut, owner_ty) = match ctx.vars.get(array.as_str()) {
                    Some(v) => {
                        if v.ty.is_affine_option() {
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
                        match checked_array_binding(&v.ty) {
                            Some((element, mode)) => (element, mode, v.mutable, v.ty.clone()),
                            None => {
                                return Err(Diagnostic {
                                    name: "expose.not_an_array".into(),
                                    title: format!("`{array}` is not an array"),
                                    span: *array_span,
                                    label: format!("this has type `{}`", v.ty.clone().name()),
                                    notes: vec![],
                                });
                            }
                        }
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
                    (ptr.as_str(), *ptr_span, Ty::Raw(IntTy::U8)),
                    (res.as_str(), *res_span, Ty::Res(ResKind::RawSpan)),
                ] {
                    if !ctx.declared.insert(name.to_string()) {
                        return Err(Diagnostic {
                            name: "type.duplicate_name".into(),
                            title: format!("duplicate variable name `{name}`"),
                            span,
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
                let result = check_block(ctx, body, ret_ty.clone(), outline, exposure_plan.body());
                ctx.in_unsafe = outer;
                result?;
                if exposure_plan.flow().contains_return() {
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
                let effect = CheckedExposure {
                    key: EffectSiteKey {
                        owner: ctx.call_owner.clone(),
                        span: *kw_span,
                    },
                    owner_place: Place::local(array),
                    owner_span: *array_span,
                    owner_ty,
                    mutability: if *mutable {
                        Mutability::Mut
                    } else {
                        Mutability::Shared
                    },
                    pointer: ptr.clone(),
                    pointer_span: *ptr_span,
                    resource: res.clone(),
                    resource_span: *res_span,
                };
                ctx.ownership
                    .insert_exposure(effect)
                    .map_err(|duplicate| Diagnostic {
                        name: "internal.check.duplicate_exposure".into(),
                        title: format!(
                            "duplicate exposure identity inside {}",
                            duplicate.owner.render()
                        ),
                        span: duplicate.span,
                        label: "owner and keyword span must identify exactly one exposure".into(),
                        notes: vec![],
                    })?;
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
                                Some(
                                    Ty::Int(_)
                                    | Ty::Bool
                                    | Ty::Param(_)
                                    | Ty::Class(_)
                                    | Ty::Record(_)
                                    | Ty::Array(_)
                                    | Ty::Slots(_)
                                    | Ty::Option(_)
                                    | Ty::OptionRaw(_)
                                    | Ty::Res(_)
                                    | Ty::Raw(_)
                                    | Ty::RawRecord(_)
                                    | Ty::Borrow(..)
                                    | Ty::Unit,
                                )
                                | None => {
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
                        ExprKind::IntLit(_)
                        | ExprKind::BoolLit(_)
                        | ExprKind::Unary { .. }
                        | ExprKind::Binary { .. }
                        | ExprKind::Call { .. }
                        | ExprKind::Index { .. }
                        | ExprKind::Len { .. }
                        | ExprKind::RawOp { .. }
                        | ExprKind::DeviceOp { .. }
                        | ExprKind::ResOp { .. }
                        | ExprKind::SlotOp { .. }
                        | ExprKind::Widen { .. }
                        | ExprKind::Narrow { .. }
                        | ExprKind::IsSome { .. }
                        | ExprKind::OptValue { .. }
                        | ExprKind::OptTake { .. }
                        | ExprKind::SomeE(_)
                        | ExprKind::NoneE
                        | ExprKind::ArrayLit(_)
                        | ExprKind::SelfField { .. }
                        | ExprKind::SelfFieldLen { .. }
                        | ExprKind::SelfFieldIndex { .. }
                        | ExprKind::CtorCall { .. }
                        | ExprKind::ClassField { .. }
                        | ExprKind::RecordField { .. }
                        | ExprKind::ClassFieldLen { .. }
                        | ExprKind::ClassFieldIndex { .. }
                        | ExprKind::TraitCall { .. }
                        | ExprKind::MethodCall { .. }
                        | ExprKind::Borrow { .. }
                        | ExprKind::RecordLit { .. } => {
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
                    check_direct_slot_expr(
                        ctx,
                        value,
                        Some(fty.clone()),
                        DirectSlotPosition::FieldAssignment,
                    )?;
                }
                // A field is a sink like any other: it takes the value, so
                // the source place dies. And a field outlives the exposure
                // body, so it is a place a brand may not reach.
                let dest = Place::field("self", field);
                reject_overwrite_of_obligation(ctx, &dest, *field_span)?;
                let carries = transfer_and_record(
                    ctx,
                    value,
                    ValueTransferSink::FieldAssignment(dest.clone()),
                    Some(("be stored in a field", *field_span)),
                )?
                .carried_obligation;
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
                if matches!(fty, Ty::Slots(_)) {
                    return Err(slot_store_unsupported(*field_span));
                }
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
                    Some(v) if matches!(v.ty, Ty::Slots(_)) => {
                        return Err(slot_store_unsupported(*array_span));
                    }
                    Some(v) => match checked_array_binding(&v.ty) {
                        Some((element, mode)) => (element.clone(), mode, v.mutable),
                        None => {
                            return Err(Diagnostic {
                                name: "type.not_an_array".into(),
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
    Ok(planned_block.flow().definitely_returns())
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
        ExprKind::IntLit(_)
        | ExprKind::BoolLit(_)
        | ExprKind::Unary { .. }
        | ExprKind::Binary { .. }
        | ExprKind::Call { .. }
        | ExprKind::Index { .. }
        | ExprKind::Len { .. }
        | ExprKind::RawOp { .. }
        | ExprKind::DeviceOp { .. }
        | ExprKind::ResOp { .. }
        | ExprKind::SlotOp { .. }
        | ExprKind::Widen { .. }
        | ExprKind::Narrow { .. }
        | ExprKind::IsSome { .. }
        | ExprKind::OptValue { .. }
        | ExprKind::OptTake { .. }
        | ExprKind::SomeE(_)
        | ExprKind::NoneE
        | ExprKind::ArrayLit(_)
        | ExprKind::AllocArray { .. }
        | ExprKind::SelfFieldLen { .. }
        | ExprKind::SelfFieldIndex { .. }
        | ExprKind::CtorCall { .. }
        | ExprKind::ClassField { .. }
        | ExprKind::RecordField { .. }
        | ExprKind::ClassFieldLen { .. }
        | ExprKind::ClassFieldIndex { .. }
        | ExprKind::TraitCall { .. }
        | ExprKind::MethodCall { .. }
        | ExprKind::RecordLit { .. } => e.ty.clone(),
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
        unexpected => unreachable!("unknown affine-option boundary `{unexpected}`"),
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
        Ty::Slots(payload) => slot_payload_ty(&payload, span),
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

fn slots_unsupported(span: Span, role: impl AsRef<str>) -> Diagnostic {
    Diagnostic {
        name: "type.slots_unsupported".into(),
        title: "owner slots are not admitted at this boundary".into(),
        span,
        label: format!(
            "{} uses `slots<T>` outside its sealed local/field operations",
            role.as_ref()
        ),
        notes: vec![(
            "note".into(),
            "owner slots are local or class-field storage; they do not cross calls, returns, ordinary borrows, or record layout"
                .into(),
        )],
    }
}

fn slot_index_unsupported(span: Span) -> Diagnostic {
    Diagnostic {
        name: "slots.index_unsupported".into(),
        title: "owner-slot cells cannot be indexed directly".into(),
        span,
        label: "use `slot_take(&mut owner, index)` to extract an occupied cell".into(),
        notes: vec![(
            "note".into(),
            "a direct read would erase whether the cell remains occupied".into(),
        )],
    }
}

fn slot_store_unsupported(span: Span) -> Diagnostic {
    Diagnostic {
        name: "slots.store_unsupported".into(),
        title: "owner-slot cells cannot be assigned directly".into(),
        span,
        label: "use `slot_put(&mut owner, index, value)` as a statement".into(),
        notes: vec![(
            "note".into(),
            "put checks that the destination cell is empty before installing its owner".into(),
        )],
    }
}

/// Payloads admitted by the first occupied-slot transition model. This is an
/// allow-list independent of parser position so substituted generic instances
/// and forged typed ASTs meet the same boundary.
fn slot_payload_ty(payload: &Ty, span: Span) -> CResult<()> {
    match payload {
        Ty::Int(IntTy::TParam(_)) => Err(noncanonical_aggregate_payload(span)),
        Ty::Int(
            IntTy::U8
            | IntTy::U16
            | IntTy::U32
            | IntTy::U64
            | IntTy::I8
            | IntTy::I16
            | IntTy::I32
            | IntTy::I64,
        )
        | Ty::Bool
        | Ty::Param(_)
        | Ty::Record(_)
        | Ty::Class(_) => Ok(()),
        Ty::Array(_)
        | Ty::Slots(_)
        | Ty::Option(_)
        | Ty::OptionRaw(_)
        | Ty::Res(_)
        | Ty::Raw(_)
        | Ty::RawRecord(_)
        | Ty::Borrow(..)
        | Ty::Unit => Err(Diagnostic {
            name: "type.slot_payload_unsupported".into(),
            title: format!(
                "`{}` has no occupied-slot payload semantics",
                payload.clone().name()
            ),
            span,
            label: "expected an integer, `bool`, type parameter, POD record, or direct class"
                .into(),
            notes: vec![(
                "note".into(),
                "nested containers, resources, raw values, borrows, and unit remain outside the first slot cleanup model"
                    .into(),
            )],
        }),
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
        | Ty::Slots(_)
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
    if matches!(ty, Ty::Slots(_)) {
        return Err(slots_unsupported(span, "parameter"));
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
            Ty::Param(_)
            | Ty::Class(_)
            | Ty::Record(_)
            | Ty::Array(_)
            | Ty::Slots(_)
            | Ty::Option(_)
            | Ty::OptionRaw(_)
            | Ty::Res(_)
            | Ty::Raw(_)
            | Ty::RawRecord(_)
            | Ty::Borrow(..)
            | Ty::Unit => false,
        },
        Ty::Int(_)
        | Ty::Bool
        | Ty::Param(_)
        | Ty::Class(_)
        | Ty::Record(_)
        | Ty::Array(_)
        | Ty::Slots(_)
        | Ty::OptionRaw(_)
        | Ty::Res(_)
        | Ty::Raw(_)
        | Ty::RawRecord(_)
        | Ty::Borrow(..)
        | Ty::Unit => false,
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
    if matches!(ty, Ty::Slots(_)) {
        return Err(slots_unsupported(
            span,
            format!("return type of `{fn_name}`"),
        ));
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
    if matches!(ty, Ty::Borrow(_, referent) if matches!(referent.as_ref(), Ty::Slots(_))) {
        return Err(Diagnostic {
            name: "type.slot_owner_binding".into(),
            title: "an owner-slot field must own its allocation".into(),
            span,
            label: "borrowed slot containers exist only for one `slot_take` or `slot_put`".into(),
            notes: vec![],
        });
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
            Ty::Param(_)
            | Ty::Class(_)
            | Ty::Record(_)
            | Ty::Array(_)
            | Ty::Slots(_)
            | Ty::Option(_)
            | Ty::OptionRaw(_)
            | Ty::Res(_)
            | Ty::Raw(_)
            | Ty::RawRecord(_)
            | Ty::Borrow(..)
            | Ty::Unit => false,
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
/// value, so this is a positive gate: only integers and the retained type
/// parameter that monomorphizes to an integer are admitted. Keeping the
/// match exhaustive prevents a newly transportable ordinary-call shape
/// from silently entering the narrower trait proof domain.
pub(crate) fn trait_param_ty(ty: &Ty, span: Span) -> CResult<()> {
    if ty.is_affine_option() {
        return Err(affine_option_boundary(ty.clone(), span, "trait"));
    }
    match ty {
        Ty::Int(_) | Ty::Param(_) => Ok(()),
        Ty::Bool
        | Ty::Class(_)
        | Ty::Record(_)
        | Ty::Array(_)
        | Ty::Slots(_)
        | Ty::Option(_)
        | Ty::OptionRaw(_)
        | Ty::Res(_)
        | Ty::Raw(_)
        | Ty::RawRecord(_)
        | Ty::Borrow(..)
        | Ty::Unit => Err(Diagnostic {
            name: "type.trait_param_unsupported".into(),
            title: "trait methods accept only integer proof-value parameters".into(),
            span,
            label: format!(
                "`{}` is not supported in a trait method parameter",
                ty.clone().name()
            ),
            notes: vec![(
                "note".into(),
                "ordinary functions transport more value, owner, pointer, and borrow shapes; \
                 a retained trait call substitutes only integer arguments into its abstract \
                 contract"
                    .into(),
            )],
        }),
    }
}

/// The declared result type of a trait method. This is the result-side half
/// of the same positive integer proof-domain gate as `trait_param_ty`.
pub(crate) fn trait_return_ty(ty: &Ty, method_name: &str, span: Span) -> CResult<()> {
    if ty.is_affine_option() {
        return Err(affine_option_boundary(ty.clone(), span, "trait"));
    }
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
    match ty {
        Ty::Int(_) | Ty::Param(_) => Ok(()),
        Ty::Bool
        | Ty::Class(_)
        | Ty::Record(_)
        | Ty::Array(_)
        | Ty::Slots(_)
        | Ty::OptionRaw(_)
        | Ty::Res(_)
        | Ty::Raw(_)
        | Ty::RawRecord(_)
        | Ty::Borrow(..)
        | Ty::Unit => Err(Diagnostic {
            name: "type.trait_return_unsupported".into(),
            title: "trait methods return only integer proof values".into(),
            span,
            label: format!(
                "`{}` is not supported as a trait method result",
                ty.clone().name()
            ),
            notes: vec![(
                "note".into(),
                format!(
                    "ordinary function `{method_name}` may return other supported values or \
                     owners; a retained trait call has only an integer result in its abstract \
                     contract"
                )
                .into(),
            )],
        }),
        Ty::Option(_) => unreachable!("value-option results were rejected above"),
    }
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
                Stmt::Decl { .. }
                | Stmt::Assign { .. }
                | Stmt::Return { .. }
                | Stmt::ExprStmt(_)
                | Stmt::Assert(_)
                | Stmt::VarDecl { .. }
                | Stmt::FieldAssign { .. }
                | Stmt::FieldStore { .. }
                | Stmt::Store { .. }
                | Stmt::StaticAlloc { .. }
                | Stmt::SystemAlloc { .. }
                | Stmt::SystemDealloc { .. } => {}
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
        concrete @ (IntTy::U8
        | IntTy::U16
        | IntTy::U32
        | IntTy::U64
        | IntTy::I8
        | IntTy::I16
        | IntTy::I32
        | IntTy::I64) => Ty::Int(concrete),
    }
}

/// Exhaustive checker-side view of an array binding.  Keeping this match in
/// the trusted checker (rather than hiding the negative case behind an
/// `Option<Ty>` wildcard) makes every new `Ty` constructor require an explicit
/// ownership decision here.
fn checked_array_binding(ty: &Ty) -> Option<(&Ty, BindingMode)> {
    match ty {
        Ty::Array(element) => Some((element, BindingMode::Owned)),
        Ty::Borrow(Mutability::Shared, referent) => match referent.as_ref() {
            Ty::Array(element) => Some((element, BindingMode::Shared)),
            Ty::Int(_)
            | Ty::Bool
            | Ty::Param(_)
            | Ty::Class(_)
            | Ty::Record(_)
            | Ty::Slots(_)
            | Ty::Option(_)
            | Ty::OptionRaw(_)
            | Ty::Res(_)
            | Ty::Raw(_)
            | Ty::RawRecord(_)
            | Ty::Borrow(..)
            | Ty::Unit => None,
        },
        Ty::Borrow(Mutability::Mut, referent) => match referent.as_ref() {
            Ty::Array(element) => Some((element, BindingMode::Mut)),
            Ty::Int(_)
            | Ty::Bool
            | Ty::Param(_)
            | Ty::Class(_)
            | Ty::Record(_)
            | Ty::Slots(_)
            | Ty::Option(_)
            | Ty::OptionRaw(_)
            | Ty::Res(_)
            | Ty::Raw(_)
            | Ty::RawRecord(_)
            | Ty::Borrow(..)
            | Ty::Unit => None,
        },
        Ty::Int(_)
        | Ty::Bool
        | Ty::Param(_)
        | Ty::Class(_)
        | Ty::Record(_)
        | Ty::Slots(_)
        | Ty::Option(_)
        | Ty::OptionRaw(_)
        | Ty::Res(_)
        | Ty::Raw(_)
        | Ty::RawRecord(_)
        | Ty::Unit => None,
    }
}

/// Exhaustive checker-side view of a class borrow.  The explicit mutability
/// arms also ensure a future loan mode cannot silently inherit shared-borrow
/// behavior.
fn checked_class_borrow(ty: &Ty) -> Option<(usize, Mutability)> {
    match ty {
        Ty::Borrow(Mutability::Shared, referent) => match referent.as_ref() {
            Ty::Class(class) => Some((*class, Mutability::Shared)),
            Ty::Int(_)
            | Ty::Bool
            | Ty::Param(_)
            | Ty::Record(_)
            | Ty::Array(_)
            | Ty::Slots(_)
            | Ty::Option(_)
            | Ty::OptionRaw(_)
            | Ty::Res(_)
            | Ty::Raw(_)
            | Ty::RawRecord(_)
            | Ty::Borrow(..)
            | Ty::Unit => None,
        },
        Ty::Borrow(Mutability::Mut, referent) => match referent.as_ref() {
            Ty::Class(class) => Some((*class, Mutability::Mut)),
            Ty::Int(_)
            | Ty::Bool
            | Ty::Param(_)
            | Ty::Record(_)
            | Ty::Array(_)
            | Ty::Slots(_)
            | Ty::Option(_)
            | Ty::OptionRaw(_)
            | Ty::Res(_)
            | Ty::Raw(_)
            | Ty::RawRecord(_)
            | Ty::Borrow(..)
            | Ty::Unit => None,
        },
        Ty::Int(_)
        | Ty::Bool
        | Ty::Param(_)
        | Ty::Class(_)
        | Ty::Record(_)
        | Ty::Array(_)
        | Ty::Slots(_)
        | Ty::Option(_)
        | Ty::OptionRaw(_)
        | Ty::Res(_)
        | Ty::Raw(_)
        | Ty::RawRecord(_)
        | Ty::Unit => None,
    }
}

fn checked_class_index(ty: &Ty) -> Option<usize> {
    match ty {
        Ty::Class(class) => Some(*class),
        Ty::Borrow(Mutability::Shared, _) | Ty::Borrow(Mutability::Mut, _) => {
            checked_class_borrow(ty).map(|(class, _mutability)| class)
        }
        Ty::Int(_)
        | Ty::Bool
        | Ty::Param(_)
        | Ty::Record(_)
        | Ty::Array(_)
        | Ty::Slots(_)
        | Ty::Option(_)
        | Ty::OptionRaw(_)
        | Ty::Res(_)
        | Ty::Raw(_)
        | Ty::RawRecord(_)
        | Ty::Unit => None,
    }
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
            transfer_and_record(ctx, inner, ValueTransferSink::OptionPayload, None)?;
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
            transfer_and_record(ctx, inner, ValueTransferSink::OptionPayload, None)?;
        }
        ExprKind::SomeE(_)
        | ExprKind::IntLit(_)
        | ExprKind::BoolLit(_)
        | ExprKind::Var(_)
        | ExprKind::Unary { .. }
        | ExprKind::Binary { .. }
        | ExprKind::Call { .. }
        | ExprKind::Index { .. }
        | ExprKind::Len { .. }
        | ExprKind::RawOp { .. }
        | ExprKind::DeviceOp { .. }
        | ExprKind::ResOp { .. }
        | ExprKind::SlotOp { .. }
        | ExprKind::Widen { .. }
        | ExprKind::Narrow { .. }
        | ExprKind::IsSome { .. }
        | ExprKind::OptValue { .. }
        | ExprKind::OptTake { .. }
        | ExprKind::ArrayLit(_)
        | ExprKind::AllocArray { .. }
        | ExprKind::SelfField { .. }
        | ExprKind::SelfFieldLen { .. }
        | ExprKind::SelfFieldIndex { .. }
        | ExprKind::CtorCall { .. }
        | ExprKind::ClassField { .. }
        | ExprKind::RecordField { .. }
        | ExprKind::ClassFieldLen { .. }
        | ExprKind::ClassFieldIndex { .. }
        | ExprKind::TraitCall { .. }
        | ExprKind::MethodCall { .. }
        | ExprKind::Borrow { .. }
        | ExprKind::RecordLit { .. } => {
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
    let effect = CheckedOptionTake {
        key: EffectSiteKey {
            owner: ctx.call_owner.clone(),
            span: expression.span,
        },
        source: Place::local(option),
        source_span: *option_span,
        payload: ty.clone(),
    };
    ctx.ownership
        .insert_option_take(effect)
        .map_err(|duplicate| Diagnostic {
            name: "internal.check.duplicate_option_take".into(),
            title: format!(
                "duplicate affine-option take identity inside {}",
                duplicate.owner.render()
            ),
            span: duplicate.span,
            label: "owner and span must identify exactly one checked take".into(),
            notes: vec![],
        })?;
    Ok(ty)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DirectSlotPosition {
    ExplicitLocal,
    InferredLocal,
    Assignment,
    Return,
    FieldAssignment,
    Statement,
}

impl DirectSlotPosition {
    fn describe(self) -> &'static str {
        match self {
            Self::ExplicitLocal => "an explicit local initializer",
            Self::InferredLocal => "an inferred local initializer",
            Self::Assignment => "a local assignment",
            Self::Return => "a return value",
            Self::FieldAssignment => "a `self` field assignment",
            Self::Statement => "an expression statement",
        }
    }
}

/// Check a direct statement-level value boundary, admitting the deliberately
/// small slot-operation surface without making slot operations ordinary nested
/// expressions. Children of a slot operation go through `check_expr`, so a
/// take cannot hide inside a put value, index, call argument, or other child.
fn check_direct_slot_expr(
    ctx: &mut Ctx,
    expression: &mut Expr,
    expected: Option<Ty>,
    position: DirectSlotPosition,
) -> CResult<Ty> {
    let ty = if matches!(expression.kind, ExprKind::SlotOp { .. }) {
        check_slot_operation(ctx, expression, position)?
    } else {
        check_expr(ctx, expression, expected.clone())?
    };
    if let Some(expected) = expected {
        if ty != expected {
            return Err(Diagnostic {
                name: "type.mismatch".into(),
                title: format!(
                    "type mismatch: expected `{}`, found `{}`",
                    expected.name(),
                    ty.clone().name()
                ),
                span: expression.span,
                label: format!("this has type `{}`", ty.name()),
                notes: vec![],
            });
        }
    }
    Ok(ty)
}

fn slot_operation_position(op: &SlotOp, position: DirectSlotPosition, span: Span) -> CResult<()> {
    let admitted = match op {
        SlotOp::Alloc { .. } => matches!(
            position,
            DirectSlotPosition::ExplicitLocal | DirectSlotPosition::FieldAssignment
        ),
        SlotOp::Take => !matches!(position, DirectSlotPosition::Statement),
        SlotOp::Put => position == DirectSlotPosition::Statement,
    };
    if admitted {
        return Ok(());
    }
    Err(Diagnostic {
        name: "slots.operation_position".into(),
        title: format!("`{}` is not admitted as {}", op.name(), position.describe()),
        span,
        label: match op {
            SlotOp::Alloc { .. } => {
                "allocate directly into an explicit `slots<T>` local or `self` field"
            }
            SlotOp::Take => "move the result directly into a local/field or return it",
            SlotOp::Put => "use `slot_put(...)` as a statement",
        }
        .into(),
        notes: vec![(
            "note".into(),
            "direct positions give the retained control action one exact ownership sink".into(),
        )],
    })
}

fn slot_operation_arity(op: &SlotOp, args: &[Expr], span: Span) -> CResult<()> {
    if args.len() == op.arity() {
        return Ok(());
    }
    Err(Diagnostic {
        name: "internal.check.slot_operation_arity".into(),
        title: format!(
            "checked `{}` has {} argument(s), expected {}",
            op.name(),
            args.len(),
            op.arity()
        ),
        span,
        label: "the sealed slot transition requires exact arity".into(),
        notes: vec![],
    })
}

/// Resolve the unique slot loan used only by `slot_take`/`slot_put`.
///
/// This is intentionally not part of ordinary `ExprKind::Borrow` checking.
/// It admits `&mut local` and `&mut self.field`, and nothing else, so adding
/// owner slots does not widen general mutable field borrows or call loans.
fn resolve_slot_container(ctx: &mut Ctx, argument: &mut Expr) -> CResult<(Place, Ty)> {
    let span = argument.span;
    let ExprKind::Borrow {
        array,
        field,
        mutable,
    } = &argument.kind
    else {
        return Err(Diagnostic {
            name: "slots.container_borrow".into(),
            title: "slot operation needs an explicit unique container borrow".into(),
            span,
            label: "write `&mut slots_local` or `&mut self.slot_field`".into(),
            notes: vec![],
        });
    };
    if !*mutable {
        return Err(Diagnostic {
            name: "slots.container_mutability".into(),
            title: "slot operation received a shared container borrow".into(),
            span,
            label: "taking or putting changes cell occupancy; write `&mut`".into(),
            notes: vec![],
        });
    }

    let (place, container_ty) = match field.as_deref() {
        Some(field) if array == "self" => {
            let ty = ctx.self_field_ty(field, span, true)?;
            ctx.require_field_init(field, span)?;
            (Place::field("self", field), ty)
        }
        Some(field) => {
            return Err(Diagnostic {
                name: "slots.container_place".into(),
                title: format!("`{array}.{field}` is not an admitted slot-operation place"),
                span,
                label: "only a mutable local or the current receiver's direct field is admitted"
                    .into(),
                notes: vec![(
                    "note".into(),
                    "this operation-local exception does not authorize general mutable class-field borrows"
                        .into(),
                )],
            });
        }
        None => {
            reject_exposed_owner(ctx, array, span)?;
            let place = Place::local(array);
            if ctx.is_moved(&place) {
                return Err(moved_out(ctx, &place, span, "borrow"));
            }
            let Some(binding) = ctx.vars.get(array.as_str()) else {
                return Err(Diagnostic {
                    name: "type.unknown_variable".into(),
                    title: format!("unknown variable `{array}`"),
                    span,
                    label: "not declared".into(),
                    notes: vec![],
                });
            };
            if !binding.initialized {
                return Err(Diagnostic {
                    name: "type.uninitialized".into(),
                    title: format!("`{array}` may be used before initialization"),
                    span,
                    label: "slot operations need a live container owner".into(),
                    notes: vec![],
                });
            }
            if !binding.mutable {
                return Err(Diagnostic {
                    name: "slots.container_mutability".into(),
                    title: format!("slot container `{array}` is immutable"),
                    span,
                    label: "declare it `mut slots<...>` before taking or putting".into(),
                    notes: vec![],
                });
            }
            (place, binding.ty.clone())
        }
    };
    let Ty::Slots(payload) = container_ty else {
        return Err(Diagnostic {
            name: "slots.container_type".into(),
            title: format!("`{}` is not an owner-slot container", place.render()),
            span,
            label: format!("this has type `{}`", container_ty.name()),
            notes: vec![],
        });
    };
    slot_payload_ty(&payload, span)?;
    let payload = *payload;
    argument.ty = Some(Ty::borrow(Mutability::Mut, Ty::slots(payload.clone())));
    Ok((place, payload))
}

fn check_slot_operation(
    ctx: &mut Ctx,
    expression: &mut Expr,
    position: DirectSlotPosition,
) -> CResult<Ty> {
    let span = expression.span;
    let ExprKind::SlotOp { op, op_span, args } = &mut expression.kind else {
        unreachable!("slot checker is called only for a slot operation")
    };
    slot_operation_position(op, position, span)?;
    slot_operation_arity(op, args, span)?;
    let op = op.clone();
    let op_span = *op_span;
    let key = EffectSiteKey {
        owner: ctx.call_owner.clone(),
        span,
    };
    let (payload, result_ty, kind) = match op {
        SlotOp::Alloc { elem } => {
            slot_payload_ty(&elem, op_span)?;
            check_expr(ctx, &mut args[0], Some(Ty::Int(IntTy::U64)))?;
            (
                elem.clone(),
                Ty::slots(elem),
                CheckedSlotTransitionKind::Alloc {
                    length_ty: Ty::Int(IntTy::U64),
                    length_span: args[0].span,
                },
            )
        }
        SlotOp::Take => {
            let (container, payload) = resolve_slot_container(ctx, &mut args[0])?;
            check_expr(ctx, &mut args[1], Some(Ty::Int(IntTy::U64)))?;
            (
                payload.clone(),
                payload,
                CheckedSlotTransitionKind::Take {
                    container,
                    container_span: args[0].span,
                    index_ty: Ty::Int(IntTy::U64),
                    index_span: args[1].span,
                },
            )
        }
        SlotOp::Put => {
            let (container, payload) = resolve_slot_container(ctx, &mut args[0])?;
            check_expr(ctx, &mut args[1], Some(Ty::Int(IntTy::U64)))?;
            check_expr(ctx, &mut args[2], Some(payload.clone()))?;
            let sink = ValueTransferSink::SlotPut(container.clone());
            transfer_and_record(
                ctx,
                &args[2],
                sink.clone(),
                Some(("be stored in owner slots", args[2].span)),
            )?;
            let value_transfer = ValueTransferKey {
                owner: ctx.call_owner.clone(),
                span: args[2].span,
                sink,
            };
            (
                payload.clone(),
                Ty::Unit,
                CheckedSlotTransitionKind::Put {
                    container,
                    container_span: args[0].span,
                    index_ty: Ty::Int(IntTy::U64),
                    index_span: args[1].span,
                    value_span: args[2].span,
                    value_transfer,
                },
            )
        }
    };
    expression.ty = Some(result_ty.clone());
    ctx.ownership
        .insert_slot_transition(CheckedSlotTransition {
            key,
            op_span,
            payload,
            result_ty: result_ty.clone(),
            kind,
        })
        .map_err(|duplicate| Diagnostic {
            name: "internal.check.duplicate_slot_transition".into(),
            title: format!(
                "duplicate slot-transition identity inside {}",
                duplicate.owner.render()
            ),
            span: duplicate.span,
            label: "owner and operation span must identify exactly one slot transition".into(),
            notes: vec![],
        })?;
    Ok(result_ty)
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
        ExprKind::SlotOp { op, .. } => {
            return Err(Diagnostic {
                name: "slots.operation_position".into(),
                title: format!("`{}` is nested in an unsupported expression", op.name()),
                span,
                label: "owner-slot operations require one direct statement-level ownership sink"
                    .into(),
                notes: vec![(
                    "note".into(),
                    "allocate into an explicit slot local or `self` field, bind/assign/return a take directly, and use put as a statement"
                        .into(),
                )],
            });
        }
        ExprKind::IntLit(n) => {
            let t = match expected {
                Some(
                    t @ (Ty::Int(
                        IntTy::U8
                        | IntTy::U16
                        | IntTy::U32
                        | IntTy::U64
                        | IntTy::I8
                        | IntTy::I16
                        | IntTy::I32
                        | IntTy::I64,
                    )
                    | Ty::Param(_)),
                ) => t,
                Some(
                    other @ (Ty::Int(IntTy::TParam(_))
                    | Ty::Bool
                    | Ty::Class(_)
                    | Ty::Record(_)
                    | Ty::Array(_)
                    | Ty::Slots(_)
                    | Ty::Option(_)
                    | Ty::OptionRaw(_)
                    | Ty::Res(_)
                    | Ty::Raw(_)
                    | Ty::RawRecord(_)
                    | Ty::Borrow(..)
                    | Ty::Unit),
                ) => {
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
                if let Ty::Slots(payload) = &v.ty {
                    if !v.initialized {
                        return Err(Diagnostic {
                            name: "type.uninitialized".into(),
                            title: format!("`{name}` may be moved before initialization"),
                            span,
                            label: "owner slots need a live allocation before a whole-owner move"
                                .into(),
                            notes: vec![],
                        });
                    }
                    slot_payload_ty(payload, span)?;
                    if matches!(&expected, Some(want) if *want == v.ty) {
                        e.ty = Some(v.ty.clone());
                        return Ok(v.ty.clone());
                    }
                    return Err(Diagnostic {
                        name: "slots.owner_value_position".into(),
                        title: format!("owner-slot local `{name}` used as an ordinary value"),
                        span,
                        label: "move the whole owner directly into a local or `self` field".into(),
                        notes: vec![(
                            "note".into(),
                            "observe `.len`, or mutate occupancy with `slot_take` and `slot_put`"
                                .into(),
                        )],
                    });
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
            if ctx
                .vars
                .get(array.as_str())
                .is_some_and(|binding| binding.ty.as_slots().is_some())
            {
                return Err(slot_index_unsupported(*array_span));
            }
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
            if let Some(binding) = ctx
                .vars
                .get(array.as_str())
                .filter(|binding| binding.ty.as_owned_slots().is_some())
            {
                reject_exposed_owner(ctx, array, span)?;
                let place = Place::local(array);
                if ctx.is_moved(&place) {
                    return Err(moved_out(ctx, &place, span, "length observation"));
                }
                if !binding.initialized {
                    return Err(Diagnostic {
                        name: "type.uninitialized".into(),
                        title: format!("owner-slot local `{array}` may be uninitialized"),
                        span,
                        label: "`.len` needs a live slot allocation".into(),
                        notes: vec![],
                    });
                }
                let payload = binding
                    .ty
                    .as_owned_slots()
                    .expect("filtered to an owner-slot binding");
                slot_payload_ty(payload, span)?;
                e.ty = Some(Ty::Int(IntTy::U64));
                return Ok(Ty::Int(IntTy::U64));
            }
            array_elem_ty(ctx, array, span)?;
            Ty::Int(IntTy::U64)
        }
        ExprKind::Widen { target, arg } => {
            let target_ty = legacy_integer_ty(*target);
            let src = match check_expr(ctx, arg, None) {
                Ok(
                    ty @ (Ty::Int(
                        IntTy::U8
                        | IntTy::U16
                        | IntTy::U32
                        | IntTy::U64
                        | IntTy::I8
                        | IntTy::I16
                        | IntTy::I32
                        | IntTy::I64,
                    )
                    | Ty::Param(_)),
                ) => ty,
                Ok(
                    other @ (Ty::Int(IntTy::TParam(_))
                    | Ty::Bool
                    | Ty::Class(_)
                    | Ty::Record(_)
                    | Ty::Array(_)
                    | Ty::Slots(_)
                    | Ty::Option(_)
                    | Ty::OptionRaw(_)
                    | Ty::Res(_)
                    | Ty::Raw(_)
                    | Ty::RawRecord(_)
                    | Ty::Borrow(..)
                    | Ty::Unit),
                ) => {
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
                Ok(
                    Ty::Int(
                        IntTy::U8
                        | IntTy::U16
                        | IntTy::U32
                        | IntTy::U64
                        | IntTy::I8
                        | IntTy::I16
                        | IntTy::I32
                        | IntTy::I64,
                    )
                    | Ty::Param(_),
                ) => {}
                Ok(
                    other @ (Ty::Int(IntTy::TParam(_))
                    | Ty::Bool
                    | Ty::Class(_)
                    | Ty::Record(_)
                    | Ty::Array(_)
                    | Ty::Slots(_)
                    | Ty::Option(_)
                    | Ty::OptionRaw(_)
                    | Ty::Res(_)
                    | Ty::Raw(_)
                    | Ty::RawRecord(_)
                    | Ty::Borrow(..)
                    | Ty::Unit),
                ) => {
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
                ExprKind::Var(_)
                | ExprKind::IntLit(_)
                | ExprKind::BoolLit(_)
                | ExprKind::Unary { .. }
                | ExprKind::Binary { .. }
                | ExprKind::Call { .. }
                | ExprKind::Index { .. }
                | ExprKind::Len { .. }
                | ExprKind::RawOp { .. }
                | ExprKind::DeviceOp { .. }
                | ExprKind::ResOp { .. }
                | ExprKind::SlotOp { .. }
                | ExprKind::Widen { .. }
                | ExprKind::Narrow { .. }
                | ExprKind::IsSome { .. }
                | ExprKind::OptValue { .. }
                | ExprKind::OptTake { .. }
                | ExprKind::SomeE(_)
                | ExprKind::NoneE
                | ExprKind::ArrayLit(_)
                | ExprKind::AllocArray { .. }
                | ExprKind::SelfField { .. }
                | ExprKind::SelfFieldLen { .. }
                | ExprKind::SelfFieldIndex { .. }
                | ExprKind::CtorCall { .. }
                | ExprKind::ClassField { .. }
                | ExprKind::RecordField { .. }
                | ExprKind::ClassFieldLen { .. }
                | ExprKind::ClassFieldIndex { .. }
                | ExprKind::TraitCall { .. }
                | ExprKind::MethodCall { .. }
                | ExprKind::Borrow { .. }
                | ExprKind::RecordLit { .. } => None,
            };
            if let Some(option) = affine_name {
                let (option_ty, _) =
                    check_affine_option_local(ctx, &option, operand.span, "is_some")?;
                operand.ty = Some(option_ty);
            } else {
                match check_expr(ctx, operand, None)? {
                    Ty::Option(_) | Ty::OptionRaw(_) => {}
                    other @ (Ty::Int(_)
                    | Ty::Bool
                    | Ty::Param(_)
                    | Ty::Class(_)
                    | Ty::Record(_)
                    | Ty::Array(_)
                    | Ty::Slots(_)
                    | Ty::Res(_)
                    | Ty::Raw(_)
                    | Ty::RawRecord(_)
                    | Ty::Borrow(..)
                    | Ty::Unit) => {
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
                other @ (Ty::Int(_)
                | Ty::Bool
                | Ty::Param(_)
                | Ty::Class(_)
                | Ty::Record(_)
                | Ty::Array(_)
                | Ty::Slots(_)
                | Ty::Res(_)
                | Ty::Raw(_)
                | Ty::RawRecord(_)
                | Ty::Borrow(..)
                | Ty::Unit) => {
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
                Ty::Slots(_) => {
                    return Err(slots_unsupported(span, "slot field read"));
                }
                other @ (Ty::Bool
                | Ty::Class(_)
                | Ty::Record(_)
                | Ty::Option(_)
                | Ty::OptionRaw(_)
                | Ty::Res(_)
                | Ty::Raw(_)
                | Ty::RawRecord(_)
                | Ty::Borrow(..)
                | Ty::Unit) => {
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
            let field_ty = meta
                .fields
                .iter()
                .find(|(name, _)| name == field)
                .map(|(_, ty)| ty.clone())
                .ok_or_else(|| Diagnostic {
                    name: "type.unknown_field".into(),
                    title: format!("`{}` has no field `{field}`", meta.name),
                    span,
                    label: "unknown record field".into(),
                    notes: vec![],
                })?;
            if matches!(field_ty, Ty::Slots(_)) {
                return Err(slots_unsupported(span, "slot record-field read"));
            }
            field_ty
        }
        ExprKind::ClassFieldLen { obj, field } => {
            let ci = class_of(ctx, obj, span)?;
            let meta = &ctx.class_metas[ci];
            let Some((_name, field_ty)) = meta.fields.iter().find(|(n, _ty)| n == field) else {
                return Err(Diagnostic {
                    name: "type.mismatch".into(),
                    title: format!("`.len` needs an array field; `{field}` is not one"),
                    span,
                    label: "not an array field".into(),
                    notes: vec![],
                });
            };
            match field_ty {
                Ty::Array(..) => Ty::Int(IntTy::U64),
                Ty::Slots(payload) => {
                    reject_exposed_owner(ctx, obj, span)?;
                    let place = Place::local(obj);
                    if ctx.is_moved(&place) {
                        return Err(moved_out(ctx, &place, span, "field length observation"));
                    }
                    if !ctx
                        .vars
                        .get(obj.as_str())
                        .is_some_and(|binding| binding.initialized)
                    {
                        return Err(Diagnostic {
                            name: "type.uninitialized".into(),
                            title: format!("class receiver `{obj}` may be uninitialized"),
                            span,
                            label: "slot-field `.len` needs a live receiver".into(),
                            notes: vec![],
                        });
                    }
                    slot_payload_ty(payload, span)?;
                    Ty::Int(IntTy::U64)
                }
                Ty::Int(_)
                | Ty::Bool
                | Ty::Param(_)
                | Ty::Class(_)
                | Ty::Record(_)
                | Ty::Option(_)
                | Ty::OptionRaw(_)
                | Ty::Res(_)
                | Ty::Raw(_)
                | Ty::RawRecord(_)
                | Ty::Borrow(..)
                | Ty::Unit => {
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
            let Some((_name, field_ty)) = meta.fields.iter().find(|(n, _ty)| n == field) else {
                return Err(Diagnostic {
                    name: "type.mismatch".into(),
                    title: format!("`{field}` is not an array field"),
                    span,
                    label: "not indexable".into(),
                    notes: vec![],
                });
            };
            let elem = match field_ty {
                Ty::Array(element) => element.clone(),
                Ty::Slots(_) => {
                    return Err(slot_index_unsupported(span));
                }
                Ty::Int(_)
                | Ty::Bool
                | Ty::Param(_)
                | Ty::Class(_)
                | Ty::Record(_)
                | Ty::Option(_)
                | Ty::OptionRaw(_)
                | Ty::Res(_)
                | Ty::Raw(_)
                | Ty::RawRecord(_)
                | Ty::Borrow(..)
                | Ty::Unit => {
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
                    other @ (Ty::Int(_)
                    | Ty::Bool
                    | Ty::Param(_)
                    | Ty::Class(_)
                    | Ty::Record(_)
                    | Ty::Array(_)
                    | Ty::Slots(_)
                    | Ty::Option(_)
                    | Ty::OptionRaw(_)
                    | Ty::Res(_)
                    | Ty::Raw(_)
                    | Ty::RawRecord(_)
                    | Ty::Borrow(..)
                    | Ty::Unit) => other,
                };
                match t {
                    Ty::Param(parameter) if parameter.index() == 0 => {
                        Ty::Param(TypeParamId::from_legacy(pidx))
                    }
                    Ty::Int(IntTy::TParam(0)) => Ty::Param(TypeParamId::from_legacy(pidx)),
                    Ty::Array(payload) => Ty::array(remap_payload(*payload)),
                    Ty::Slots(payload) => Ty::slots(remap_payload(*payload)),
                    Ty::Option(payload) => Ty::Option(Box::new(remap_payload(*payload))),
                    // A borrow's referent is remapped in place: `&[<T>]` is
                    // the same remap `[<T>]` gets, one marker further out.
                    Ty::Borrow(mutability, referent) => Ty::borrow(
                        mutability,
                        match *referent {
                            Ty::Array(payload) => Ty::array(remap_payload(*payload)),
                            Ty::Slots(payload) => Ty::slots(remap_payload(*payload)),
                            other @ (Ty::Int(_)
                            | Ty::Bool
                            | Ty::Param(_)
                            | Ty::Class(_)
                            | Ty::Record(_)
                            | Ty::Option(_)
                            | Ty::OptionRaw(_)
                            | Ty::Res(_)
                            | Ty::Raw(_)
                            | Ty::RawRecord(_)
                            | Ty::Borrow(..)
                            | Ty::Unit) => other,
                        },
                    ),
                    other @ (Ty::Int(_)
                    | Ty::Bool
                    | Ty::Param(_)
                    | Ty::Class(_)
                    | Ty::Record(_)
                    | Ty::OptionRaw(_)
                    | Ty::Res(_)
                    | Ty::Raw(_)
                    | Ty::RawRecord(_)
                    | Ty::Unit) => other,
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
            let raw = Ty::Raw(IntTy::U8);
            let u8t = Ty::Int(IntTy::U8);
            let u64t = Ty::Int(IntTy::U64);
            let shared = Ty::borrow(Mutability::Shared, Ty::Res(ResKind::RawSpan));
            let unique = Ty::borrow(Mutability::Mut, Ty::Res(ResKind::RawSpan));
            let raw_span = Ty::Res(ResKind::RawSpan);
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
                RawOp::Offset
                | RawOp::Load8
                | RawOp::Store8
                | RawOp::Copy
                | RawOp::CastRecord(_)
                | RawOp::PointerOffsetRecord(_)
                | RawOp::IntoFreeHeader
                | RawOp::FromFreeHeader
                | RawOp::HeaderInit
                | RawOp::HeaderSize
                | RawOp::HeaderNext
                | RawOp::HeaderClear => None,
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
                        raw_span.clone()
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
            let moved_before = ctx.moved.clone();
            let mut transfers = vec![None; args.len()];
            for (index, (arg, w)) in args.iter_mut().zip(&want).enumerate() {
                require_explicit_borrow(ctx, arg, w.clone())?;
                check_expr(ctx, arg, Some(w.clone()))?;
                if matches!(w, Ty::Res(_)) {
                    transfers[index] = Some(transfer(ctx, arg, None)?);
                }
            }
            let result = match op {
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
                        raw_span
                    }
                }
                RawOp::CellInitU64 | RawOp::CellDropU64 => Ty::Unit,
                RawOp::CellReadU64 | RawOp::CellTakeU64 => u64t,
                RawOp::IntoCellRecord(ri) => Ty::Res(ResKind::PointsToRecord(ri)),
                RawOp::FromCellRecord(_) => raw_span,
                RawOp::CellInitRecord(_) | RawOp::CellDropRecord(_) => Ty::Unit,
                RawOp::CellReadRecord(ri) | RawOp::CellTakeRecord(ri) => Ty::Record(ri),
                RawOp::CastRecord(ri) => Ty::RawRecord(ri),
                RawOp::PointerOffsetRecord(_) => u64t,
                RawOp::IntoFreeHeader => free_header,
                RawOp::FromFreeHeader => free_block,
                RawOp::HeaderInit | RawOp::HeaderClear => Ty::Unit,
                RawOp::HeaderSize | RawOp::HeaderNext => u64t,
            };
            record_sealed_operation(
                ctx,
                CheckedSealedTarget::Raw(op),
                args,
                &transfers,
                &moved_before,
                result.clone(),
                span,
            )?;
            result
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
            let uart = Ty::borrow(Mutability::Mut, Ty::Res(ResKind::Uart));
            let want = match op {
                DeviceOp::UartStatus => vec![uart],
                DeviceOp::UartWrite => vec![Ty::Int(IntTy::U8), uart],
            };
            let moved_before = ctx.moved.clone();
            for (arg, expected) in args.iter_mut().zip(want) {
                require_explicit_borrow(ctx, arg, expected.clone())?;
                check_expr(ctx, arg, Some(expected))?;
            }
            let result = match op {
                DeviceOp::UartStatus => Ty::Int(IntTy::U8),
                DeviceOp::UartWrite => Ty::Unit,
            };
            record_sealed_operation(
                ctx,
                CheckedSealedTarget::Device(op),
                args,
                &vec![None; args.len()],
                &moved_before,
                result.clone(),
                span,
            )?;
            result
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
            let moved_before = ctx.moved.clone();
            let mut transfers = vec![None; args.len()];
            let result = match op {
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
                    for (index, arg) in args.iter_mut().enumerate() {
                        check_expr(ctx, arg, Some(want.clone()))?;
                        transfers[index] = Some(transfer(ctx, arg, None)?);
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
                    transfers[0] = Some(transfer(ctx, &args[0], None)?);
                    Ty::Res(ResKind::AllocatorState)
                }
                // The aggregate may unfold only when its free map once
                // again contains the complete root; that condition is a VC.
                ResOp::AllocatorDestroy => {
                    let want = Ty::Res(ResKind::AllocatorState);
                    check_expr(ctx, &mut args[0], Some(want))?;
                    transfers[0] = Some(transfer(ctx, &args[0], None)?);
                    Ty::Res(ResKind::RawSpan)
                }
                ResOp::AllocatorTake => {
                    let want = Ty::borrow(Mutability::Mut, Ty::Res(ResKind::AllocatorState));
                    require_explicit_borrow(ctx, &args[0], want.clone())?;
                    check_expr(ctx, &mut args[0], Some(want))?;
                    check_expr(ctx, &mut args[1], Some(Ty::Int(IntTy::U64)))?;
                    Ty::Res(ResKind::BlockLease)
                }
                ResOp::AllocatorPut => {
                    let state = Ty::borrow(Mutability::Mut, Ty::Res(ResKind::AllocatorState));
                    require_explicit_borrow(ctx, &args[0], state.clone())?;
                    check_expr(ctx, &mut args[0], Some(state))?;
                    let lease = Ty::Res(ResKind::BlockLease);
                    check_expr(ctx, &mut args[1], Some(lease))?;
                    transfers[1] = Some(transfer(ctx, &args[1], None)?);
                    Ty::Unit
                }
                ResOp::AllocatorTakeFree => {
                    let want = Ty::borrow(Mutability::Mut, Ty::Res(ResKind::AllocatorState));
                    require_explicit_borrow(ctx, &args[0], want.clone())?;
                    check_expr(ctx, &mut args[0], Some(want))?;
                    check_expr(ctx, &mut args[1], Some(Ty::Int(IntTy::U64)))?;
                    Ty::Res(ResKind::FreeBlock)
                }
                ResOp::AllocatorPutFree => {
                    let state = Ty::borrow(Mutability::Mut, Ty::Res(ResKind::AllocatorState));
                    require_explicit_borrow(ctx, &args[0], state.clone())?;
                    check_expr(ctx, &mut args[0], Some(state))?;
                    let block = Ty::Res(ResKind::FreeBlock);
                    check_expr(ctx, &mut args[1], Some(block))?;
                    transfers[1] = Some(transfer(ctx, &args[1], None)?);
                    Ty::Unit
                }
                ResOp::AllocatorTakeHeader => {
                    let want = Ty::borrow(Mutability::Mut, Ty::Res(ResKind::AllocatorState));
                    require_explicit_borrow(ctx, &args[0], want.clone())?;
                    check_expr(ctx, &mut args[0], Some(want))?;
                    check_expr(ctx, &mut args[1], Some(Ty::Int(IntTy::U64)))?;
                    Ty::Res(ResKind::FreeHeader)
                }
                ResOp::AllocatorPutHeader => {
                    let state = Ty::borrow(Mutability::Mut, Ty::Res(ResKind::AllocatorState));
                    require_explicit_borrow(ctx, &args[0], state.clone())?;
                    check_expr(ctx, &mut args[0], Some(state))?;
                    let header = Ty::Res(ResKind::FreeHeader);
                    check_expr(ctx, &mut args[1], Some(header))?;
                    transfers[1] = Some(transfer(ctx, &args[1], None)?);
                    Ty::Unit
                }
                ResOp::AllocatorStepHeader => {
                    let want = Ty::borrow(Mutability::Mut, Ty::Res(ResKind::AllocatorState));
                    require_explicit_borrow(ctx, &args[0], want.clone())?;
                    check_expr(ctx, &mut args[0], Some(want))?;
                    check_expr(ctx, &mut args[1], Some(Ty::Int(IntTy::U64)))?;
                    check_expr(ctx, &mut args[2], Some(Ty::Int(IntTy::U64)))?;
                    Ty::Res(ResKind::FreeHeader)
                }
                ResOp::FreeBlockSplit => {
                    let block = Ty::borrow(Mutability::Mut, Ty::Res(ResKind::FreeBlock));
                    require_explicit_borrow(ctx, &args[0], block.clone())?;
                    check_expr(ctx, &mut args[0], Some(block))?;
                    check_expr(ctx, &mut args[1], Some(Ty::Int(IntTy::U64)))?;
                    Ty::Res(ResKind::FreeBlock)
                }
                ResOp::FreeBlockJoin => {
                    let block = Ty::Res(ResKind::FreeBlock);
                    for (index, arg) in args.iter_mut().enumerate() {
                        check_expr(ctx, arg, Some(block.clone()))?;
                        transfers[index] = Some(transfer(ctx, arg, None)?);
                    }
                    Ty::Res(ResKind::FreeBlock)
                }
                ResOp::FreeBlockLease => {
                    let block = Ty::Res(ResKind::FreeBlock);
                    check_expr(ctx, &mut args[0], Some(block))?;
                    transfers[0] = Some(transfer(ctx, &args[0], None)?);
                    Ty::Res(ResKind::BlockLease)
                }
                ResOp::BlockLeaseFree => {
                    let lease = Ty::Res(ResKind::BlockLease);
                    check_expr(ctx, &mut args[0], Some(lease))?;
                    transfers[0] = Some(transfer(ctx, &args[0], None)?);
                    Ty::Res(ResKind::FreeBlock)
                }
                ResOp::ResourceMapEmpty => match expected {
                    Some(Ty::Res(kind)) => match kind {
                        ResKind::ResourceMapPointsToU64 | ResKind::ResourceMapPointsToRecord(_) => {
                            Ty::Res(kind)
                        }
                        ResKind::RawSpan
                        | ResKind::PointsToU64
                        | ResKind::PointsToRecord(_)
                        | ResKind::OpenFile
                        | ResKind::PosixWorld
                        | ResKind::Uart
                        | ResKind::SystemDealloc
                        | ResKind::AllocatorState
                        | ResKind::BlockLease
                        | ResKind::LeasedPointsToU64
                        | ResKind::FreeBlock
                        | ResKind::FreeHeader => Ty::Res(ResKind::ResourceMapPointsToU64),
                    },
                    Some(
                        Ty::Int(_)
                        | Ty::Bool
                        | Ty::Param(_)
                        | Ty::Class(_)
                        | Ty::Record(_)
                        | Ty::Array(_)
                        | Ty::Slots(_)
                        | Ty::Option(_)
                        | Ty::OptionRaw(_)
                        | Ty::Raw(_)
                        | Ty::RawRecord(_)
                        | Ty::Borrow(..)
                        | Ty::Unit,
                    )
                    | None => Ty::Res(ResKind::ResourceMapPointsToU64),
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
                    Ty::Res(match map_kind {
                        ResKind::ResourceMapPointsToU64 => ResKind::PointsToU64,
                        ResKind::ResourceMapPointsToRecord(ri) => ResKind::PointsToRecord(ri),
                        ResKind::RawSpan
                        | ResKind::PointsToU64
                        | ResKind::PointsToRecord(_)
                        | ResKind::OpenFile
                        | ResKind::PosixWorld
                        | ResKind::Uart
                        | ResKind::SystemDealloc
                        | ResKind::AllocatorState
                        | ResKind::BlockLease
                        | ResKind::LeasedPointsToU64
                        | ResKind::FreeBlock
                        | ResKind::FreeHeader => unreachable!(),
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
                        ResKind::RawSpan
                        | ResKind::PointsToU64
                        | ResKind::PointsToRecord(_)
                        | ResKind::OpenFile
                        | ResKind::PosixWorld
                        | ResKind::Uart
                        | ResKind::SystemDealloc
                        | ResKind::AllocatorState
                        | ResKind::BlockLease
                        | ResKind::LeasedPointsToU64
                        | ResKind::FreeBlock
                        | ResKind::FreeHeader => unreachable!(),
                    });
                    check_expr(ctx, &mut args[2], Some(cell))?;
                    transfers[2] = Some(transfer(ctx, &args[2], None)?);
                    Ty::Unit
                }
            };
            record_sealed_operation(
                ctx,
                CheckedSealedTarget::Resource(op),
                args,
                &transfers,
                &moved_before,
                result.clone(),
                span,
            )?;
            result
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
            if let Ty::Slots(payload) = &fty {
                ctx.require_field_init(field, span)?;
                slot_payload_ty(payload, span)?;
                if matches!(&expected, Some(want) if *want == fty) {
                    e.ty = Some(fty.clone());
                    return Ok(fty);
                }
                return Err(Diagnostic {
                    name: "slots.owner_value_position".into(),
                    title: format!("owner-slot field `self.{field}` used as an ordinary value"),
                    span,
                    label: "move the whole owner directly into a local or replacement field".into(),
                    notes: vec![(
                        "note".into(),
                        "ordinary field reads would copy an affine slot allocation".into(),
                    )],
                });
            }
            if ctx.in_init {
                ctx.require_field_init(field, span)?;
            }
            fty
        }
        ExprKind::SelfFieldLen { field } => {
            let fty = ctx.self_field_ty(field, span, false)?;
            if let Ty::Slots(payload) = &fty {
                ctx.require_field_init(field, span)?;
                slot_payload_ty(payload, span)?;
                e.ty = Some(Ty::Int(IntTy::U64));
                return Ok(Ty::Int(IntTy::U64));
            }
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
            if matches!(fty, Ty::Slots(_)) {
                return Err(slot_index_unsupported(span));
            }
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
            let moved_before = ctx.moved.clone();
            let mut transfers = Vec::with_capacity(args.len());
            for (arg, p) in args.iter_mut().zip(&params) {
                // A constructor returns a class, and a class may hold
                // resource fields (ADR 0029) — so it is exactly a container
                // a brand could leave in.
                let escapes = launders.then(|| ("be passed to a constructor", arg.span));
                check_user_call_argument(ctx, arg, &p.ty)?;
                transfers.push(transfer(ctx, arg, escapes)?);
            }
            record_call_transitions(
                ctx,
                CallTarget::Constructor {
                    class: class.clone(),
                    init: init.clone(),
                },
                &params,
                args,
                &transfers,
                None,
                &moved_before,
                span,
            )?;
            ctx.calls.push(CallOwner::Constructor {
                class: class.clone(),
                init: init.clone(),
            });
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
                Some(v) => match checked_class_borrow(&v.ty) {
                    Some((ci, mutability)) => (ci, mutability == Mutability::Mut, false),
                    None => {
                        return Err(Diagnostic {
                            name: "type.not_a_class".into(),
                            title: format!("`{recv}` is not a class value"),
                            span: *recv_span,
                            label: format!("this has type `{}`", v.ty.clone().name()),
                            notes: vec![],
                        });
                    }
                },
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
            // A method call is an implicit borrow of its receiver. Resolve
            // that borrow through the same place-state table as an explicit
            // `&item`: looking the type up in `vars` is not enough, because a
            // move deliberately leaves the declaration there while killing
            // the value it used to contain.
            let receiver_place = Place::local(recv);
            if ctx.is_moved(&receiver_place) {
                return Err(moved_out(
                    ctx,
                    &receiver_place,
                    *recv_span,
                    "method receiver",
                ));
            }
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
                Ty::Res(_)
                | Ty::Raw(_)
                | Ty::RawRecord(_)
                | Ty::OptionRaw(_)
                | Ty::Array(_)
                | Ty::Borrow(..) => true,
                Ty::Class(ci) => class_holds_storage(ctx.class_metas, ci, 0),
                Ty::Record(ri) => record_holds_storage(ctx.record_metas, ri),
                Ty::Slots(_) => {
                    return Err(slots_unsupported(span, "method return type"));
                }
                Ty::Int(_) | Ty::Bool | Ty::Param(_) | Ty::Option(_) | Ty::Unit => false,
            };
            let moved_before = ctx.moved.clone();
            let mut transfers = Vec::with_capacity(args.len());
            for (arg, p) in args.iter_mut().zip(&params) {
                check_user_call_argument(ctx, arg, &p.ty)?;
                transfers.push(transfer(
                    ctx,
                    arg,
                    launders.then(|| ("be passed to a method", arg.span)),
                )?);
            }
            record_call_transitions(
                ctx,
                CallTarget::Method {
                    class: ctx.class_metas[ci].name.clone(),
                    method: method.clone(),
                },
                &params,
                args,
                &transfers,
                Some((
                    receiver_place,
                    ctx.class_metas[ci].name.clone(),
                    if self_kind == SelfKind::Mut {
                        Mutability::Mut
                    } else {
                        Mutability::Shared
                    },
                    *recv_span,
                    Ty::Class(ci),
                )),
                &moved_before,
                span,
            )?;
            ctx.calls.push(CallOwner::Method {
                class: ctx.class_metas[ci].name.clone(),
                method: method.clone(),
            });
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
            Some(
                Ty::Int(_)
                | Ty::Bool
                | Ty::Param(_)
                | Ty::Class(_)
                | Ty::Record(_)
                | Ty::Slots(_)
                | Ty::Option(_)
                | Ty::OptionRaw(_)
                | Ty::Res(_)
                | Ty::Raw(_)
                | Ty::RawRecord(_)
                | Ty::Borrow(..)
                | Ty::Unit,
            )
            | None => {
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
                let p = field
                    .as_deref()
                    .map_or_else(|| Place::local(array), |f| Place::field(array, f));
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
                        Some((ci, _member_is_mutable)) => {
                            Ty::borrow(Mutability::Shared, Ty::Class(ci))
                        }
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
                    Ty::Slots(_) => Err(slots_unsupported(span, "slot-field borrow")),
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
                    let (src_mut, is_local) = match &v.ty {
                        Ty::Res(_) => (Mutability::Mut, true),
                        Ty::Borrow(Mutability::Shared, referent) => match referent.as_ref() {
                            Ty::Res(_) => (Mutability::Shared, false),
                            Ty::Int(_)
                            | Ty::Bool
                            | Ty::Param(_)
                            | Ty::Class(_)
                            | Ty::Record(_)
                            | Ty::Array(_)
                            | Ty::Slots(_)
                            | Ty::Option(_)
                            | Ty::OptionRaw(_)
                            | Ty::Raw(_)
                            | Ty::RawRecord(_)
                            | Ty::Borrow(..)
                            | Ty::Unit => unreachable!("res_kind classified the borrow"),
                        },
                        Ty::Borrow(Mutability::Mut, referent) => match referent.as_ref() {
                            Ty::Res(_) => (Mutability::Mut, false),
                            Ty::Int(_)
                            | Ty::Bool
                            | Ty::Param(_)
                            | Ty::Class(_)
                            | Ty::Record(_)
                            | Ty::Array(_)
                            | Ty::Slots(_)
                            | Ty::Option(_)
                            | Ty::OptionRaw(_)
                            | Ty::Raw(_)
                            | Ty::RawRecord(_)
                            | Ty::Borrow(..)
                            | Ty::Unit => unreachable!("res_kind classified the borrow"),
                        },
                        Ty::Int(_)
                        | Ty::Bool
                        | Ty::Param(_)
                        | Ty::Class(_)
                        | Ty::Record(_)
                        | Ty::Array(_)
                        | Ty::Slots(_)
                        | Ty::Option(_)
                        | Ty::OptionRaw(_)
                        | Ty::Raw(_)
                        | Ty::RawRecord(_)
                        | Ty::Unit => unreachable!("res_kind classified the value"),
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
                if let Some(ci) = checked_class_index(&v.ty) {
                    let (src_mut, is_local) = match checked_class_borrow(&v.ty) {
                        Some((_borrowed_class, mutability)) => (mutability, false),
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
            if ctx
                .vars
                .get(array.as_str())
                .is_some_and(|binding| binding.ty.as_slots().is_some())
            {
                return Err(slots_unsupported(span, "slot borrow"));
            }
            let elem = array_elem_ty(ctx, array, span)?;
            let src_mut = match ctx.vars.get(array.as_str()).map(|v| v.ty.clone()) {
                Some(ty) => match checked_array_binding(&ty) {
                    Some((_element, mode)) => mode,
                    None => unreachable!("array_elem_ty checked"),
                },
                None => unreachable!("array_elem_ty checked"),
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
            Some(
                Ty::Int(_)
                | Ty::Bool
                | Ty::Param(_)
                | Ty::Class(_)
                | Ty::Record(_)
                | Ty::Array(_)
                | Ty::Slots(_)
                | Ty::Res(_)
                | Ty::Raw(_)
                | Ty::RawRecord(_)
                | Ty::Borrow(..)
                | Ty::Unit,
            )
            | None => {
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
            Some(
                Ty::Int(_)
                | Ty::Bool
                | Ty::Param(_)
                | Ty::Class(_)
                | Ty::Record(_)
                | Ty::Array(_)
                | Ty::Slots(_)
                | Ty::Res(_)
                | Ty::Raw(_)
                | Ty::RawRecord(_)
                | Ty::Borrow(..)
                | Ty::Unit,
            )
            | None => {
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
                    Ty::Bool
                    | Ty::Class(_)
                    | Ty::Record(_)
                    | Ty::Array(_)
                    | Ty::Slots(_)
                    | Ty::Option(_)
                    | Ty::OptionRaw(_)
                    | Ty::Res(_)
                    | Ty::Raw(_)
                    | Ty::RawRecord(_)
                    | Ty::Borrow(..)
                    | Ty::Unit => {
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
                    Some(ty) => checked_class_index(&ty).map(|ci| (n.clone(), ci)),
                    None => None,
                },
                ExprKind::IntLit(_)
                | ExprKind::BoolLit(_)
                | ExprKind::Unary { .. }
                | ExprKind::Binary { .. }
                | ExprKind::Call { .. }
                | ExprKind::Index { .. }
                | ExprKind::Len { .. }
                | ExprKind::RawOp { .. }
                | ExprKind::DeviceOp { .. }
                | ExprKind::ResOp { .. }
                | ExprKind::SlotOp { .. }
                | ExprKind::Widen { .. }
                | ExprKind::Narrow { .. }
                | ExprKind::IsSome { .. }
                | ExprKind::OptValue { .. }
                | ExprKind::OptTake { .. }
                | ExprKind::SomeE(_)
                | ExprKind::NoneE
                | ExprKind::ArrayLit(_)
                | ExprKind::AllocArray { .. }
                | ExprKind::SelfField { .. }
                | ExprKind::SelfFieldLen { .. }
                | ExprKind::SelfFieldIndex { .. }
                | ExprKind::CtorCall { .. }
                | ExprKind::ClassField { .. }
                | ExprKind::RecordField { .. }
                | ExprKind::ClassFieldLen { .. }
                | ExprKind::ClassFieldIndex { .. }
                | ExprKind::TraitCall { .. }
                | ExprKind::MethodCall { .. }
                | ExprKind::Borrow { .. }
                | ExprKind::RecordLit { .. } => None,
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
                    Some(
                        ty @ (Ty::Int(
                            IntTy::U8
                            | IntTy::U16
                            | IntTy::U32
                            | IntTy::U64
                            | IntTy::I8
                            | IntTy::I16
                            | IntTy::I32
                            | IntTy::I64,
                        )
                        | Ty::Param(_)),
                    ) => Some(ty),
                    Some(
                        Ty::Int(IntTy::TParam(_))
                        | Ty::Bool
                        | Ty::Class(_)
                        | Ty::Record(_)
                        | Ty::Array(_)
                        | Ty::Slots(_)
                        | Ty::Option(_)
                        | Ty::OptionRaw(_)
                        | Ty::Res(_)
                        | Ty::Raw(_)
                        | Ty::RawRecord(_)
                        | Ty::Borrow(..)
                        | Ty::Unit,
                    )
                    | None => None,
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
            let params = sig.params.clone();
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
                Ty::Res(_)
                | Ty::Raw(_)
                | Ty::RawRecord(_)
                | Ty::OptionRaw(_)
                | Ty::Array(_)
                | Ty::Borrow(..) => true,
                Ty::Class(ci) => class_holds_storage(ctx.class_metas, ci, 0),
                Ty::Record(ri) => record_holds_storage(ctx.record_metas, ri),
                Ty::Slots(_) => {
                    return Err(slots_unsupported(span, "function return type"));
                }
                Ty::Int(_) | Ty::Bool | Ty::Param(_) | Ty::Option(_) | Ty::Unit => false,
            };
            let moved_before = ctx.moved.clone();
            let mut transfers = Vec::with_capacity(args.len());
            for (arg, parameter) in args.iter_mut().zip(&params) {
                let escapes = launders.then(|| ("be passed to a function", arg.span));
                check_user_call_argument(ctx, arg, &parameter.ty)?;
                transfers.push(transfer(ctx, arg, escapes)?);
            }
            record_call_transitions(
                ctx,
                CallTarget::Function(callee.clone()),
                &params,
                args,
                &transfers,
                None,
                &moved_before,
                span,
            )?;
            if *callee != ctx.current_fn {
                ctx.calls.push(CallOwner::Function(callee.clone()));
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

/// The place an argument borrows, and whether the borrow is mutable. A
/// bare name that is already a class borrow counts too: it hands the
/// borrowed place on without an `&` at the call site.
fn borrow_place(ctx: &Ctx, arg: &Expr) -> Option<(Place, bool)> {
    match BorrowedPlace::from_expr(arg) {
        Some(borrowed) => Some((
            borrowed.place().clone(),
            borrowed.mutability() == Mutability::Mut,
        )),
        // A borrowed class or resource parameter is itself a place that can
        // be re-borrowed. A borrowed array is not: its element storage is
        // named by an index, which `Place` has no path for.
        None => match &arg.kind {
            ExprKind::Var(n) => match ctx.vars.get(n.as_str()).map(|v| v.ty.clone()) {
                Some(ty) => match ty {
                    Ty::Borrow(Mutability::Shared, referent) => match referent.as_ref() {
                        Ty::Class(_) | Ty::Res(_) => Some((Place::local(n), false)),
                        Ty::Int(_)
                        | Ty::Bool
                        | Ty::Param(_)
                        | Ty::Record(_)
                        | Ty::Raw(_)
                        | Ty::RawRecord(_)
                        | Ty::Array(_)
                        | Ty::Slots(_)
                        | Ty::Option(_)
                        | Ty::OptionRaw(_)
                        | Ty::Borrow(..)
                        | Ty::Unit => None,
                    },
                    Ty::Borrow(Mutability::Mut, referent) => match referent.as_ref() {
                        Ty::Class(_) | Ty::Res(_) => Some((Place::local(n), true)),
                        Ty::Int(_)
                        | Ty::Bool
                        | Ty::Param(_)
                        | Ty::Record(_)
                        | Ty::Raw(_)
                        | Ty::RawRecord(_)
                        | Ty::Array(_)
                        | Ty::Slots(_)
                        | Ty::Option(_)
                        | Ty::OptionRaw(_)
                        | Ty::Borrow(..)
                        | Ty::Unit => None,
                    },
                    Ty::Int(_)
                    | Ty::Bool
                    | Ty::Param(_)
                    | Ty::Class(_)
                    | Ty::Record(_)
                    | Ty::Raw(_)
                    | Ty::RawRecord(_)
                    | Ty::Array(_)
                    | Ty::Slots(_)
                    | Ty::Option(_)
                    | Ty::OptionRaw(_)
                    | Ty::Res(_)
                    | Ty::Unit => None,
                },
                None => None,
            },
            ExprKind::IntLit(_)
            | ExprKind::BoolLit(_)
            | ExprKind::Len { .. }
            | ExprKind::Index { .. }
            | ExprKind::Unary { .. }
            | ExprKind::Binary { .. }
            | ExprKind::Call { .. }
            | ExprKind::TraitCall { .. }
            | ExprKind::SomeE(_)
            | ExprKind::NoneE
            | ExprKind::IsSome { .. }
            | ExprKind::OptValue { .. }
            | ExprKind::OptTake { .. }
            | ExprKind::Widen { .. }
            | ExprKind::Narrow { .. }
            | ExprKind::AllocArray { .. }
            | ExprKind::ArrayLit(_)
            | ExprKind::SelfField { .. }
            | ExprKind::SelfFieldLen { .. }
            | ExprKind::SelfFieldIndex { .. }
            | ExprKind::ClassField { .. }
            | ExprKind::ClassFieldLen { .. }
            | ExprKind::ClassFieldIndex { .. }
            | ExprKind::MethodCall { .. }
            | ExprKind::CtorCall { .. }
            | ExprKind::RawOp { .. }
            | ExprKind::ResOp { .. }
            | ExprKind::DeviceOp { .. }
            | ExprKind::SlotOp { .. }
            | ExprKind::Borrow { .. }
            | ExprKind::RecordField { .. }
            | ExprKind::RecordLit { .. } => None,
        },
    }
}

/// Preserve the checker's resolved unique-borrow effects for VC generation.
///
/// This runs only after argument typing. Alias admission consumes the completed
/// record plus the checker's flow-sensitive move delta for argument evaluation,
/// so a nested expression cannot hide a move behind a fresh outer result.
fn record_call_transitions(
    ctx: &mut Ctx,
    target: CallTarget,
    params: &[Param],
    args: &[Expr],
    transfers: &[ValueTransfer],
    receiver: Option<(Place, String, Mutability, Span, Ty)>,
    moved_before: &HashSet<Place>,
    span: Span,
) -> CResult<()> {
    if params.len() != args.len() || args.len() != transfers.len() {
        return Err(Diagnostic {
            name: "internal.check.call_transition_arity".into(),
            title: "checked call arguments and ownership outcomes have different lengths".into(),
            span,
            label: "the ownership handoff requires one outcome per argument".into(),
            notes: vec![],
        });
    }
    let mut arguments = Vec::with_capacity(args.len());
    for (parameter_index, ((parameter, argument), transfer)) in
        params.iter().zip(args).zip(transfers).enumerate()
    {
        let effect = match &parameter.ty {
            Ty::Borrow(mutability, referent) => {
                let Some((place, actual_mutable)) = borrow_place(ctx, argument) else {
                    return Err(Diagnostic {
                        name: "internal.check.call_transition_shape".into(),
                        title: format!(
                            "checked borrowed parameter `{}` has no borrowed place",
                            parameter.name
                        ),
                        span: argument.span,
                        label: "the ownership handoff cannot identify this argument".into(),
                        notes: vec![],
                    });
                };
                // Argument checking normally rejects this first. Keep the
                // complete checker-authored call record independently honest,
                // including direct `&self.field` places and bare re-borrows:
                // no loan may start from a place that was already dead when
                // this call began. Moves performed by later arguments are
                // intentionally handled below as `borrow.moved_in_call`.
                if place_is_moved(moved_before, &place) {
                    return Err(moved_out(ctx, &place, argument.span, "borrow"));
                }
                let actual = if actual_mutable {
                    Mutability::Mut
                } else {
                    Mutability::Shared
                };
                if actual != *mutability {
                    return Err(Diagnostic {
                        name: "internal.check.call_transition_mutability".into(),
                        title: format!(
                            "checked borrow for `{}` has the wrong mutability",
                            parameter.name
                        ),
                        span: argument.span,
                        label: "argument admission and ownership handoff disagree".into(),
                        notes: vec![],
                    });
                }
                CallArgumentEffect::Loan(
                    CallTransition::borrow(
                        place,
                        *mutability,
                        referent.as_ref().clone(),
                        argument.span,
                    )
                    .map_err(|message| Diagnostic {
                        name: "internal.check.call_transition_unsupported".into(),
                        title: message,
                        span: argument.span,
                        label: "the checked loan has no admitted ownership transition".into(),
                        notes: vec![],
                    })?,
                )
            }
            Ty::Int(_)
            | Ty::Bool
            | Ty::Param(_)
            | Ty::Class(_)
            | Ty::Record(_)
            | Ty::Array(_)
            | Ty::Slots(_)
            | Ty::Option(_)
            | Ty::OptionRaw(_)
            | Ty::Res(_)
            | Ty::Raw(_)
            | Ty::RawRecord(_)
            | Ty::Unit => CallArgumentEffect::Value(transfer.clone()),
        };
        arguments.push(CallArgumentTransition {
            parameter_index,
            parameter: parameter.name.clone(),
            parameter_ty: parameter.ty.clone(),
            argument_span: argument.span,
            effect,
        });
    }

    if let Some((place, _, _, receiver_span, _)) = &receiver {
        // Method receivers use this same authority boundary as explicit call
        // arguments. The early receiver rule gives the source diagnostic;
        // this check prevents a forged or future caller from retaining an
        // impossible receiver transition in the ownership plan.
        if place_is_moved(moved_before, place) {
            return Err(moved_out(ctx, place, *receiver_span, "method receiver"));
        }
    }
    let receiver = receiver
        .map(|(place, class, mutability, receiver_span, referent)| {
            CallTransition::borrow(place, mutability, referent, receiver_span)
                .map(|transition| CallReceiverTransition { class, transition })
                .map_err(|message| Diagnostic {
                    name: "internal.check.call_receiver_unsupported".into(),
                    title: message,
                    span: receiver_span,
                    label: "the checked receiver has no admitted ownership transition".into(),
                    notes: vec![],
                })
        })
        .transpose()?;

    let call = CheckedCallTransition {
        key: CallSiteKey {
            owner: ctx.call_owner.clone(),
            span,
            target,
        },
        receiver,
        arguments,
    };
    let argument_loans: Vec<Option<CallTransition>> = call
        .arguments
        .iter()
        .map(|argument| match &argument.effect {
            CallArgumentEffect::Loan(loan) => Some(loan.clone()),
            CallArgumentEffect::Value(_) => None,
        })
        .collect();
    check_pending_loan_argument_mutations(
        ctx,
        &call.key.target.render(),
        call.receiver.as_ref().map(|receiver| &receiver.transition),
        args,
        &argument_loans,
        span,
    )?;
    check_recorded_call_conflicts(ctx, moved_before, &call)?;
    ctx.ownership
        .calls
        .insert(call)
        .map_err(|duplicate| Diagnostic {
            name: "internal.check.duplicate_call_transition".into(),
            title: format!(
                "duplicate checked-call identity for {} inside {}",
                duplicate.target.render(),
                duplicate.owner.render()
            ),
            span: duplicate.span,
            label: "owner, span, and resolved target must identify exactly one call".into(),
            notes: vec![],
        })
}

/// Build the single checker-authored mutation summary consumed by loop havoc.
/// This walk runs only after condition/body checking has succeeded, so call,
/// sealed-operation, option, and exposure records are already resolved. It is
/// deliberately checker-side: VC generation must not infer effects by walking
/// expression syntax a second time.
fn checked_loop_effects(
    ctx: &Ctx,
    keyword_span: Span,
    condition: &Expr,
    body: &[Stmt],
) -> CResult<CheckedLoopEffects> {
    let mut mutations = Vec::new();
    collect_checked_expr_mutations(ctx, condition, &mut mutations)?;
    collect_checked_stmt_mutations(ctx, body, &mut mutations)?;
    Ok(CheckedLoopEffects {
        key: EffectSiteKey {
            owner: ctx.call_owner.clone(),
            span: keyword_span,
        },
        condition_span: condition.span,
        mutations,
    })
}

fn collect_checked_stmt_mutations(
    ctx: &Ctx,
    statements: &[Stmt],
    out: &mut Vec<CheckedMutation>,
) -> CResult<()> {
    for statement in statements {
        match statement {
            Stmt::Assign { name, value, .. } => {
                out.push(CheckedMutation::DirectWrite {
                    place: Place::local(name),
                });
                collect_checked_expr_mutations(ctx, value, out)?;
            }
            Stmt::Store {
                array,
                index,
                value,
                ..
            } => {
                out.push(CheckedMutation::DirectWrite {
                    place: Place::local(array),
                });
                collect_checked_expr_mutations(ctx, index, out)?;
                collect_checked_expr_mutations(ctx, value, out)?;
            }
            Stmt::FieldAssign { value, .. } => {
                out.push(CheckedMutation::DirectWrite {
                    place: Place::local("self"),
                });
                collect_checked_expr_mutations(ctx, value, out)?;
            }
            Stmt::FieldStore { index, value, .. } => {
                out.push(CheckedMutation::DirectWrite {
                    place: Place::local("self"),
                });
                collect_checked_expr_mutations(ctx, index, out)?;
                collect_checked_expr_mutations(ctx, value, out)?;
            }
            Stmt::ExprStmt(expression) => {
                collect_checked_expr_mutations(ctx, expression, out)?;
            }
            Stmt::Decl {
                init: Some(init), ..
            }
            | Stmt::VarDecl { init, .. } => {
                collect_checked_expr_mutations(ctx, init, out)?;
            }
            Stmt::Return {
                value: Some(value), ..
            } => collect_checked_expr_mutations(ctx, value, out)?,
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                collect_checked_expr_mutations(ctx, cond, out)?;
                collect_checked_stmt_mutations(ctx, then_block, out)?;
                if let Some(else_block) = else_block {
                    collect_checked_stmt_mutations(ctx, else_block, out)?;
                }
            }
            Stmt::While { cond, body, .. } => {
                collect_checked_expr_mutations(ctx, cond, out)?;
                collect_checked_stmt_mutations(ctx, body, out)?;
            }
            Stmt::Unsafe { body, .. } => collect_checked_stmt_mutations(ctx, body, out)?,
            Stmt::Expose {
                kw_span,
                mutable,
                body,
                ..
            } => {
                let key = EffectSiteKey {
                    owner: ctx.call_owner.clone(),
                    span: *kw_span,
                };
                let Some(exposure) = ctx.ownership.exposure(&key) else {
                    return Err(Diagnostic {
                        name: "internal.check.loop_exposure_missing".into(),
                        title: "checked loop exposure has no ownership record".into(),
                        span: *kw_span,
                        label: "loop effects require the admitted exposure boundary".into(),
                        notes: vec![],
                    });
                };
                if *mutable {
                    out.push(CheckedMutation::ExposureRebuild {
                        owner_place: exposure.owner_place.clone(),
                    });
                }
                collect_checked_stmt_mutations(ctx, body, out)?;
            }
            Stmt::StaticAlloc { size, .. } | Stmt::SystemAlloc { size, .. } => {
                collect_checked_expr_mutations(ctx, size, out)?;
            }
            Stmt::SystemDealloc {
                ptr, res, release, ..
            } => {
                collect_checked_expr_mutations(ctx, ptr, out)?;
                collect_checked_expr_mutations(ctx, res, out)?;
                collect_checked_expr_mutations(ctx, release, out)?;
            }
            Stmt::Assert(_) | Stmt::Decl { init: None, .. } | Stmt::Return { value: None, .. } => {}
        }
    }
    Ok(())
}

fn collect_checked_expr_mutations(
    ctx: &Ctx,
    expression: &Expr,
    out: &mut Vec<CheckedMutation>,
) -> CResult<()> {
    match &expression.kind {
        ExprKind::SlotOp { op, args, .. } => {
            for argument in args {
                collect_checked_expr_mutations(ctx, argument, out)?;
            }
            let key = EffectSiteKey {
                owner: ctx.call_owner.clone(),
                span: expression.span,
            };
            let Some(transition) = ctx.ownership.slot_transition(&key) else {
                return Err(Diagnostic {
                    name: "internal.check.loop_slot_transition_missing".into(),
                    title: "checked loop slot operation has no ownership transition".into(),
                    span: expression.span,
                    label: "loop effects require the checker-authored slot boundary".into(),
                    notes: vec![],
                });
            };
            match (op, &transition.kind) {
                (SlotOp::Alloc { .. }, CheckedSlotTransitionKind::Alloc { .. }) => {}
                (SlotOp::Take, CheckedSlotTransitionKind::Take { container, .. }) => {
                    out.push(CheckedMutation::Slot {
                        key,
                        operation: CheckedSlotMutationKind::Take,
                        container: container.clone(),
                        payload: transition.payload.clone(),
                    });
                }
                (SlotOp::Put, CheckedSlotTransitionKind::Put { container, .. }) => {
                    out.push(CheckedMutation::Slot {
                        key,
                        operation: CheckedSlotMutationKind::Put,
                        container: container.clone(),
                        payload: transition.payload.clone(),
                    });
                }
                (SlotOp::Alloc { .. }, CheckedSlotTransitionKind::Take { .. })
                | (SlotOp::Alloc { .. }, CheckedSlotTransitionKind::Put { .. })
                | (SlotOp::Take, CheckedSlotTransitionKind::Alloc { .. })
                | (SlotOp::Take, CheckedSlotTransitionKind::Put { .. })
                | (SlotOp::Put, CheckedSlotTransitionKind::Alloc { .. })
                | (SlotOp::Put, CheckedSlotTransitionKind::Take { .. }) => {
                    return Err(Diagnostic {
                        name: "internal.check.loop_slot_transition_mismatch".into(),
                        title: "slot syntax and checked ownership transition disagree".into(),
                        span: expression.span,
                        label: format!("`{}` must retain its exact checked operation", op.name()),
                        notes: vec![],
                    });
                }
            }
        }
        ExprKind::Call { args, .. }
        | ExprKind::CtorCall { args, .. }
        | ExprKind::MethodCall { args, .. } => {
            for argument in args {
                collect_checked_expr_mutations(ctx, argument, out)?;
            }
            let mut records = ctx
                .ownership
                .calls
                .for_owner_span(&ctx.call_owner, expression.span);
            let Some((_, call)) = records.next() else {
                return Err(Diagnostic {
                    name: "internal.check.loop_call_missing".into(),
                    title: "checked loop call has no ownership record".into(),
                    span: expression.span,
                    label: "loop effects require the admitted call boundary".into(),
                    notes: vec![],
                });
            };
            if records.next().is_some() {
                return Err(Diagnostic {
                    name: "internal.check.loop_call_ambiguous".into(),
                    title: "checked loop call span has more than one ownership record".into(),
                    span: expression.span,
                    label: "one source call must have one resolved transition".into(),
                    notes: vec![],
                });
            }
            if let Some(receiver) = &call.receiver {
                if receiver.transition.effect == crate::transition::CallEffect::HavocUniqueBorrow {
                    out.push(CheckedMutation::UniqueLoan(receiver.transition.clone()));
                }
            }
            for argument in &call.arguments {
                if let CallArgumentEffect::Loan(loan) = &argument.effect {
                    if loan.effect == crate::transition::CallEffect::HavocUniqueBorrow {
                        out.push(CheckedMutation::UniqueLoan(loan.clone()));
                    }
                }
            }
        }
        ExprKind::RawOp { args, .. }
        | ExprKind::ResOp { args, .. }
        | ExprKind::DeviceOp { args, .. } => {
            for argument in args {
                collect_checked_expr_mutations(ctx, argument, out)?;
            }
            let key = EffectSiteKey {
                owner: ctx.call_owner.clone(),
                span: expression.span,
            };
            let Some(operation) = ctx.ownership.sealed_operation(&key) else {
                return Err(Diagnostic {
                    name: "internal.check.loop_sealed_missing".into(),
                    title: "checked sealed operation has no ownership record".into(),
                    span: expression.span,
                    label: "loop effects require the admitted sealed boundary".into(),
                    notes: vec![],
                });
            };
            for argument in &operation.arguments {
                if let CallArgumentEffect::Loan(loan) = &argument.effect {
                    if loan.effect == crate::transition::CallEffect::HavocUniqueBorrow {
                        out.push(CheckedMutation::UniqueLoan(loan.clone()));
                    }
                }
            }
        }
        ExprKind::OptTake { .. } => {
            let key = EffectSiteKey {
                owner: ctx.call_owner.clone(),
                span: expression.span,
            };
            let Some(take) = ctx.ownership.option_take(&key) else {
                return Err(Diagnostic {
                    name: "internal.check.loop_option_take_missing".into(),
                    title: "checked option take has no ownership record".into(),
                    span: expression.span,
                    label: "loop effects require the admitted extraction boundary".into(),
                    notes: vec![],
                });
            };
            out.push(CheckedMutation::OptionTake {
                source: take.source.clone(),
                payload: take.payload.clone(),
            });
        }
        ExprKind::TraitCall { args, .. } | ExprKind::RecordLit { args, .. } => {
            for argument in args {
                collect_checked_expr_mutations(ctx, argument, out)?;
            }
        }
        ExprKind::Unary { operand, .. }
        | ExprKind::Widen { arg: operand, .. }
        | ExprKind::Narrow { arg: operand, .. }
        | ExprKind::IsSome { operand }
        | ExprKind::OptValue { operand }
        | ExprKind::SomeE(operand) => collect_checked_expr_mutations(ctx, operand, out)?,
        ExprKind::Binary { lhs, rhs, .. } => {
            collect_checked_expr_mutations(ctx, lhs, out)?;
            collect_checked_expr_mutations(ctx, rhs, out)?;
        }
        ExprKind::Index { index, .. }
        | ExprKind::SelfFieldIndex { index, .. }
        | ExprKind::ClassFieldIndex { index, .. } => {
            collect_checked_expr_mutations(ctx, index, out)?;
        }
        ExprKind::AllocArray { len, init, .. } => {
            collect_checked_expr_mutations(ctx, len, out)?;
            collect_checked_expr_mutations(ctx, init, out)?;
        }
        ExprKind::ArrayLit(elements) => {
            for element in elements {
                collect_checked_expr_mutations(ctx, element, out)?;
            }
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
    Ok(())
}

/// Seal the ownership boundary of one compiler-defined operation after its
/// ordinary typing rules have succeeded. Transfers are captured at the point
/// they occur; the remaining arguments are loans or non-affine copies whose
/// state cannot change while the rest of this operation is checked.
fn record_sealed_operation(
    ctx: &mut Ctx,
    target: CheckedSealedTarget,
    args: &[Expr],
    transfers: &[Option<ValueTransfer>],
    moved_before: &HashSet<Place>,
    result_ty: Ty,
    span: Span,
) -> CResult<()> {
    if args.len() != transfers.len() {
        return Err(Diagnostic {
            name: "internal.check.sealed_transition_arity".into(),
            title: format!(
                "checked `{}` arguments and ownership outcomes have different lengths",
                target.render()
            ),
            span,
            label: "the ownership handoff requires one outcome per argument".into(),
            notes: vec![],
        });
    }
    let mut arguments = Vec::with_capacity(args.len());
    for (index, (argument, transferred)) in args.iter().zip(transfers).enumerate() {
        let argument_ty = argument
            .ty
            .clone()
            .expect("sealed operation record follows successful expression checking");
        let effect = match &argument_ty {
            Ty::Borrow(mutability, referent) => {
                let Some((place, actual_mutable)) = borrow_place(ctx, argument) else {
                    return Err(Diagnostic {
                        name: "internal.check.sealed_transition_shape".into(),
                        title: format!(
                            "checked borrowed argument {index} of `{}` has no borrowed place",
                            target.render()
                        ),
                        span: argument.span,
                        label: "the ownership handoff cannot identify this argument".into(),
                        notes: vec![],
                    });
                };
                let actual = if actual_mutable {
                    Mutability::Mut
                } else {
                    Mutability::Shared
                };
                if actual != *mutability {
                    return Err(Diagnostic {
                        name: "internal.check.sealed_transition_mutability".into(),
                        title: format!(
                            "checked borrow argument {index} of `{}` has the wrong mutability",
                            target.render()
                        ),
                        span: argument.span,
                        label: "argument admission and ownership handoff disagree".into(),
                        notes: vec![],
                    });
                }
                if !place.is_root() {
                    return Err(Diagnostic {
                        name: "resource.field_borrow_op".into(),
                        title: format!(
                            "`{}` cannot borrow the field `{}`",
                            target.render(),
                            place.render()
                        ),
                        span: argument.span,
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
                CallArgumentEffect::Loan(
                    CallTransition::borrow(
                        place,
                        *mutability,
                        referent.as_ref().clone(),
                        argument.span,
                    )
                    .map_err(|message| Diagnostic {
                        name: "internal.check.sealed_transition_unsupported".into(),
                        title: message,
                        span: argument.span,
                        label: "the checked loan has no admitted ownership transition".into(),
                        notes: vec![],
                    })?,
                )
            }
            Ty::Int(_)
            | Ty::Bool
            | Ty::Param(_)
            | Ty::Class(_)
            | Ty::Record(_)
            | Ty::Array(_)
            | Ty::Slots(_)
            | Ty::Option(_)
            | Ty::OptionRaw(_)
            | Ty::Res(_)
            | Ty::Raw(_)
            | Ty::RawRecord(_)
            | Ty::Unit => {
                let value = if let Some(value) = transferred {
                    value.clone()
                } else {
                    if is_affine(&argument_ty) {
                        return Err(Diagnostic {
                            name: "internal.check.sealed_transition_missing_move".into(),
                            title: format!(
                                "affine argument {index} of `{}` has no transfer outcome",
                                target.render()
                            ),
                            span: argument.span,
                            label: "the checked move must be captured when it occurs".into(),
                            notes: vec![],
                        });
                    }
                    ValueTransfer {
                        source: Place::from_value_expr(argument),
                        value_ty: argument_ty.clone(),
                        kind: ValueTransferKind::Copy,
                        carried_obligation: false,
                        branded: brand_of(ctx, argument),
                        span: argument.span,
                    }
                };
                CallArgumentEffect::Value(value)
            }
        };
        arguments.push(CheckedSealedArgument {
            index,
            argument_ty,
            argument_span: argument.span,
            effect,
        });
    }

    let argument_loans: Vec<Option<CallTransition>> = arguments
        .iter()
        .map(|argument| match &argument.effect {
            CallArgumentEffect::Loan(loan) => Some(loan.clone()),
            CallArgumentEffect::Value(_) => None,
        })
        .collect();
    check_pending_loan_argument_mutations(ctx, target.render(), None, args, &argument_loans, span)?;
    check_recorded_argument_conflicts(ctx, moved_before, target.render(), &arguments)?;
    let operation = CheckedSealedOperation {
        key: EffectSiteKey {
            owner: ctx.call_owner.clone(),
            span,
        },
        target,
        arguments,
        result_ty,
    };
    ctx.ownership
        .insert_sealed_operation(operation)
        .map_err(|duplicate| Diagnostic {
            name: "internal.check.duplicate_sealed_transition".into(),
            title: format!(
                "duplicate sealed-operation identity inside {}",
                duplicate.owner.render()
            ),
            span: duplicate.span,
            label: "owner and span must identify exactly one sealed operation".into(),
            notes: vec![],
        })
}

/// Keep a pending call loan's captured state stable across later arguments.
///
/// Sable evaluates arguments left-to-right. A borrow expression is therefore
/// not a place recipe resolved only at callee entry: its place and entry state
/// are captured at that argument position. The reservation becomes a callee
/// loan only after argument evaluation completes, so a transient later read
/// may finish first; a later mutation may not invalidate the captured state.
/// The formal SVM makes this observable for unique array loans by reading the
/// lending argument before entering the callee and writing its exit value
/// back later. Letting a subsequent argument mutate the same place would make
/// that copy-in/write-back semantics disagree with the interpreter's shared
/// storage, native pointers, and VC snapshots.
///
/// Mutation discovery consumes the checker-authored ownership plan. In
/// particular, a nested call contributes its recorded unique receiver or
/// argument loan; this check does not rediscover mutability from call syntax.
/// Every [`CheckedMutation`] variant denotes a write, extraction, or state
/// reconstruction and therefore conflicts on overlap; none is filtered by its
/// current source spelling. A mutation that completes in an earlier argument
/// remains legal because no outer reservation has captured that state yet.
fn check_pending_loan_argument_mutations(
    ctx: &Ctx,
    operation: &str,
    receiver: Option<&CallTransition>,
    arguments: &[Expr],
    argument_loans: &[Option<CallTransition>],
    span: Span,
) -> CResult<()> {
    if arguments.len() != argument_loans.len() {
        return Err(Diagnostic {
            name: "internal.check.call_evaluation_arity".into(),
            title: format!(
                "checked `{operation}` arguments and evaluation effects have different lengths"
            ),
            span,
            label: "pending-loan stability requires one checked effect per argument".into(),
            notes: vec![],
        });
    }

    // A named method receiver is resolved before its explicit arguments in
    // every executable backend, so its implicit loan is the first pending
    // reservation whose captured state must stay stable.
    let mut pending_loans: Vec<CallTransition> = receiver.into_iter().cloned().collect();
    for (argument, loan) in arguments.iter().zip(argument_loans) {
        let mut mutations = Vec::new();
        collect_checked_expr_mutations(ctx, argument, &mut mutations)?;
        for mutation in mutations {
            if let Some(pending) = pending_loans
                .iter()
                .find(|pending| pending.place.overlaps(mutation.place()))
            {
                return Err(Diagnostic {
                    name: "borrow.conflict".into(),
                    title: format!(
                        "borrow of `{}` overlaps a later mutation in `{operation}`",
                        pending.place.render()
                    ),
                    span: argument.span,
                    label: format!(
                        "this argument mutates `{}` after the borrow was created",
                        mutation.place().render()
                    ),
                    notes: vec![(
                        "note".into(),
                        "call arguments evaluate left-to-right; a borrow argument captures its \
                         entry state before the callee begins, so later arguments must not \
                         mutate the same place"
                            .into(),
                    )],
                });
            }
        }
        if let Some(loan) = loan {
            pending_loans.push(loan.clone());
        }
    }
    Ok(())
}

fn check_recorded_argument_conflicts(
    ctx: &Ctx,
    moved_before: &HashSet<Place>,
    operation: &str,
    arguments: &[CheckedSealedArgument],
) -> CResult<()> {
    let loans: Vec<(&Place, bool, Span)> = arguments
        .iter()
        .filter_map(|argument| match &argument.effect {
            CallArgumentEffect::Loan(loan) => Some((
                &loan.place,
                loan.effect == crate::transition::CallEffect::HavocUniqueBorrow,
                loan.span,
            )),
            CallArgumentEffect::Value(_) => None,
        })
        .collect();
    for i in 0..loans.len() {
        for j in (i + 1)..loans.len() {
            let (left, left_mut, _) = loans[i];
            let (right, right_mut, right_span) = loans[j];
            if (left_mut || right_mut) && left.overlaps(right) {
                return Err(Diagnostic {
                    name: "borrow.conflict".into(),
                    title: format!(
                        "conflicting borrows of `{}` in `{operation}`",
                        left.render()
                    ),
                    span: right_span,
                    label: format!("this overlaps the borrow of `{}`", left.render()),
                    notes: vec![(
                        "note".into(),
                        "a mutable borrow must not overlap another borrow in the same \
                         operation: its symbolic effects frame them as distinct storage"
                            .into(),
                    )],
                });
            }
        }
    }
    for argument in arguments {
        let CallArgumentEffect::Value(value) = &argument.effect else {
            continue;
        };
        if value.kind != ValueTransferKind::Move {
            continue;
        }
        let Some(moved) = value.source.as_ref() else {
            continue;
        };
        if let Some((loaned, _, loan_span)) = loans
            .iter()
            .copied()
            .find(|(loaned, _, _)| loaned.overlaps(moved))
        {
            return Err(Diagnostic {
                name: "borrow.moved_in_call".into(),
                title: format!(
                    "`{}` is both lent and handed over in `{operation}`",
                    loaned.render()
                ),
                span: loan_span,
                label: format!(
                    "this borrow promises the caller keeps `{}`, which the same operation moves",
                    loaned.render()
                ),
                notes: vec![],
            });
        }
    }
    for (loaned, _, loan_span) in loans {
        if ctx
            .moved
            .difference(moved_before)
            .any(|moved| loaned.overlaps(moved))
        {
            return Err(Diagnostic {
                name: "borrow.moved_in_call".into(),
                title: format!(
                    "`{}` is lent and moved while evaluating `{operation}`",
                    loaned.render()
                ),
                span: loan_span,
                label: format!(
                    "this borrow promises the caller keeps `{}`, which argument evaluation moves",
                    loaned.render()
                ),
                notes: vec![(
                    "note".into(),
                    "a nested argument may return a fresh value while moving caller storage; \
                     the move still invalidates an earlier pending sealed-operation loan"
                        .into(),
                )],
            });
        }
    }
    Ok(())
}

/// Alias and move conflicts consume the same resolved record VC generation
/// receives. The flow delta is checker state, not a second source walk: it
/// retains moves performed by nested argument evaluation whose outer argument
/// transfer is necessarily `Fresh`.
fn check_recorded_call_conflicts(
    ctx: &Ctx,
    moved_before: &HashSet<Place>,
    call: &CheckedCallTransition,
) -> CResult<()> {
    let mut loans: Vec<(&Place, bool, Span)> = Vec::new();
    if let Some(receiver) = &call.receiver {
        loans.push((
            &receiver.transition.place,
            receiver.transition.effect == crate::transition::CallEffect::HavocUniqueBorrow,
            receiver.transition.span,
        ));
    }
    for argument in &call.arguments {
        if let CallArgumentEffect::Loan(loan) = &argument.effect {
            loans.push((
                &loan.place,
                loan.effect == crate::transition::CallEffect::HavocUniqueBorrow,
                loan.span,
            ));
        }
    }
    for i in 0..loans.len() {
        for j in (i + 1)..loans.len() {
            let (left, left_mut, _) = loans[i];
            let (right, right_mut, right_span) = loans[j];
            if (left_mut || right_mut) && left.overlaps(right) {
                return Err(Diagnostic {
                    name: "borrow.conflict".into(),
                    title: format!("conflicting borrows of `{}` in one call", left.render()),
                    span: right_span,
                    label: format!("this overlaps the borrow of `{}`", left.render()),
                    notes: vec![(
                        "note".into(),
                        "a mutable borrow must not overlap another borrow in the same call: \
                         the callee's contract frames them as distinct storage"
                            .into(),
                    )],
                });
            }
        }
    }
    for argument in &call.arguments {
        let CallArgumentEffect::Value(value) = &argument.effect else {
            continue;
        };
        if value.kind != ValueTransferKind::Move {
            continue;
        }
        let Some(moved) = value.source.as_ref() else {
            continue;
        };
        if let Some((loaned, _, loan_span)) = loans
            .iter()
            .copied()
            .find(|(loaned, _, _)| loaned.overlaps(moved))
        {
            return Err(Diagnostic {
                name: "borrow.moved_in_call".into(),
                title: format!(
                    "`{}` is both lent and handed over in one call",
                    loaned.render()
                ),
                span: loan_span,
                label: format!(
                    "this borrow promises the caller keeps `{}`, which the same call moves",
                    loaned.render()
                ),
                notes: vec![(
                    "note".into(),
                    "a borrow and a move of one storage reach the callee as two values its \
                     contract frames separately, so a write through one is invisible to the other"
                        .into(),
                )],
            });
        }
    }
    for (loaned, _, loan_span) in loans {
        if ctx
            .moved
            .difference(moved_before)
            .any(|moved| loaned.overlaps(moved))
        {
            return Err(Diagnostic {
                name: "borrow.moved_in_call".into(),
                title: format!(
                    "`{}` is both lent and handed over in one call",
                    loaned.render()
                ),
                span: loan_span,
                label: format!(
                    "this borrow promises the caller keeps `{}`, which argument evaluation moves",
                    loaned.render()
                ),
                notes: vec![(
                    "note".into(),
                    "a nested argument may return a fresh value while moving caller storage; \
                     the move still conflicts with another argument's loan"
                        .into(),
                )],
            });
        }
    }
    Ok(())
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
    for (borrowed, _, span) in &borrows {
        if ctx.is_moved(borrowed) {
            return Err(Diagnostic {
                name: "borrow.moved_in_call".into(),
                title: format!(
                    "`{}` is both lent and handed over in one call",
                    borrowed.render()
                ),
                span: *span,
                label: format!(
                    "this borrow promises the caller keeps `{}`, which the same call moves",
                    borrowed.render()
                ),
                notes: vec![(
                    "note".into(),
                    "a borrow and a move of one storage reach the callee as two values its \
                     contract frames separately, so a write through one is invisible to the \
                     other"
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
/// follow (ADR 0023, ADR 0024). Only an already-held shared borrow may be
/// forwarded bare; unique access is visibly reborrowed with `&mut`.
fn check_user_call_argument(ctx: &mut Ctx, arg: &mut Expr, parameter_ty: &Ty) -> CResult<()> {
    match parameter_ty {
        Ty::Slots(_) => Err(slots_unsupported(arg.span, "call parameter")),
        borrowed_array @ Ty::Borrow(mutability, referent)
            if matches!(referent.as_ref(), Ty::Array(_)) =>
        {
            if !matches!(arg.kind, ExprKind::Borrow { .. }) {
                return Err(Diagnostic {
                    name: "type.array_arg_borrow".into(),
                    title: "a borrowed array parameter takes an explicit borrow".into(),
                    span: arg.span,
                    label: format!(
                        "write `{}name`",
                        if *mutability == Mutability::Mut {
                            "&mut "
                        } else {
                            "&"
                        }
                    ),
                    notes: vec![(
                        "note".into(),
                        "an argument's form follows the parameter's binding mode: a borrow \
                         names the caller's storage, while an owned `[T]` parameter takes the \
                         array itself"
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
            Ok(())
        }
        Ty::Borrow(..) => {
            require_explicit_borrow(ctx, arg, parameter_ty.clone())?;
            check_expr(ctx, arg, Some(parameter_ty.clone()))?;
            Ok(())
        }
        other @ (Ty::Int(_)
        | Ty::Bool
        | Ty::Param(_)
        | Ty::Class(_)
        | Ty::Record(_)
        | Ty::Array(_)
        | Ty::Option(_)
        | Ty::OptionRaw(_)
        | Ty::Res(_)
        | Ty::Raw(_)
        | Ty::RawRecord(_)
        | Ty::Unit) => {
            check_expr(ctx, arg, Some(other.clone()))?;
            Ok(())
        }
    }
}

/// Validate the explicit syntax of a class or resource borrow argument.
/// A bare shared borrow may be forwarded; unique access is always spelled
/// `&mut` at each call boundary (ADR 0023).
fn require_explicit_borrow(ctx: &Ctx, arg: &Expr, pty: Ty) -> CResult<()> {
    // Only a class or resource borrow names an owner a diagnostic can
    // print. An array borrow is written `&`/`&mut` at the call site by its
    // own rule, and a borrow of anything else is refused before this runs.
    let original_parameter_ty = pty.clone();
    let (m, owner, flipped) = match pty {
        Ty::Borrow(mutability, referent) => {
            let mutability = match mutability {
                Mutability::Shared => Mutability::Shared,
                Mutability::Mut => Mutability::Mut,
            };
            match *referent {
                Ty::Class(ci) => (
                    mutability,
                    ctx.class_metas[ci].name.clone(),
                    Ty::borrow(flip(mutability), Ty::Class(ci)),
                ),
                Ty::Res(kind) => (
                    mutability,
                    kind.name().to_string(),
                    Ty::borrow(flip(mutability), Ty::Res(kind)),
                ),
                Ty::Int(_)
                | Ty::Bool
                | Ty::Param(_)
                | Ty::Record(_)
                | Ty::Array(_)
                | Ty::Slots(_)
                | Ty::Option(_)
                | Ty::OptionRaw(_)
                | Ty::Raw(_)
                | Ty::RawRecord(_)
                | Ty::Borrow(..)
                | Ty::Unit => return Ok(()),
            }
        }
        Ty::Int(_)
        | Ty::Bool
        | Ty::Param(_)
        | Ty::Class(_)
        | Ty::Record(_)
        | Ty::Array(_)
        | Ty::Slots(_)
        | Ty::Option(_)
        | Ty::OptionRaw(_)
        | Ty::Res(_)
        | Ty::Raw(_)
        | Ty::RawRecord(_)
        | Ty::Unit => return Ok(()),
    };
    // Passing along a *shared* borrow already held under the same type:
    // nothing is handed over that the caller did not already have, and
    // no `&` announces anything. Unique access is different — `&mut` is
    // always written, so every mutable borrow argument is visible at the
    // call site (which conflict detection and the caller's post-call
    // havoc both rely on).
    if m == Mutability::Shared {
        if let ExprKind::Var(n) = &arg.kind {
            if ctx.vars.get(n.as_str()).map(|v| v.ty.clone()) == Some(original_parameter_ty.clone())
            {
                return Ok(());
            }
        }
    }
    let want = if m == Mutability::Mut { "&mut " } else { "&" };
    let Some(borrowed) = BorrowedPlace::from_expr(arg) else {
        return Err(Diagnostic {
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
        });
    };
    if borrowed.mutability() != m {
        Err(Diagnostic {
            name: "type.borrow_mutability".into(),
            title: format!(
                "expected `{}`, found `{}`",
                original_parameter_ty.name(),
                flipped.name()
            ),
            span: arg.span,
            label: format!("write `{want}name`"),
            notes: vec![(
                "note".into(),
                "a borrow's mutability is written at the call site, not \
                 inferred from the parameter"
                    .into(),
            )],
        })
    } else {
        Ok(())
    }
}

fn flip(m: Mutability) -> Mutability {
    match m {
        Mutability::Mut => Mutability::Shared,
        Mutability::Shared => Mutability::Mut,
    }
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
fn transfer(ctx: &mut Ctx, e: &Expr, escapes: Option<(&str, Span)>) -> CResult<ValueTransfer> {
    if let Some((how, span)) = escapes {
        reject_brand_escape(ctx, e, how, span)?;
    }
    let source = Place::from_value_expr(e);
    let value_ty =
        e.ty.clone()
            .expect("transfer follows successful expression checking");
    let branded = brand_of(ctx, e);
    // A fresh result of a mandatory resource type starts with an
    // obligation even though it has no source place. A move normally
    // finds the same obligation on its source; deriving it from the type
    // as well makes returns and compiler-sealed resource producers obey
    // the same rule without one-off minting hooks.
    let mut carries = e.ty.clone().is_some_and(mandatory_ty);
    if let Some(name) = source.as_ref().map(Place::state_key) {
        if let Some(v) = ctx.vars.get_mut(name.as_str()) {
            carries |= v.obligation;
            // The obligation goes with the token. Whether it is discharged
            // or merely relocated is the *sink's* answer, and the source
            // no longer owes it either way.
            v.obligation = false;
        }
    }
    // A borrow has no source place here, and a temporary already has no
    // caller-owned place. A named affine value has exactly the place decoded
    // above, shared with borrow conflict checking and VC call havoc.
    let kind = if is_affine(&value_ty) {
        if let Some(source) = source.as_ref() {
            ctx.moved.insert(source.clone());
            ValueTransferKind::Move
        } else {
            ValueTransferKind::Fresh
        }
    } else {
        ValueTransferKind::Copy
    };
    Ok(ValueTransfer {
        source,
        value_ty,
        kind,
        carried_obligation: carries,
        branded,
        span: e.span,
    })
}

/// Perform and retain a non-call value transfer. Calls and sealed operations
/// store their argument transfers in their complete boundary records instead;
/// every other admitted sink uses an exact owner+expression+semantic-sink
/// identity. The sink component keeps parser-desugared expressions with one
/// source anchor distinct without relying on traversal order.
fn transfer_and_record(
    ctx: &mut Ctx,
    expression: &Expr,
    sink: ValueTransferSink,
    escapes: Option<(&str, Span)>,
) -> CResult<ValueTransfer> {
    let transfer = transfer(ctx, expression, escapes)?;
    ctx.ownership
        .insert_value_transfer(ctx.call_owner.clone(), sink, transfer.clone())
        .map_err(|duplicate| Diagnostic {
            name: "internal.check.duplicate_value_transfer".into(),
            title: format!(
                "duplicate value-transfer identity inside {}",
                duplicate.owner.render()
            ),
            span: duplicate.span,
            label: "owner, expression span, and semantic sink must identify exactly one transfer"
                .into(),
            notes: vec![],
        })?;
    Ok(transfer)
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
    // A lexical child block does not merely make its locals uninitialized:
    // their names cease to denote places. Keep `ctx.declared` untouched so
    // function-wide uniqueness remains authoritative, but remove child-only
    // entries from the live source environment before restoring outer state.
    ctx.vars.retain(|name, _| snap.contains_key(name));
    for (name, v) in ctx.vars.iter_mut() {
        let st = &snap[name];
        v.initialized = st.initialized;
        v.branded = st.branded;
        v.obligation = st.obligation;
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
        .filter(|p| p.root() == "self")
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

    /// Whether this place owns an occupancy-tracked slot allocation.
    fn is_slots_place(&self, p: &Place) -> bool {
        self.place_ty(p).is_some_and(|t| matches!(t, Ty::Slots(_)))
    }

    /// Which affine category a place belongs to, as the prefix its
    /// diagnostics carry. The consequence differs — a class you can
    /// rebuild, a resource is authority somebody else now holds, an array
    /// is storage two names would reach — so the name says which.
    fn affine_kind(&self, p: &Place) -> &'static str {
        if self.is_resource_place(p) {
            "resource"
        } else if self.is_slots_place(p) {
            "slots"
        } else if self.is_array_place(p) {
            "array"
        } else {
            "class"
        }
    }

    /// A place is dead if it, or anything containing it, has been moved
    /// out: moving `o` kills `o.inner` too.
    fn is_moved(&self, p: &Place) -> bool {
        place_is_moved(&self.moved, p)
    }

    /// Type of `self.field` for a *use*: reading it, or writing through
    /// it. A field whose value moved away has neither.
    fn self_field_ty(&self, field: &str, span: Span, mutating: bool) -> CResult<Ty> {
        let ty = self.self_field_ty_rebind(field, span, mutating)?;
        // A field whose value was moved out is dead, and so is the whole
        // object; its untouched siblings are still readable. This is what
        // `partially-moved` means, and it is what a `deinit` body that
        // hands one field on and reads another needs (ADR 0029).
        let place = Place::field("self", field);
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
        Ty::Slots(_) => true,
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
        ExprKind::IntLit(_)
        | ExprKind::BoolLit(_)
        | ExprKind::Unary { .. }
        | ExprKind::Binary { .. }
        | ExprKind::Call { .. }
        | ExprKind::Index { .. }
        | ExprKind::Len { .. }
        | ExprKind::SlotOp { .. }
        | ExprKind::Widen { .. }
        | ExprKind::Narrow { .. }
        | ExprKind::NoneE
        | ExprKind::ArrayLit(_)
        | ExprKind::AllocArray { .. }
        | ExprKind::SelfField { .. }
        | ExprKind::SelfFieldLen { .. }
        | ExprKind::SelfFieldIndex { .. }
        | ExprKind::CtorCall { .. }
        | ExprKind::ClassField { .. }
        | ExprKind::ClassFieldLen { .. }
        | ExprKind::ClassFieldIndex { .. }
        | ExprKind::TraitCall { .. }
        | ExprKind::MethodCall { .. } => false,
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
        ExprKind::IntLit(_)
        | ExprKind::BoolLit(_)
        | ExprKind::Unary { .. }
        | ExprKind::Binary { .. }
        | ExprKind::Call { .. }
        | ExprKind::Index { .. }
        | ExprKind::Len { .. }
        | ExprKind::RawOp { .. }
        | ExprKind::DeviceOp { .. }
        | ExprKind::ResOp { .. }
        | ExprKind::SlotOp { .. }
        | ExprKind::Widen { .. }
        | ExprKind::Narrow { .. }
        | ExprKind::IsSome { .. }
        | ExprKind::OptValue { .. }
        | ExprKind::OptTake { .. }
        | ExprKind::SomeE(_)
        | ExprKind::NoneE
        | ExprKind::ArrayLit(_)
        | ExprKind::AllocArray { .. }
        | ExprKind::SelfField { .. }
        | ExprKind::SelfFieldLen { .. }
        | ExprKind::SelfFieldIndex { .. }
        | ExprKind::CtorCall { .. }
        | ExprKind::ClassField { .. }
        | ExprKind::RecordField { .. }
        | ExprKind::ClassFieldLen { .. }
        | ExprKind::ClassFieldIndex { .. }
        | ExprKind::TraitCall { .. }
        | ExprKind::MethodCall { .. }
        | ExprKind::RecordLit { .. } => e.ty.clone(),
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
        ExprKind::IntLit(_)
        | ExprKind::BoolLit(_)
        | ExprKind::Unary { .. }
        | ExprKind::Binary { .. }
        | ExprKind::Call { .. }
        | ExprKind::Index { .. }
        | ExprKind::Len { .. }
        | ExprKind::RawOp { .. }
        | ExprKind::DeviceOp { .. }
        | ExprKind::ResOp { .. }
        | ExprKind::SlotOp { .. }
        | ExprKind::Widen { .. }
        | ExprKind::Narrow { .. }
        | ExprKind::IsSome { .. }
        | ExprKind::OptValue { .. }
        | ExprKind::OptTake { .. }
        | ExprKind::SomeE(_)
        | ExprKind::NoneE
        | ExprKind::ArrayLit(_)
        | ExprKind::AllocArray { .. }
        | ExprKind::SelfField { .. }
        | ExprKind::SelfFieldLen { .. }
        | ExprKind::SelfFieldIndex { .. }
        | ExprKind::CtorCall { .. }
        | ExprKind::ClassField { .. }
        | ExprKind::RecordField { .. }
        | ExprKind::ClassFieldLen { .. }
        | ExprKind::ClassFieldIndex { .. }
        | ExprKind::TraitCall { .. }
        | ExprKind::MethodCall { .. }
        | ExprKind::RecordLit { .. } => "storage derived from this exposure".to_string(),
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
        _other => "the value was passed by value earlier",
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
    if ctx.is_slots_place(p) {
        return Diagnostic {
            name: "slots.use_after_move".into(),
            title: format!("`{}` has been moved out", p.render()),
            span,
            label,
            notes: vec![(
                "note".into(),
                "owner slots move with their allocation and occupancy; the old place no longer names it"
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

/// Query one snapshot of the checker's move state.
///
/// Call admission keeps the state from before argument evaluation so it can
/// distinguish a loan that was dead on entry (`*.use_after_move`) from a live
/// loan moved by another argument in the same call (`borrow.moved_in_call`).
/// Both queries use the same containment rule as ordinary expression reads.
fn place_is_moved(moved: &HashSet<Place>, place: &Place) -> bool {
    moved.iter().any(|moved_place| moved_place.contains(place))
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
        ty @ (Ty::Int(
            IntTy::U8
            | IntTy::U16
            | IntTy::U32
            | IntTy::U64
            | IntTy::I8
            | IntTy::I16
            | IntTy::I32
            | IntTy::I64,
        )
        | Ty::Param(_)) => Ok(ty),
        other @ (Ty::Int(IntTy::TParam(_))
        | Ty::Bool
        | Ty::Class(_)
        | Ty::Record(_)
        | Ty::Array(_)
        | Ty::Slots(_)
        | Ty::Option(_)
        | Ty::OptionRaw(_)
        | Ty::Res(_)
        | Ty::Raw(_)
        | Ty::RawRecord(_)
        | Ty::Borrow(..)
        | Ty::Unit) => Err(Diagnostic {
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
        ExprKind::BoolLit(_)
        | ExprKind::Var(_)
        | ExprKind::Unary { .. }
        | ExprKind::Binary { .. }
        | ExprKind::Call { .. }
        | ExprKind::Index { .. }
        | ExprKind::Len { .. }
        | ExprKind::RawOp { .. }
        | ExprKind::DeviceOp { .. }
        | ExprKind::ResOp { .. }
        | ExprKind::SlotOp { .. }
        | ExprKind::Widen { .. }
        | ExprKind::Narrow { .. }
        | ExprKind::IsSome { .. }
        | ExprKind::OptValue { .. }
        | ExprKind::OptTake { .. }
        | ExprKind::SomeE(_)
        | ExprKind::NoneE
        | ExprKind::ArrayLit(_)
        | ExprKind::AllocArray { .. }
        | ExprKind::SelfField { .. }
        | ExprKind::SelfFieldLen { .. }
        | ExprKind::SelfFieldIndex { .. }
        | ExprKind::CtorCall { .. }
        | ExprKind::ClassField { .. }
        | ExprKind::RecordField { .. }
        | ExprKind::ClassFieldLen { .. }
        | ExprKind::ClassFieldIndex { .. }
        | ExprKind::TraitCall { .. }
        | ExprKind::MethodCall { .. }
        | ExprKind::Borrow { .. }
        | ExprKind::RecordLit { .. } => false,
    }
}

fn find_cycle(graph: &HashMap<CallOwner, Vec<CallOwner>>) -> Option<CallOwner> {
    #[derive(Clone, Copy, PartialEq)]
    enum State {
        Unvisited,
        InProgress,
        Done,
    }
    let mut state: HashMap<&CallOwner, State> =
        graph.keys().map(|key| (key, State::Unvisited)).collect();

    fn dfs<'a>(
        node: &'a CallOwner,
        graph: &'a HashMap<CallOwner, Vec<CallOwner>>,
        state: &mut HashMap<&'a CallOwner, State>,
    ) -> Option<CallOwner> {
        state.insert(node, State::InProgress);
        if let Some(callees) = graph.get(node) {
            for callee in callees {
                match state.get(callee).copied() {
                    Some(State::InProgress) => return Some(callee.clone()),
                    Some(State::Unvisited) => {
                        if let Some(found) = dfs(callee, graph, state) {
                            return Some(found);
                        }
                    }
                    Some(State::Done) | None => {}
                }
            }
        }
        state.insert(node, State::Done);
        None
    }

    let mut keys: Vec<&CallOwner> = graph.keys().collect();
    keys.sort();
    for key in keys {
        if state.get(key) == Some(&State::Unvisited) {
            if let Some(found) = dfs(key, graph, &mut state) {
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

    #[test]
    fn trusted_checker_and_vcgen_do_not_use_bare_match_catchalls() {
        for (name, source) in [
            ("check.rs", include_str!("check.rs")),
            ("vcgen.rs", include_str!("vcgen.rs")),
        ] {
            let production_source = source.split("#[cfg(test)]").next().unwrap_or(source);
            for (line_index, line) in production_source.lines().enumerate() {
                let code = line.split("//").next().unwrap_or("").trim();
                let compact: String = code.chars().filter(|ch| !ch.is_whitespace()).collect();
                let bare_arm = compact.starts_with("_=>");
                let leading_tuple_slot = compact.starts_with("(_,");
                let trailing_tuple_slot = compact.starts_with('(')
                    && (compact.contains(",_)=>") || compact.contains(",_)if"));

                assert!(
                    !bare_arm && !leading_tuple_slot && !trailing_tuple_slot,
                    "{name}:{} uses a wildcard match catch-all in trusted semantic code: {code}",
                    line_index + 1
                );
            }
        }
    }

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

    #[test]
    fn borrowed_whitelisted_resources_remain_extern_abi_parameters() {
        let mut program = parse_program(
            r#"
pub extern "C" #[audit(id := "test.borrowed-resource.v1",
                        reason := "pins the established erased-resource ABI")]
fn foreign(raw<u8> p, resource &RawSpan shared,
           resource &mut RawSpan unique, resource &mut OpenFile file,
           resource &mut PosixWorld world);
"#,
        );
        check(&mut program).expect("borrowed whitelisted resources remain ABI-admitted");
    }

    #[test]
    fn extern_resource_abi_table_covers_owned_and_borrowed_forms() {
        for kind in [ResKind::RawSpan, ResKind::OpenFile, ResKind::PosixWorld] {
            let owned = Ty::Res(kind);
            let shared = Ty::Borrow(Mutability::Shared, Box::new(owned.clone()));
            let unique = Ty::Borrow(Mutability::Mut, Box::new(owned.clone()));

            assert!(extern_parameter_abi_allowed(&owned));
            assert!(extern_parameter_abi_allowed(&shared));
            assert!(extern_parameter_abi_allowed(&unique));
        }

        let rejected = Ty::Res(ResKind::PointsToU64);
        for ty in [
            rejected.clone(),
            Ty::Borrow(Mutability::Shared, Box::new(rejected.clone())),
            Ty::Borrow(Mutability::Mut, Box::new(rejected)),
        ] {
            assert!(!extern_parameter_abi_allowed(&ty));
        }
    }

    #[test]
    fn lexical_child_bindings_are_not_visible_after_their_control_edge() {
        let cases = [
            r#"
fn subject() -> u64 {
    if (true) {
        mut u64 hidden = 0;
    }
    hidden = 1;
    return hidden;
}
"#,
            r#"
fn subject() -> u64 {
    mut u64 iteration = 0;
    /// invariant iteration <= 1
    /// variant 1 - iteration
    while (iteration < 1) {
        mut u64 hidden = iteration;
        iteration = iteration + 1;
    }
    hidden = 1;
    return hidden;
}
"#,
        ];

        for source in cases {
            let mut program = monomorphized_program(source);
            let error = check_error(&mut program);
            assert_eq!(error.name, "type.unknown_variable");
            assert_ne!(error.name, "internal.check.control_outline");
            assert_ne!(error.name, "internal.check.control_plan");
        }
    }

    #[test]
    fn source_type_and_duplicate_diagnostics_precede_control_sealing() {
        let mut duplicate = monomorphized_program(
            r#"
fn subject() -> u64 {
    u64 value = 0;
    u64 value = 1;
    return value;
}
"#,
        );
        assert_eq!(check_error(&mut duplicate).name, "type.duplicate_name");

        let mut malformed = monomorphized_program(
            r#"
fn subject() {
    u64 value = 0;
}
"#,
        );
        let Stmt::Decl { ty, .. } = &mut malformed.fns[0].body[0] else {
            panic!("fixture declaration changed shape");
        };
        *ty = Ty::array(Ty::array(Ty::Int(IntTy::U64)));
        let error = check_error(&mut malformed);
        assert_eq!(error.name, "type.array_payload_unsupported");
        assert_ne!(error.name, "internal.check.control_outline");
        assert_ne!(error.name, "internal.check.control_plan");
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
    fn only_fresh_class_results_can_be_discarded_as_temporaries() {
        let mut projected = monomorphized_program(
            r#"
class Child {
    u64 value;

    init new() {
        self.value = 1;
    }
}

class Parent {
    Child child;

    init new() {
        self.child = Child::new();
    }

    fn discard_child(&mut self) {
    }
}
"#,
        );
        // The source parser deliberately admits only calls as expression
        // statements. Forge the otherwise well-typed projection shape to pin
        // the checker's trust boundary too: an internal AST producer must not
        // turn a read of an installed owner into a temporary destruction.
        projected.classes[1].methods[0]
            .f
            .body
            .push(Stmt::ExprStmt(Expr {
                kind: ExprKind::SelfField {
                    field: "child".into(),
                },
                span: Span::new(200, 210),
                ty: Some(Ty::Class(0)),
            }));
        let error = check_error(&mut projected);
        assert_eq!(error.name, "type.class_temporary_source");
        assert!(error.title.contains("self.child"));

        let mut fresh = monomorphized_program(
            r#"
class Child {
    u64 value;

    init new() {
        self.value = 1;
    }
}

fn make_child() -> Child {
    return Child::new();
}

class Maker {
    init new() {}

    fn make(&self) -> Child {
        return Child::new();
    }
}

fn discard_fresh_results() {
    make_child();
    var maker = Maker::new();
    maker.make();
}
"#,
        );
        // Non-generic constructor calls are not source-level statement
        // starters, but an internal producer may still form the legitimate
        // temporary. Keep that side of the boundary pinned beside the two
        // source-admitted call forms.
        fresh.fns[1].body.insert(
            0,
            Stmt::ExprStmt(Expr {
                kind: ExprKind::CtorCall {
                    class: "Child".into(),
                    class_span: Span::new(300, 305),
                    type_args: Vec::new(),
                    init: "new".into(),
                    args: Vec::new(),
                },
                span: Span::new(300, 312),
                ty: Some(Ty::Class(0)),
            }),
        );
        let checked = check(&mut fresh).expect("fresh class results are owned temporaries");
        let body = &fresh.fns[1].body;
        let discarded = [&body[0], &body[1], &body[3]];
        for statement in discarded {
            let Stmt::ExprStmt(result) = statement else {
                panic!("expected discarded fresh class result");
            };
            assert_eq!(result.ty, Some(Ty::Class(0)));
        }
        let owner = CallOwner::Function("discard_fresh_results".into());
        let discard_transfers: Vec<_> = checked
            .ownership
            .value_transfers_for_owner(&owner)
            .filter(|(key, _)| key.sink == ValueTransferSink::DiscardTemporary)
            .collect();
        assert_eq!(discard_transfers.len(), 3);
        for (key, transfer) in discard_transfers {
            assert_eq!(key.owner, owner);
            assert_eq!(key.span, transfer.span);
            assert_eq!(transfer.source, None);
            assert_eq!(transfer.value_ty, Ty::Class(0));
            assert_eq!(transfer.kind, ValueTransferKind::Fresh);
        }
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
    fn nested_argument_moves_still_conflict_with_an_outer_recorded_loan() {
        let mut program = monomorphized_program(
            r#"
fn hand_over([u64] values) -> [u64] {
    return values;
}

fn use_both(&mut [u64] borrowed, [u64] owned) {}

fn bad() {
    mut [u64] values = alloc_array<u64>(1, 0);
    use_both(&mut values, hand_over(values));
}
"#,
        );
        assert_eq!(check_error(&mut program).name, "borrow.moved_in_call");
    }

    #[test]
    fn later_nested_mutations_conflict_with_pending_call_state_in_every_call_shape() {
        const PRELUDE: &str = r#"
class TimingItem {
    u64 value;

    init new(u64 initial) {
        self.value = initial;
    }

    fn set_nine(&mut self) {
        self.value = 9;
    }

    fn receive(&self, u64 marker) {}
}

fn mutate(&mut TimingItem item) -> u64 {
    item.set_nine();
    return 0;
}

fn observe(&TimingItem item, u64 marker) {}

class TimingTarget {
    u64 marker;

    init make(&TimingItem item, u64 marker) {
        self.marker = marker;
    }

    init empty() {
        self.marker = 0;
    }

    fn observe(&self, &TimingItem item, u64 marker) {}
}
"#;

        let cases = [
            // An explicit free-call loan captures state before the later
            // nested call tries to mutate it.
            r#"
fn bad() {
    var mut item = TimingItem::new(1);
    observe(&item, mutate(&mut item));
}
"#,
            // Constructors use the same argument-evaluation rule.
            r#"
fn bad() {
    var mut item = TimingItem::new(1);
    var target = TimingTarget::make(&item, mutate(&mut item));
}
"#,
            // So do explicit arguments of a method on a disjoint receiver.
            r#"
fn bad() {
    var target = TimingTarget::empty();
    var mut item = TimingItem::new(1);
    target.observe(&item, mutate(&mut item));
}
"#,
            // A method's implicit receiver reservation captures state before
            // every explicit argument, so it is subject to the same rule.
            r#"
fn bad() {
    var mut item = TimingItem::new(1);
    item.receive(mutate(&mut item));
}
"#,
        ];

        for source in cases {
            let mut program = monomorphized_program(&format!("{PRELUDE}\n{source}"));
            let error = check_error(&mut program);
            assert_eq!(error.name, "borrow.conflict", "for:\n{source}");
            assert!(error.title.contains("later mutation"));
            assert!(
                error
                    .notes
                    .iter()
                    .any(|(_, note)| note.contains("left-to-right"))
            );
        }
    }

    #[test]
    fn completed_nested_mutations_may_precede_a_later_call_reservation() {
        let mut program = monomorphized_program(
            r#"
class TimingItem {
    u64 value;

    init new(u64 initial) {
        self.value = initial;
    }

    fn set_nine(&mut self) {
        self.value = 9;
    }

    fn receive(&self, u64 marker) {}
}

fn mutate(&mut TimingItem item) -> u64 {
    item.set_nine();
    return 0;
}

fn observe(u64 marker, &TimingItem item) {}

class TimingTarget {
    u64 marker;

    init make(u64 marker, &TimingItem item) {
        self.marker = marker;
    }

    init empty() {
        self.marker = 0;
    }

    fn observe(&self, u64 marker, &TimingItem item) {}
}

fn good() {
    var mut free_item = TimingItem::new(1);
    observe(mutate(&mut free_item), &free_item);

    var mut ctor_item = TimingItem::new(1);
    var made = TimingTarget::make(mutate(&mut ctor_item), &ctor_item);

    var target = TimingTarget::empty();
    var mut method_item = TimingItem::new(1);
    target.observe(mutate(&mut method_item), &method_item);

    var receiver = TimingItem::new(1);
    var mut disjoint = TimingItem::new(1);
    receiver.receive(mutate(&mut disjoint));
}
"#,
        );

        check(&mut program).expect(
            "a nested mutation that completes before a later reservation captures state is sound",
        );
    }

    #[test]
    fn pending_unique_reservations_allow_completed_reads_but_not_callee_aliases() {
        let mut reads = monomorphized_program(
            r#"
fn nested_len(&[u64] values) -> u64 {
    return values.len;
}

fn hold(&mut [u64] values, u64 nested, u64 direct) {}

class ReadItem {
    u64 value;

    init new(u64 value) {
        self.value = value;
    }

    fn get(&self) -> u64 {
        return self.value;
    }

    fn hold(&mut self, u64 nested, u64 direct) {}
}

fn read_item(&ReadItem item) -> u64 {
    return item.get();
}

fn good() {
    mut [u64] values = [1];
    hold(&mut values, nested_len(&values), values.len);

    var mut item = ReadItem::new(1);
    item.hold(read_item(&item), item.get());
}
"#,
        );
        check(&mut reads).expect(
            "transient nested shared reads and direct scalar reads finish before the callee",
        );

        let mut direct_alias = monomorphized_program(
            r#"
fn alias(&mut [u64] unique, &[u64] shared) {}

fn bad() {
    mut [u64] values = [1];
    alias(&mut values, &values);
}
"#,
        );
        assert_eq!(check_error(&mut direct_alias).name, "borrow.conflict");
    }

    #[test]
    fn sealed_operations_retain_the_same_pending_loan_stability_rule() {
        let mut program = monomorphized_program(
            r#"
fn mutate_map(
    resource &mut ResourceMap<u64, PointsTo<u64>> cells
) -> u64 {
    return 0;
}

fn bad(
    resource &mut ResourceMap<u64, PointsTo<u64>> cells,
    resource PointsTo<u64> cell
) {
    resource_map_put(&mut cells, mutate_map(&mut cells), cell);
}
"#,
        );

        let error = check_error(&mut program);
        assert_eq!(error.name, "borrow.conflict");
        assert!(error.title.contains("later mutation"));
    }

    #[test]
    fn sealed_operations_reject_nested_moves_that_invalidate_pending_loans() {
        let mut program = monomorphized_program(
            r#"
fn move_map(
    resource ResourceMap<u64, PointsTo<u64>> cells
) -> u64 {
    return 0;
}

fn bad(resource PointsTo<u64> cell) {
    mut resource ResourceMap<u64, PointsTo<u64>> cells = resource_map_empty();
    resource_map_put(&mut cells, move_map(cells), cell);
}
"#,
        );

        let error = check_error(&mut program);
        assert_eq!(error.name, "borrow.moved_in_call");
        assert!(error.title.contains("resource_map_put"));
        assert!(error.label.contains("argument evaluation moves"));
    }

    #[test]
    fn sealed_operations_allow_completed_or_disjoint_effects_before_a_later_loan() {
        let mut program = monomorphized_program(
            r#"
fn move_map_to_pointer(
    raw<u8> pointer,
    resource ResourceMap<u64, PointsTo<u64>> moved
) -> raw<u8> {
    return pointer;
}

fn good(
    raw<u8> pointer,
    resource &PointsTo<u64> cell,
    resource ResourceMap<u64, PointsTo<u64>> moved
) -> u64 {
    unsafe {
        return raw_cell_read_u64(move_map_to_pointer(pointer, moved), &cell);
    }
}

fn poll(resource &mut Uart uart) -> u8 {
    return 65;
}

fn good_uart(resource &mut Uart uart) {
    unsafe {
        uart_write(poll(&mut uart), &mut uart);
    }
}
"#,
        );

        check(&mut program)
            .expect("completed mutation and disjoint-move effects may precede a later sealed loan");
    }

    #[test]
    fn retained_trait_signatures_admit_exactly_the_integer_proof_domain() {
        let span = Span::new(10, 20);
        for ty in [
            Ty::Int(IntTy::U64),
            Ty::Int(IntTy::TParam(0)),
            Ty::Param(TypeParamId::from_legacy(0)),
        ] {
            trait_param_ty(&ty, span)
                .unwrap_or_else(|_| panic!("`{}` is a trait proof value", ty.name()));
            trait_return_ty(&ty, "proof_value", span)
                .unwrap_or_else(|_| panic!("`{}` is a trait proof result", ty.name()));
        }

        for ty in [
            Ty::Bool,
            Ty::Class(0),
            Ty::Record(0),
            Ty::array(Ty::Int(IntTy::U64)),
            Ty::slots(Ty::Int(IntTy::U64)),
            Ty::OptionRaw(0),
            Ty::Res(ResKind::RawSpan),
            Ty::Raw(IntTy::U8),
            Ty::RawRecord(0),
            Ty::borrow(Mutability::Shared, Ty::Res(ResKind::RawSpan)),
            Ty::Unit,
        ] {
            let parameter = trait_param_ty(&ty, span)
                .expect_err(&format!("`{}` is not a trait proof value", ty.name()));
            assert_eq!(parameter.name, "type.trait_param_unsupported");
            assert_eq!(parameter.span, span);

            let result = trait_return_ty(&ty, "closed", span)
                .expect_err(&format!("`{}` is not a trait proof result", ty.name()));
            assert_eq!(result.name, "type.trait_return_unsupported");
            assert_eq!(result.span, span);
        }

        let value_option = Ty::option(Ty::Int(IntTy::U64));
        assert_eq!(
            trait_param_ty(&value_option, span)
                .expect_err("an option is not an integer proof value")
                .name,
            "type.trait_param_unsupported"
        );
        assert_eq!(
            trait_return_ty(&value_option, "closed", span)
                .expect_err("an option is not an integer proof result")
                .name,
            "type.trait_option_return"
        );

        let affine_option = Ty::affine_array_option(Ty::Bool);
        for refusal in [
            trait_param_ty(&affine_option, span)
                .expect_err("an affine option cannot enter a trait signature"),
            trait_return_ty(&affine_option, "closed", span)
                .expect_err("an affine option cannot leave a trait signature"),
        ] {
            assert_eq!(refusal.name, "type.affine_option_trait");
        }
    }

    #[test]
    fn moved_class_method_receivers_are_rejected_as_place_uses() {
        let mut program = monomorphized_program(
            r#"
class Item {
    u64 value;

    init new(u64 value) {
        self.value = value;
    }

    fn get(&self) -> u64 {
        return self.value;
    }
}

fn consume(Item item) {}

fn bad() -> u64 {
    var item = Item::new(7);
    consume(item);
    return item.get();
}
"#,
        );

        let error = check_error(&mut program);
        assert_eq!(error.name, "class.use_after_move");
        assert!(error.title.contains("item"));

        let mut field_receiver = monomorphized_program(
            r#"
class Item {
    u64 value;

    init new(u64 value) {
        self.value = value;
    }
}

fn consume(Item item) {}

fn bad() -> u64 {
    var item = Item::new(7);
    consume(item);
    return item.value;
}
"#,
        );
        assert_eq!(
            check_error(&mut field_receiver).name,
            "class.use_after_move"
        );

        let mut moved_during_call = monomorphized_program(
            r#"
class Item {
    u64 value;

    init new(u64 value) {
        self.value = value;
    }

    fn absorb(&self, Item other) {}
}

fn bad() {
    var item = Item::new(7);
    item.absorb(item);
}
"#,
        );
        assert_eq!(
            check_error(&mut moved_during_call).name,
            "borrow.moved_in_call"
        );
    }

    #[test]
    fn ordinary_free_constructor_and_method_calls_retain_live_places() {
        let mut program = monomorphized_program(
            r#"
class Item {
    u64 value;

    init new(u64 value) {
        self.value = value;
    }

    fn get(&self) -> u64 {
        return self.value;
    }
}

fn read(&Item item) -> u64 {
    return item.get();
}

class Holder {
    Item item;

    init wrap(Item item) {
        self.item = item;
    }

    fn read(&self) -> u64 {
        return read(&self.item);
    }
}

fn exercise() -> u64 {
    var item = Item::new(7);
    var holder = Holder::wrap(item);
    return holder.read();
}
"#,
        );

        let checked = check(&mut program).expect("ordinary live call places should be admitted");

        let read_owner = CallOwner::Function("read".into());
        let read_calls: Vec<_> = checked.ownership.calls.for_owner(&read_owner).collect();
        assert_eq!(read_calls.len(), 1);
        let (_, item_get) = read_calls[0];
        assert_eq!(
            item_get.key.target,
            CallTarget::Method {
                class: "Item".into(),
                method: "get".into(),
            }
        );
        assert_eq!(
            item_get
                .receiver
                .as_ref()
                .expect("method call has an implicit loan")
                .transition
                .place,
            Place::local("item")
        );

        let holder_read_owner = CallOwner::Method {
            class: "Holder".into(),
            method: "read".into(),
        };
        let holder_read_calls: Vec<_> = checked
            .ownership
            .calls
            .for_owner(&holder_read_owner)
            .collect();
        assert_eq!(holder_read_calls.len(), 1);
        let (_, field_read) = holder_read_calls[0];
        assert_eq!(field_read.key.target, CallTarget::Function("read".into()));
        let CallArgumentEffect::Loan(field_loan) = &field_read.arguments[0].effect else {
            panic!("the free call should retain its direct field loan");
        };
        assert_eq!(field_loan.place, Place::field("self", "item"));

        let exercise_owner = CallOwner::Function("exercise".into());
        let exercise_calls: Vec<_> = checked
            .ownership
            .calls
            .for_owner(&exercise_owner)
            .map(|(_, call)| call)
            .collect();
        assert_eq!(exercise_calls.len(), 3);
        assert!(exercise_calls.iter().any(|call| {
            call.key.target
                == CallTarget::Constructor {
                    class: "Item".into(),
                    init: "new".into(),
                }
        }));
        assert!(exercise_calls.iter().any(|call| {
            call.key.target
                == CallTarget::Constructor {
                    class: "Holder".into(),
                    init: "wrap".into(),
                }
        }));
        let holder_method = exercise_calls
            .iter()
            .find(|call| {
                call.key.target
                    == CallTarget::Method {
                        class: "Holder".into(),
                        method: "read".into(),
                    }
            })
            .expect("ordinary method call record");
        assert_eq!(
            holder_method
                .receiver
                .as_ref()
                .expect("method call has an implicit loan")
                .transition
                .place,
            Place::local("holder")
        );
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

    #[test]
    fn slot_transitions_actions_and_loop_mutations_share_exact_checked_identity() {
        let mut program = monomorphized_program(
            r#"
fn cycle(u64 length) -> u64 {
    mut slots<u64> cells = alloc_slots<u64>(length);
    slot_put(&mut cells, 0, 7);
    mut u64 i = 0;
    var observed = cells.len;
    /// invariant i <= 1
    /// variant 1 - i
    while (i < 1) {
        var value = slot_take(&mut cells, i);
        slot_put(&mut cells, i, value);
        i = i + 1;
    }
    return slot_take(&mut cells, 0);
}
"#,
        );
        let checked = check(&mut program).expect("the checker admits the bounded slot surface");
        let owner = CallOwner::Function("cycle".into());
        let transitions: Vec<_> = checked
            .ownership
            .slot_transitions_for_owner(&owner)
            .map(|(_, transition)| transition)
            .collect();
        assert_eq!(transitions.len(), 5);
        assert_eq!(
            transitions
                .iter()
                .filter(|transition| matches!(
                    transition.kind,
                    CheckedSlotTransitionKind::Alloc { .. }
                ))
                .count(),
            1
        );
        assert_eq!(
            transitions
                .iter()
                .filter(|transition| matches!(
                    transition.kind,
                    CheckedSlotTransitionKind::Take { .. }
                ))
                .count(),
            2
        );
        assert_eq!(
            transitions
                .iter()
                .filter(|transition| matches!(
                    transition.kind,
                    CheckedSlotTransitionKind::Put { .. }
                ))
                .count(),
            2
        );

        let loop_effects = checked
            .ownership
            .loops_for_owner(&owner)
            .next()
            .expect("the loop has one checked effect record")
            .1;
        let slot_mutations: Vec<_> = loop_effects
            .mutations
            .iter()
            .filter_map(|mutation| match mutation {
                CheckedMutation::Slot {
                    operation,
                    container,
                    payload,
                    ..
                } => Some((*operation, container.clone(), payload.clone())),
                CheckedMutation::DirectWrite { .. }
                | CheckedMutation::UniqueLoan(_)
                | CheckedMutation::OptionTake { .. }
                | CheckedMutation::ExposureRebuild { .. } => None,
            })
            .collect();
        assert_eq!(
            slot_mutations,
            vec![
                (
                    CheckedSlotMutationKind::Take,
                    Place::local("cells"),
                    Ty::Int(IntTy::U64),
                ),
                (
                    CheckedSlotMutationKind::Put,
                    Place::local("cells"),
                    Ty::Int(IntTy::U64),
                ),
            ]
        );

        let body = checked
            .control
            .body(&owner, program.fns[0].span)
            .expect("cycle has a retained control body");
        let actions: Vec<_> = body.plan().slot_actions().collect();
        assert_eq!(actions.len(), transitions.len());
        for action in &actions {
            assert_eq!(
                body.plan()
                    .slot_action_trap_sites(action)
                    .expect("every action retains its exact trap identities")
                    .len(),
                2
            );
            assert_eq!(action.effect_key().owner, owner);
            assert_eq!(action.payload(), &Ty::Int(IntTy::U64));
            if let SlotActionKind::Put {
                container,
                value_transfer,
                staging,
                ..
            } = action.kind()
            {
                assert_eq!(container, &Place::local("cells"));
                assert!(staging.root().starts_with("$sable$slot_put_value$"));
                let transfer = checked
                    .ownership
                    .value_transfer(value_transfer)
                    .expect("put action links its checker-authored transfer");
                assert_eq!(transfer.value_ty, Ty::Int(IntTy::U64));
            }
        }

        let Stmt::VarDecl { init: len, .. } = &program.fns[0].body[3] else {
            panic!("expected the checked `.len` binding");
        };
        assert_eq!(len.ty, Some(Ty::Int(IntTy::U64)));
    }

    #[test]
    fn slot_owners_move_as_whole_locals_and_direct_self_fields() {
        let mut program = monomorphized_program(
            r#"
class Pool {
    slots<u64> cells;

    init new(u64 length) {
        self.cells = alloc_slots<u64>(length);
    }

    fn replace(&mut self, u64 length) -> u64 {
        mut slots<u64> next = alloc_slots<u64>(length);
        var previous = self.cells;
        self.cells = next;
        var installed = self.cells.len;
        return installed;
    }

    fn roundtrip(&mut self, u64 value) -> u64 {
        slot_put(&mut self.cells, 0, value);
        return slot_take(&mut self.cells, 0);
    }
}

fn local_move(u64 length) -> u64 {
    mut slots<u64> first = alloc_slots<u64>(length);
    var moved = first;
    mut slots<u64> replacement = alloc_slots<u64>(length);
    replacement = moved;
    return replacement.len;
}

fn observe(Pool pool) -> u64 {
    return pool.cells.len;
}
"#,
        );
        let checked =
            check(&mut program).expect("whole slot owners move without copying their allocation");

        let method = &program.classes[0].methods[0].f;
        let Stmt::VarDecl {
            init: moved, ty, ..
        } = &method.body[1]
        else {
            panic!("expected inferred self-field move");
        };
        assert_eq!(ty.as_ref(), Some(&Ty::slots(Ty::Int(IntTy::U64))));
        assert_eq!(moved.ty.as_ref(), ty.as_ref());
        let Stmt::VarDecl { init: len, .. } = &method.body[3] else {
            panic!("expected self-field length observation");
        };
        assert_eq!(len.ty, Some(Ty::Int(IntTy::U64)));

        let roundtrip = CallOwner::Method {
            class: "Pool".into(),
            method: "roundtrip".into(),
        };
        let transitions: Vec<_> = checked
            .ownership
            .slot_transitions_for_owner(&roundtrip)
            .map(|(_, transition)| transition)
            .collect();
        assert_eq!(transitions.len(), 2);
        assert!(
            transitions.iter().all(|transition| {
                transition.container() == Some(&Place::field("self", "cells"))
            })
        );

        let local_owner = CallOwner::Function("local_move".into());
        let local_plan = checked
            .control
            .body(&local_owner, program.fns[0].span)
            .expect("local_move has a retained control body")
            .plan();
        let replacement = local_plan
            .assignments()
            .find(|action| action.destination() == &Place::local("replacement"))
            .expect("whole-slot reassignment has an exact replacement action");
        assert!(replacement.previous().is_some());
        assert!(matches!(
            replacement.staging(),
            crate::control::AssignmentStaging::Temporary(_)
        ));
        let Stmt::Return {
            value: Some(class_len),
            ..
        } = &program.fns[1].body[0]
        else {
            panic!("expected arbitrary class-field length observation");
        };
        assert_eq!(class_len.ty, Some(Ty::Int(IntTy::U64)));
    }

    #[test]
    fn slot_positions_mutability_and_direct_cell_access_fail_by_name() {
        let cases = [
            (
                "fn bad() { var cells = alloc_slots<u64>(1); }",
                "slots.operation_position",
            ),
            (
                "fn bad() { mut slots<u64> cells = alloc_slots<u64>(1); cells = alloc_slots<u64>(1); }",
                "slots.operation_position",
            ),
            (
                "fn bad() { mut slots<u64> cells = alloc_slots<u64>(1); u64 value = slot_put(&mut cells, 0, 1); }",
                "slots.operation_position",
            ),
            (
                "fn bad() { mut slots<u64> cells = alloc_slots<u64>(1); slot_take(&mut cells, 0); }",
                "slots.operation_position",
            ),
            (
                "fn id(u64 value) -> u64 { return value; } fn bad() -> u64 { mut slots<u64> cells = alloc_slots<u64>(1); return id(slot_take(&mut cells, 0)); }",
                "slots.operation_position",
            ),
            (
                "fn bad() { slots<u64> cells = alloc_slots<u64>(1); var value = slot_take(&mut cells, 0); }",
                "slots.container_mutability",
            ),
            (
                "fn bad() { mut slots<u64> cells = alloc_slots<u64>(1); var value = cells[0]; }",
                "slots.index_unsupported",
            ),
            (
                "fn bad() { mut slots<u64> cells = alloc_slots<u64>(1); cells[0] = 1; }",
                "slots.store_unsupported",
            ),
        ];
        for (source, expected) in cases {
            let mut program = monomorphized_program(source);
            assert_eq!(check_error(&mut program).name, expected, "{source}");
        }

        let mut projected = monomorphized_program(
            r#"
class Pool {
    slots<u64> cells;
    init new() { self.cells = alloc_slots<u64>(1); }
}

fn bad(Pool pool) -> u64 {
    return slot_take(&mut pool.cells, 0);
}
"#,
        );
        assert_eq!(check_error(&mut projected).name, "slots.container_place");

        let mut ordinary_borrow = monomorphized_program(
            r#"
class Pool {
    slots<u64> cells;
    init new() { self.cells = alloc_slots<u64>(1); }
    fn bad(&mut self) { var loan = &mut self.cells; }
}
"#,
        );
        assert_eq!(
            check_error(&mut ordinary_borrow).name,
            "class.mut_field_borrow"
        );

        let mut shared_self = monomorphized_program(
            r#"
class Pool {
    slots<u64> cells;
    init new() { self.cells = alloc_slots<u64>(1); }
    fn bad(&mut self) -> u64 { return slot_take(&self.cells, 0); }
}
"#,
        );
        assert_eq!(
            check_error(&mut shared_self).name,
            "slots.container_mutability"
        );

        let mut immutable_self = monomorphized_program(
            r#"
class Pool {
    slots<u64> cells;
    init new() { self.cells = alloc_slots<u64>(1); }
    fn bad(&self) { slot_put(&mut self.cells, 0, 1); }
}
"#,
        );
        assert_eq!(
            check_error(&mut immutable_self).name,
            "type.mutate_shared_self"
        );

        for (source, expected) in [
            (
                r#"
class Pool {
    slots<u64> cells;
    init new() { self.cells = alloc_slots<u64>(1); }
    fn bad(&self) -> u64 { return self.cells[0]; }
}
"#,
                "slots.index_unsupported",
            ),
            (
                r#"
class Pool {
    slots<u64> cells;
    init new() { self.cells = alloc_slots<u64>(1); }
    fn bad(&mut self) { self.cells[0] = 1; }
}
"#,
                "slots.store_unsupported",
            ),
            (
                r#"
class Pool {
    slots<u64> cells;
    init new() { self.cells = alloc_slots<u64>(1); }
}
fn bad(Pool pool) -> u64 { return pool.cells[0]; }
"#,
                "slots.index_unsupported",
            ),
            (
                r#"
fn bad() -> u64 {
    mut slots<u64> first = alloc_slots<u64>(1);
    var moved = first;
    return first.len;
}
"#,
                "slots.use_after_move",
            ),
            (
                r#"
class Pool {
    slots<u64> cells;
    init new() { self.cells = alloc_slots<u64>(1); }
}
fn bad(Pool pool) -> u64 {
    var moved = pool;
    return pool.cells.len;
}
"#,
                "class.use_after_move",
            ),
        ] {
            let mut program = monomorphized_program(source);
            assert_eq!(check_error(&mut program).name, expected, "{source}");
        }
    }

    #[test]
    fn forged_slot_bindings_cannot_bypass_owned_form_and_initializer_gates() {
        let borrowed_slots = Ty::borrow(Mutability::Mut, Ty::slots(Ty::Int(IntTy::U64)));

        let mut local = monomorphized_program("fn bad() { u64 value; }");
        let Stmt::Decl { ty, .. } = &mut local.fns[0].body[0] else {
            panic!("expected explicit local");
        };
        *ty = borrowed_slots.clone();
        assert_eq!(
            check_error(&mut local).name,
            "type.borrow_local_unsupported"
        );

        let mut uninitialized = monomorphized_program("fn bad() { u64 value; }");
        let Stmt::Decl { ty, .. } = &mut uninitialized.fns[0].body[0] else {
            panic!("expected explicit local");
        };
        *ty = Ty::slots(Ty::Int(IntTy::U64));
        assert_eq!(
            check_error(&mut uninitialized).name,
            "type.slot_initializer"
        );

        let mut inferred = monomorphized_program("fn bad() { var value = true; }");
        let Stmt::VarDecl { ty, .. } = &mut inferred.fns[0].body[0] else {
            panic!("expected inferred local");
        };
        *ty = Some(Ty::slots(Ty::Int(IntTy::U64)));
        assert_eq!(check_error(&mut inferred).name, "slots.inferred_type");

        let mut field = monomorphized_program(
            r#"
class Owner {
    u64 value;
    init new() { self.value = 0; }
}
"#,
        );
        field.classes[0].fields[0].ty = borrowed_slots;
        assert_eq!(check_error(&mut field).name, "type.slot_owner_binding");

        let mut malformed =
            monomorphized_program("fn bad() { mut slots<u64> cells = alloc_slots<u64>(1); }");
        let Stmt::Decl {
            init: Some(allocation),
            ..
        } = &mut malformed.fns[0].body[0]
        else {
            panic!("expected slot allocation");
        };
        let ExprKind::SlotOp { args, .. } = &mut allocation.kind else {
            panic!("expected slot operation");
        };
        args.clear();
        assert_eq!(
            check_error(&mut malformed).name,
            "internal.check.slot_operation_arity"
        );
    }

    #[test]
    fn slot_payload_admission_is_an_explicit_post_substitution_allow_list() {
        for payload in [
            Ty::Int(IntTy::U64),
            Ty::Bool,
            Ty::Param(TypeParamId::from_legacy(0)),
            Ty::Record(0),
            Ty::Class(0),
        ] {
            slot_payload_ty(&payload, Span::new(1, 2)).unwrap_or_else(|error| {
                panic!("`{}` was refused: {}", payload.name(), error.title)
            });
        }
        for payload in [
            Ty::array(Ty::Bool),
            Ty::slots(Ty::Bool),
            Ty::option(Ty::Bool),
            Ty::Res(ResKind::RawSpan),
            Ty::Raw(IntTy::U8),
            Ty::borrow(Mutability::Shared, Ty::Class(0)),
            Ty::Unit,
        ] {
            assert_eq!(
                slot_payload_ty(&payload, Span::new(1, 2))
                    .expect_err("nested/authority slot payloads stay closed")
                    .name,
                "type.slot_payload_unsupported",
                "{}",
                payload.name()
            );
        }
        assert_eq!(
            slot_payload_ty(&Ty::Int(IntTy::TParam(0)), Span::new(1, 2))
                .expect_err("legacy integer parameters are not aggregate payloads")
                .name,
            "type.aggregate_payload_noncanonical"
        );
        assert_eq!(
            validate_aggregate_ty(Ty::option(Ty::slots(Ty::Int(IntTy::U64))), Span::new(1, 2),)
                .expect_err("option<slots<T>> has no conditional-owner semantics")
                .name,
            "type.affine_option_unsupported"
        );
    }

    #[test]
    fn class_payload_put_moves_the_source_and_take_produces_a_fresh_owner() {
        let mut program = monomorphized_program(
            r#"
class Item {
    u64 value;
    init new(u64 value) { self.value = value; }
}

fn subject() {
    mut slots<Item> cells = alloc_slots<Item>(1);
    var item = Item::new(7);
    slot_put(&mut cells, 0, item);
    var restored = slot_take(&mut cells, 0);
}
"#,
        );
        let checked = check(&mut program).expect("class payload slots have affine transitions");
        let owner = CallOwner::Function("subject".into());
        let put = checked
            .ownership
            .slot_transitions_for_owner(&owner)
            .find_map(|(_, transition)| match &transition.kind {
                CheckedSlotTransitionKind::Put { value_transfer, .. } => Some(value_transfer),
                CheckedSlotTransitionKind::Alloc { .. }
                | CheckedSlotTransitionKind::Take { .. } => None,
            })
            .expect("put transition");
        let put_transfer = checked
            .ownership
            .value_transfer(put)
            .expect("put transition links its transfer");
        assert_eq!(put_transfer.kind, ValueTransferKind::Move);
        assert_eq!(put_transfer.source, Some(Place::local("item")));
        assert_eq!(put_transfer.value_ty, Ty::Class(0));
        assert_eq!(put.sink, ValueTransferSink::SlotPut(Place::local("cells")));

        let take_span = checked
            .ownership
            .slot_transitions_for_owner(&owner)
            .find_map(|(key, transition)| {
                matches!(transition.kind, CheckedSlotTransitionKind::Take { .. })
                    .then_some(key.span)
            })
            .expect("take transition");
        let take_binding = ValueTransferKey {
            owner: owner.clone(),
            span: take_span,
            sink: ValueTransferSink::Binding("restored".into()),
        };
        let take_transfer = checked
            .ownership
            .value_transfer(&take_binding)
            .expect("the direct take binding has a transfer");
        assert_eq!(take_transfer.kind, ValueTransferKind::Fresh);
        assert_eq!(take_transfer.source, None);
        assert_eq!(take_transfer.value_ty, Ty::Class(0));

        let drop = checked
            .control
            .body(&owner, program.fns[0].span)
            .expect("subject control body")
            .plan()
            .candidate_for_place(&Place::local("cells"))
            .expect("slot owner has a drop candidate");
        assert!(matches!(
            drop.drop_action().recipe(),
            crate::control::ValueDropRecipe::ReleaseSlots {
                payload: Ty::Class(0),
                occupied: Some(occupied),
            } if matches!(occupied.recipe(), crate::control::ValueDropRecipe::DropClass(class) if class.class() == 0)
        ));

        let mut reuse = monomorphized_program(
            r#"
class Item {
    u64 value;
    init new(u64 value) { self.value = value; }
}
fn bad() {
    mut slots<Item> cells = alloc_slots<Item>(1);
    var item = Item::new(7);
    slot_put(&mut cells, 0, item);
    var duplicate = item;
}
"#,
        );
        assert_eq!(check_error(&mut reuse).name, "class.use_after_move");
    }

    #[test]
    fn branded_record_payload_cannot_escape_into_owner_slots() {
        let mut program = monomorphized_program(
            r#"
record Cell #[layout(size := 8, align := 8)] {
    #[offset(0)] u64 value;
}

fn bad(&mut [u8] bytes) {
    mut slots<Cell> cells = alloc_slots<Cell>(1);
    unsafe expose &mut bytes as (pointer, resource memory) {
        raw<Cell> typed = raw_cast<Cell>(pointer);
        mut resource PointsTo<Cell> cell = raw_into_cell<Cell>(typed, memory);
        raw_cell_init<Cell>(typed, Cell(7), &mut cell);
        Cell observed = raw_cell_read<Cell>(typed, &cell);
        slot_put(&mut cells, 0, observed);
    }
}
"#,
        );
        assert_eq!(check_error(&mut program).name, "expose.brand_escapes");
    }

    #[test]
    fn whole_slot_moves_change_loop_shape_but_loop_local_alloc_does_not_mutate_a_container() {
        let mut moved = monomorphized_program(
            r#"
fn bad() {
    mut slots<u64> cells = alloc_slots<u64>(1);
    mut u64 i = 0;
    /// invariant i <= 1
    /// variant 1 - i
    while (i < 1) {
        var taken_owner = cells;
        i = i + 1;
    }
}
"#,
        );
        assert_eq!(check_error(&mut moved).name, "slots.loop_shape");

        let mut allocated = monomorphized_program(
            r#"
fn ok() {
    mut u64 i = 0;
    /// invariant i <= 1
    /// variant 1 - i
    while (i < 1) {
        slots<u64> temporary = alloc_slots<u64>(1);
        i = i + 1;
    }
}
"#,
        );
        let checked = check(&mut allocated).expect("loop-local slot allocation is owner creation");
        let effects = checked
            .ownership
            .loops_for_owner(&CallOwner::Function("ok".into()))
            .next()
            .expect("loop effects")
            .1;
        assert!(
            effects
                .mutations
                .iter()
                .all(|mutation| !matches!(mutation, CheckedMutation::Slot { .. }))
        );
    }

    #[test]
    fn slot_control_handoff_refuses_missing_mismatched_and_respanned_records() {
        let source = r#"
fn subject() {
    mut slots<u64> cells = alloc_slots<u64>(1);
    slot_put(&mut cells, 0, 7);
}
"#;
        let mut missing_program = monomorphized_program(source);
        let mut missing = check(&mut missing_program).expect("baseline checks");
        let owner = CallOwner::Function("subject".into());
        let key = missing
            .ownership
            .slot_transitions_for_owner(&owner)
            .find(|(_, transition)| {
                matches!(transition.kind, CheckedSlotTransitionKind::Put { .. })
            })
            .map(|(key, _)| key.clone())
            .expect("put transition");
        missing.ownership.remove_slot_transition(&key);
        assert_eq!(
            reconcile_slot_control(&missing.control, &missing.ownership)
                .expect_err("a missing ownership transition must fail")
                .name,
            "internal.check.slot_control_transition_missing"
        );

        let mut mismatch_program = monomorphized_program(source);
        let mut mismatch = check(&mut mismatch_program).expect("baseline checks");
        let key = mismatch
            .ownership
            .slot_transitions_for_owner(&owner)
            .next()
            .map(|(key, _)| key.clone())
            .expect("slot transition");
        mismatch
            .ownership
            .slot_transition_mut(&key)
            .expect("mutable transition")
            .payload = Ty::Bool;
        assert_eq!(
            reconcile_slot_control(&mismatch.control, &mismatch.ownership)
                .expect_err("a mismatched ownership transition must fail")
                .name,
            "internal.check.slot_control_transition_mismatch"
        );
        let transition = mismatch
            .ownership
            .slot_transition_mut(&key)
            .expect("mutable transition");
        transition.payload = match &transition.result_ty {
            Ty::Slots(payload) => payload.as_ref().clone(),
            Ty::Int(_) => Ty::Int(IntTy::U64),
            Ty::Bool
            | Ty::Param(_)
            | Ty::Class(_)
            | Ty::Record(_)
            | Ty::Array(_)
            | Ty::Option(_)
            | Ty::OptionRaw(_)
            | Ty::Res(_)
            | Ty::Raw(_)
            | Ty::RawRecord(_)
            | Ty::Borrow(..)
            | Ty::Unit => Ty::Int(IntTy::U64),
        };
        transition.key.span = Span::new(key.span.start + 1, key.span.end + 1);
        assert_eq!(
            reconcile_slot_control(&mismatch.control, &mismatch.ownership)
                .expect_err("a mismatched embedded transition key must fail")
                .name,
            "internal.check.slot_control_transition_mismatch"
        );

        let checked_body = mismatch
            .control
            .body(&owner, mismatch_program.fns[0].span)
            .expect("retained subject body");
        let put = checked_body
            .plan()
            .slot_actions()
            .find(|action| matches!(action.kind(), SlotActionKind::Put { .. }))
            .expect("put action");
        let Stmt::ExprStmt(expression) = &mut mismatch_program.fns[0].body[1] else {
            panic!("expected put statement");
        };
        expression.span = Span::new(expression.span.start + 1, expression.span.end + 1);
        assert!(
            checked_body
                .plan()
                .slot_action(put.scope(), expression)
                .is_err()
        );
        assert!(
            checked_body
                .validate_callable(
                    mismatch_program.fns[0].span,
                    &mismatch_program.fns[0].params,
                    &mismatch_program.fns[0].body,
                )
                .is_err()
        );
    }
}
