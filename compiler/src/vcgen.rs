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

#![deny(clippy::wildcard_enum_match_arm)]

use crate::argument_schedule::ArgumentScheduleCertificate;
use crate::ast::*;
use crate::check::{CheckResult, FnSig};
use crate::control::{
    AssignmentAction, AssignmentStaging, BodyPlan, CompilerTempKind, ControlBody, ExitKind,
    ExitRoute, FieldAssignmentAction, ReturnRoutes, ScopeId, SlotAction, SlotActionKind,
    TemporaryDropAction, TrapSite, ValueDropRecipe,
};
use crate::ownership::{
    CheckedExposure, CheckedLoopEffects, CheckedMutation, CheckedOptionTake, CheckedOwnershipPlan,
    CheckedSealedArgument, CheckedSealedOperation, CheckedSealedTarget, CheckedSlotMutationKind,
    CheckedSlotTransition, CheckedSlotTransitionKind, EffectSiteKey, ValueTransfer,
    ValueTransferKey, ValueTransferKind, ValueTransferSink,
};
use crate::place::{BorrowedPlace, Place};
use crate::scan::Clause;
use crate::span::Span;
use crate::transition::{
    CallArgumentEffect, CallEffect, CallOwner, CallSiteKey, CallTarget, CheckedCallTransition,
    TransitionCertificate,
};
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
    /// Fixed-proof Lean certificates for selected symbolic transitions.
    /// They are not user obligations and cannot be skipped or discharged.
    pub(crate) transition_certificates: Vec<TransitionCertificate>,
    /// Closed, bounded argument-evaluation certificates. Like transition
    /// certificates, these cannot be skipped, assumed, or discharged.
    pub(crate) argument_schedule_certificates: Vec<ArgumentScheduleCertificate>,
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
        ty.res_kind() == Some(ResKind::Uart)
    }

    fn signature_uses_uart(function: &Fn) -> bool {
        is_uart_ty(function.ret.clone())
            || function
                .params
                .iter()
                .any(|param| is_uart_ty(param.ty.clone()))
    }

    fn visit_expr(expr: &Expr, uses_uart: &mut bool, used: &mut HashSet<String>) {
        *uses_uart |= expr.ty.clone().is_some_and(is_uart_ty);
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
            | ExprKind::SlotOp { args, .. }
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
            | ExprKind::ClassFieldIndex { index, .. } => visit_expr(index, uses_uart, used),
            ExprKind::AllocArray { len, init, .. } => {
                visit_expr(len, uses_uart, used);
                visit_expr(init, uses_uart, used);
            }
            ExprKind::IntLit(_)
            | ExprKind::BoolLit(_)
            | ExprKind::Var(_)
            | ExprKind::Len { .. }
            | ExprKind::OptTake { .. }
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
                    *uses_uart |= is_uart_ty(ty.clone());
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
        uses_uart |= class
            .fields
            .iter()
            .any(|field| is_uart_ty(field.ty.clone()));
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

// A type refusal raised where the caller has no error channel.
//
// Naming a Lean type and recovering an ADR 0009 integer model happen deep
// inside the symbolic executor, in `&self` helpers and in `-> Val` recursion
// that cannot return a `Result`. Two named gates already stand in front of
// them: the checker's payload gates refuse an unsupported shape at its source
// span, and `validate_vc_type_domain` refuses it again over the whole program
// before any symbolic execution starts. If a shape reaches these helpers
// regardless, the honest answer is neither a panic nor an invented Lean type:
// they latch a named internal error and return a placeholder, and `generate`
// fails on the latch before returning, so no placeholder is ever published.
thread_local! {
    static VC_TYPE_REFUSAL: std::cell::RefCell<Option<String>> =
        const { std::cell::RefCell::new(None) };
}

/// Record the first refusal; later ones are consequences of it.
fn refuse_vc_type(message: String) {
    VC_TYPE_REFUSAL.with(|latch| {
        let mut latch = latch.borrow_mut();
        if latch.is_none() {
            *latch = Some(message);
        }
    });
}

fn take_vc_type_refusal() -> Option<String> {
    VC_TYPE_REFUSAL.with(|latch| latch.borrow_mut().take())
}

/// The checker-authored root a sealed operation writes its fresh state back
/// under. No proof-state consumer decodes the borrow expression again.
fn sealed_borrow_root(operation: &CheckedSealedOperation, index: usize) -> String {
    let Some(argument) = operation.arguments.get(index) else {
        refuse_vc_type(format!(
            "internal.vcgen.sealed_borrow_shape: sealed `{}` has no checked argument {index}",
            operation.target.render()
        ));
        return format!("_refused_{}", operation.target.render());
    };
    let CallArgumentEffect::Loan(loan) = &argument.effect else {
        refuse_vc_type(format!(
            "internal.vcgen.sealed_borrow_shape: argument {index} of sealed `{}` is not a checked loan",
            operation.target.render()
        ));
        return format!("_refused_{}", operation.target.render());
    };
    if !loan.place.is_root() {
        refuse_vc_type(format!(
            "internal.vcgen.sealed_field_borrow: a borrow of the field `{}` reached \
             sealed `{op}`; the checker's `resource.field_borrow_op` gate refuses this \
             shape first",
            loan.place.render(),
            op = operation.target.render()
        ));
        return format!("_refused_{}", operation.target.render());
    }
    loan.place.root().to_string()
}

/// The Lean type name used where a payload has none. It does not exist in the
/// prelude, so it cannot elaborate even if the latch were somehow ignored.
const UNSUPPORTED_LEAN_TY: &str = "Sable.UnsupportedPayload";

/// The term used where a payload has no proof value, for the same reason.
const UNSUPPORTED_LEAN_VALUE: &str = "Sable.unsupportedValue";

/// Recover the abstract/concrete integer model used by the retained ADR 0009
/// proof domain. Boolean arrays have their own concrete proof model; options
/// likewise admit Bool. This is an allow-list so a POD record — or any shape
/// the recursive grammar can now spell — cannot silently be emitted as Lean
/// `Int`.
fn adr0009_int_model(ty: &Ty) -> IntTy {
    ty.int_model().unwrap_or_else(|| {
        refuse_vc_type(format!(
            "internal.vcgen.int_model_unsupported: `{}` has no ADR 0009 integer model",
            ty.name()
        ));
        IntTy::I64
    })
}

/// Integer-valued declaration/expression type in an ordinary instance or a
/// retained template. The latter uses `Ty::Param` rather than pretending that
/// an arbitrary type parameter is intrinsically an `IntTy`.
fn adr0009_ty_int_model(ty: Ty) -> IntTy {
    match ty {
        Ty::Int(IntTy::TParam(_)) => {
            refuse_vc_type(
                "internal.vcgen.int_model_unsupported: a non-canonical scalar type parameter \
                 reached VC generation"
                    .into(),
            );
            IntTy::I64
        }
        Ty::Int(integer) => integer,
        Ty::Param(parameter) => adr0009_int_model(&Ty::Param(parameter)),
        other @ (Ty::Bool
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
        | Ty::Unit) => {
            refuse_vc_type(format!(
                "internal.vcgen.int_model_unsupported: `{}` is not an integer or an ADR 0009 \
                 template parameter",
                other.name()
            ));
            IntTy::I64
        }
    }
}

/// The Lean type of an array with this payload. An allow-list: a payload the
/// proof language has no sequence element type for gets no name at all.
fn lean_array_ty(element: &Ty, records: &[RecordDecl]) -> String {
    match element {
        Ty::Bool => "Sable.Seq Bool".into(),
        Ty::Int(_) | Ty::Param(_) => {
            let _ = adr0009_int_model(element);
            "Sable.Seq Int".into()
        }
        // A record element's sequence is the record's own structure type.
        Ty::Record(ri) => format!("Sable.Seq {}", lean_record_name(&records[*ri].name)),
        Ty::Class(_)
        | Ty::Array(_)
        | Ty::Slots(_)
        | Ty::Option(_)
        | Ty::OptionRaw(_)
        | Ty::Res(_)
        | Ty::Raw(_)
        | Ty::RawRecord(_)
        | Ty::Borrow(..)
        | Ty::Unit => {
            refuse_vc_type(format!(
                "internal.vcgen.lean_type_unsupported: array payload `{}` has no Lean sequence \
                 element type",
                element.name()
            ));
            UNSUPPORTED_LEAN_TY.into()
        }
    }
}

/// Lean value type carried by one occupied owner-slot cell. This is a
/// separate allow-list from ordinary arrays and copyable source options:
/// `slots<T>` has move/occupancy semantics even when `T` itself is copyable.
fn lean_slot_payload_ty(payload: &Ty, classes: &[ClassDecl], records: &[RecordDecl]) -> String {
    match payload {
        Ty::Bool => "Bool".into(),
        Ty::Int(_) | Ty::Param(_) => {
            let _ = adr0009_int_model(payload);
            "Int".into()
        }
        Ty::Record(record) => lean_record_name(&records[*record].name),
        Ty::Class(class) => lean_class_name(&classes[*class].name),
        Ty::Array(_)
        | Ty::Slots(_)
        | Ty::Option(_)
        | Ty::OptionRaw(_)
        | Ty::Res(_)
        | Ty::Raw(_)
        | Ty::RawRecord(_)
        | Ty::Borrow(..)
        | Ty::Unit => {
            refuse_vc_type(format!(
                "internal.vcgen.slot_payload_unsupported: `{}` has no occupied-slot Lean value type",
                payload.name()
            ));
            UNSUPPORTED_LEAN_TY.into()
        }
    }
}

/// Proof state for `slots<T>` is an occupancy sequence, never an ordinary
/// `Seq T`: an empty cell is `none`, and a present payload is `some value`.
fn lean_slots_ty(payload: &Ty, classes: &[ClassDecl], records: &[RecordDecl]) -> String {
    format!(
        "Sable.Seq (Option {})",
        lean_slot_payload_ty(payload, classes, records)
    )
}

/// The Lean type of an option with this payload. An allow-list, for the same
/// reason `lean_array_ty` is: a payload needs a Lean type whose proof rules
/// were written for it, whether or not it owns.
///
/// The owned array payload is spelled with its parentheses because the result
/// is one argument: `Option (Sable.Seq Bool)`, never `Option Sable.Seq Bool`.
fn lean_option_ty(element: &Ty, classes: &[ClassDecl]) -> String {
    match element {
        Ty::Bool => "Option Bool".into(),
        Ty::Int(_) | Ty::Param(_) => {
            let _ = adr0009_int_model(element);
            "Option Int".into()
        }
        // A nested payload's Lean type is the payload's own option type,
        // parenthesized because the result is one argument.
        Ty::Option(inner) => format!("Option ({})", lean_option_ty(inner, classes)),
        // The owning class payload: the present case is the class's own
        // structure value.
        Ty::Class(ci) => format!("Option {}", lean_class_name(&classes[*ci].name)),
        owned @ Ty::Array(_) if owned.is_owned_array_of(&Ty::Bool) => {
            "Option (Sable.Seq Bool)".into()
        }
        Ty::Record(_)
        | Ty::Array(_)
        | Ty::Slots(_)
        | Ty::OptionRaw(_)
        | Ty::Res(_)
        | Ty::Raw(_)
        | Ty::RawRecord(_)
        | Ty::Borrow(..)
        | Ty::Unit => {
            refuse_vc_type(format!(
                "internal.vcgen.lean_type_unsupported: option payload `{}` has no Lean type",
                element.name()
            ));
            UNSUPPORTED_LEAN_TY.into()
        }
    }
}

/// The symbolic evaluator carries source booleans as propositions. Whenever
/// one crosses back into a source `Bool` position, use an explicit local
/// decidability witness and parenthesize the complete application so it stays
/// one argument inside constructors, structure updates, and substitutions.
fn lean_bool_value(prop: &str) -> String {
    format!("(@decide ({prop}) (Classical.propDecidable ({prop})))")
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum VcAggregateKind {
    Array,
    Slots,
    Option,
}

impl VcAggregateKind {
    /// The container word for a refusal, so a payload refusal says which
    /// container asked. The proof language gives an array payload and an
    /// option payload separate Lean types (`lean_array_ty`, `lean_option_ty`),
    /// so the two positions are separate questions even where they agree.
    fn container(self) -> &'static str {
        match self {
            VcAggregateKind::Array => "array",
            VcAggregateKind::Slots => "owner-slot",
            VcAggregateKind::Option => "option",
        }
    }
}

/// May a container payload cross into VC generation.
///
/// This is a gate, not a traversal: it answers from the payload family the
/// classification recognizes, and it deliberately does not call
/// `validate_vc_ty`. Option nesting is the family's own recursion
/// (`Option (Option Int)` has proof rules per level); an array element
/// stays a flat value.
pub(crate) fn validate_vc_payload_ty(
    ty: &Ty,
    allow_param: bool,
    aggregate: VcAggregateKind,
    context: &str,
) -> Result<(), String> {
    let container = aggregate.container();
    if aggregate == VcAggregateKind::Slots {
        return match ty {
            Ty::Int(IntTy::TParam(_)) => Err(format!(
                "internal.vcgen.type_error: non-canonical legacy parameter in {container} payload in {context}"
            )),
            Ty::Int(_) | Ty::Bool | Ty::Record(_) | Ty::Class(_) => Ok(()),
            Ty::Param(_) if allow_param => Ok(()),
            Ty::Param(_) => Err(format!(
                "internal.vcgen.type_error: type parameter escaped monomorphization in {container} payload in {context}"
            )),
            Ty::Array(_)
            | Ty::Slots(_)
            | Ty::Option(_)
            | Ty::OptionRaw(_)
            | Ty::Res(_)
            | Ty::Raw(_)
            | Ty::RawRecord(_)
            | Ty::Borrow(..)
            | Ty::Unit => Err(format!(
                "internal.vcgen.slot_payload_unsupported: {container} payload `{}` has no proof semantics in {context}",
                ty.name()
            )),
        };
    }
    match ty.payload_family() {
        PayloadFamily::Noncanonical => Err(format!(
            "internal.vcgen.type_error: non-canonical legacy parameter in {container} payload in {context}"
        )),
        PayloadFamily::Value => Ok(()),
        // The recursive family nests in options (`Option (Option Int)` is
        // a Lean type whose proof rules compose per level) and stays out
        // of arrays (no per-element option storage).
        PayloadFamily::OptionOfValue if aggregate == VcAggregateKind::Option => Ok(()),
        PayloadFamily::OptionOfValue => Err(format!(
            "internal.vcgen.type_error: {container} payload `{}` has no proof semantics in {context}",
            ty.name()
        )),
        PayloadFamily::Param if allow_param => Ok(()),
        PayloadFamily::Param => Err(format!(
            "internal.vcgen.type_error: type parameter escaped monomorphization in {container} payload in {context}"
        )),
        // A record element has proof semantics (`Sable.Seq SableR_X` with
        // elementwise well-formedness); a record option payload does not.
        PayloadFamily::Record if aggregate == VcAggregateKind::Array => Ok(()),
        PayloadFamily::Record => Err(format!(
            "internal.vcgen.type_error: POD-record {container} payload reached {context} before record proof semantics"
        )),
        PayloadFamily::Unsupported => Err(format!(
            "internal.vcgen.type_error: {container} payload `{}` has no proof semantics in {context}",
            ty.name()
        )),
    }
}

pub(crate) fn validate_vc_ty(ty: Ty, allow_param: bool, context: &str) -> Result<(), String> {
    // An option whose present case owns has its own proof rules, so it is
    // answered here rather than by the copyable-option payload gate below —
    // which would report the copyable family's refusal for a shape that
    // family never handles.
    if let Some(payload) = ty.as_affine_option_payload() {
        if payload.is_owned_array_of(&Ty::Bool) || matches!(payload, Ty::Class(_)) {
            return Ok(());
        }
        return Err(format!(
            "vc.affine_option_payload: `{}` has no affine-option proof semantics in {context}; `option<[bool]>` and `option<class>` are admitted",
            ty.name()
        ));
    }
    // A borrow carries no payload of its own, so what is gated is the
    // referent's: the proof model of `&[T]` is the proof model of `[T]`.
    validate_vc_container_payloads(ty.referent().clone(), allow_param, context)
}

/// The payload rules for one type's own containers, exhaustive with no
/// wildcard so a new constructor is a compile error rather than a shape the
/// proof preflight never looked at.
fn validate_vc_container_payloads(ty: Ty, allow_param: bool, context: &str) -> Result<(), String> {
    match ty {
        Ty::Slots(element) => {
            validate_vc_payload_ty(&element, allow_param, VcAggregateKind::Slots, context)
        }
        Ty::Param(_) if !allow_param => Err(format!(
            "internal.vcgen.type_error: type parameter escaped monomorphization in {context}"
        )),
        Ty::Int(IntTy::TParam(_)) => Err(format!(
            "internal.vcgen.type_error: non-canonical legacy scalar parameter in {context}"
        )),
        Ty::Array(element) => {
            validate_vc_payload_ty(&element, allow_param, VcAggregateKind::Array, context)
        }
        Ty::Option(element) => {
            validate_vc_payload_ty(&element, allow_param, VcAggregateKind::Option, context)
        }
        Ty::Int(_)
        | Ty::Bool
        | Ty::Param(_)
        | Ty::Class(_)
        | Ty::Record(_)
        | Ty::OptionRaw(_)
        | Ty::Res(_)
        | Ty::Raw(_)
        | Ty::RawRecord(_)
        | Ty::Borrow(..)
        | Ty::Unit => Ok(()),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum VcTypePosition {
    Expression,
    Local,
    Parameter,
    TraitParameter,
    Return,
    TraitReturn,
    ClassField,
    RecordField,
    Borrow,
}

pub(crate) fn validate_vc_type_position(
    ty: Ty,
    allow_param: bool,
    position: VcTypePosition,
    context: &str,
) -> Result<(), String> {
    // Validate the payload first. This keeps the unsupported POD-record model
    // (and an escaped ordinary-function type parameter) an independent
    // fail-closed boundary even if the surrounding aggregate is also in a
    // position that the checked language currently forbids.
    validate_vc_ty(ty.clone(), allow_param, context)?;

    // A borrow is an argument form and a parameter binding mode, not a local
    // binding (ADR 0072). The symbolic environment is keyed by source name and
    // every entry is assumed to be the only name for its storage; a borrow
    // local would be a second one, and the two entries would diverge at the
    // first store. `check::local_ty` refuses this at the source span — this is
    // the same rule at the VC boundary, which has no honest answer for the
    // shape either.
    if matches!(ty, Ty::Borrow(..)) && position == VcTypePosition::Local {
        return Err(format!(
            "internal.vcgen.type_error: a borrow is a parameter binding mode, not a local \
             binding, in {context}"
        ));
    }

    // Owner slots stay local/class-field storage. Their unique borrow exists
    // only as the first argument of a sealed slot operation and is validated
    // again by that operation's exact checker/control handoff.
    if matches!(ty.referent(), Ty::Slots(_)) {
        let admitted = match &ty {
            Ty::Slots(_) => match position {
                VcTypePosition::Expression | VcTypePosition::Local | VcTypePosition::ClassField => {
                    true
                }
                VcTypePosition::Parameter
                | VcTypePosition::TraitParameter
                | VcTypePosition::Return
                | VcTypePosition::TraitReturn
                | VcTypePosition::RecordField
                | VcTypePosition::Borrow => false,
            },
            Ty::Borrow(Mutability::Mut, referent) if matches!(referent.as_ref(), Ty::Slots(_)) => {
                match position {
                    VcTypePosition::Borrow => true,
                    VcTypePosition::Expression
                    | VcTypePosition::Local
                    | VcTypePosition::Parameter
                    | VcTypePosition::TraitParameter
                    | VcTypePosition::Return
                    | VcTypePosition::TraitReturn
                    | VcTypePosition::ClassField
                    | VcTypePosition::RecordField => false,
                }
            }
            Ty::Int(_)
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
            | Ty::Borrow(..)
            | Ty::Unit => false,
        };
        if admitted {
            return Ok(());
        }
        return Err(format!(
            "vc.slots_position: `{}` is owner-slot local/class-field storage and is not supported in this position in {context}",
            ty.name()
        ));
    }

    if ty.is_affine_option() {
        let position = match position {
            VcTypePosition::Expression | VcTypePosition::Local => return Ok(()),
            VcTypePosition::Parameter => "a function parameter",
            VcTypePosition::TraitParameter => "a trait parameter",
            VcTypePosition::Return => "a function return",
            VcTypePosition::TraitReturn => "a trait return",
            VcTypePosition::ClassField => "a class field",
            VcTypePosition::RecordField => "a record field",
            VcTypePosition::Borrow => "a borrow",
        };
        return Err(format!(
            "vc.affine_option_position: `option<[bool]>` is owned-local only; {position} is not supported in {context}"
        ));
    }

    // Only the *owned* Boolean array is position-restricted. A borrowed one
    // is a second name for a sequence its caller owns, and its proof model is
    // read off the element type exactly as `&[T]`'s is — one `Sable.Seq Bool`
    // binder, a length fact, and no element fact, because `Bool` is already
    // its complete value domain. So it goes wherever a borrowed array goes,
    // and the positions a borrow may be *written* in stay the parser's row
    // and `check::borrow_referent_ty`'s to state.
    if ty.is_owned_array_of(&Ty::Bool) {
        let position = match position {
            // Both halves of a call join the positions an owned Boolean array
            // occupies: the transfer is payload-blind (ADR 0085), and the
            // proof state a transferred sequence carries is
            // `lean_array_ty`'s, which reads the element type exactly as
            // every other array site does.
            VcTypePosition::Expression
            | VcTypePosition::Local
            | VcTypePosition::ClassField
            | VcTypePosition::Parameter
            | VcTypePosition::Return => {
                return Ok(());
            }
            VcTypePosition::TraitParameter => "a trait parameter",
            VcTypePosition::TraitReturn => "a trait return",
            VcTypePosition::RecordField => "a record field",
            VcTypePosition::Borrow => "a borrow",
        };
        return Err(format!(
            "internal.vcgen.type_error: an owned Boolean array is a local value or a class \
             field; {position} is not supported in {context}"
        ));
    }

    if let Ty::Option(element) = ty {
        // A parameter binds `Option Int` / `Option Bool` exactly as a local
        // or a returned value does, so the concrete value payloads pass. The
        // type-parameter payload does not: check refuses it first
        // (`type.option_param`), and this gate stays closed independently.
        // A parameter transports the recursive family (any nesting depth);
        // a class field stores flat value payloads only — the two
        // conditions are stated apart so the positions cannot drift
        // together by accident.
        let value_payload = element.payload_family() == PayloadFamily::Value;
        let transportable_payload = matches!(
            element.payload_family(),
            PayloadFamily::Value | PayloadFamily::OptionOfValue
        );
        let position = match position {
            VcTypePosition::Expression | VcTypePosition::Local | VcTypePosition::Return => {
                return Ok(());
            }
            VcTypePosition::Parameter if transportable_payload => return Ok(()),
            VcTypePosition::Parameter => "non-value-payload option parameters",
            VcTypePosition::TraitParameter => "trait option parameters",
            VcTypePosition::TraitReturn => "trait option returns",
            // A class field stores `Option Int` / `Option Bool` exactly as
            // a parameter binds it; the abstract and nested payloads stay
            // out here, independently of check's `type.option_field`.
            VcTypePosition::ClassField if value_payload => return Ok(()),
            VcTypePosition::ClassField => "non-value-payload option class fields",
            VcTypePosition::RecordField => "option-valued record fields",
            VcTypePosition::Borrow => "option borrows",
        };
        return Err(format!(
            "internal.vcgen.type_error: {position} are not supported in {context}"
        ));
    }
    Ok(())
}

fn is_bool_array(ty: Ty) -> bool {
    ty.is_array_of(&Ty::Bool)
}

/// An *owned* Boolean array — the local value that carries its own
/// allocation, literal, and rebinding rules. `&[bool]` and `&mut [bool]` are
/// deliberately not owned Boolean arrays: they name a sequence their caller
/// owns and transport exactly as `&[T]` does, so the rules that keep an owner
/// in one place have nothing to say about them.
fn is_owned_bool_array(ty: Ty) -> bool {
    ty.is_owned_array_of(&Ty::Bool)
}

fn is_affine_bool_option(ty: Ty) -> bool {
    ty.is_affine_option()
}

fn expr_is_owned_bool_array(expr: &Expr, locals: &HashMap<String, Ty>) -> bool {
    expr.ty.clone().is_some_and(is_owned_bool_array)
        || matches!(
            &expr.kind,
            ExprKind::Var(name)
                if locals.get(name).as_ref().is_some_and(|ty| ty.is_owned_array_of(&Ty::Bool))
        )
}

fn expr_is_affine_option(expr: &Expr, locals: &HashMap<String, Ty>) -> bool {
    expr.ty.clone().is_some_and(is_affine_bool_option)
        || matches!(
            &expr.kind,
            ExprKind::Var(name) if locals.get(name).is_some_and(|ty| is_affine_bool_option(ty.clone()))
        )
}

/// Where an owned Boolean array comes from. A literal and an allocation build
/// one; a call hands one over, its owner having left the callee's frame at the
/// return (ADR 0085). What is *not* here is a second name for storage someone
/// else still holds, which is the whole point of enumerating producers.
fn is_fresh_bool_array_value(expr: &Expr) -> bool {
    expr.ty == Some(Ty::array(Ty::Bool))
        && matches!(
            expr.kind,
            ExprKind::ArrayLit(_) | ExprKind::AllocArray { .. } | ExprKind::Call { .. }
        )
}

fn is_affine_option_take(expr: &Expr) -> bool {
    matches!(expr.kind, ExprKind::OptTake { .. })
        && expr
            .ty
            .as_ref()
            .is_some_and(|ty| ty.is_owned_array_of(&Ty::Bool) || matches!(ty, Ty::Class(_)))
}

fn reject_owned_bool_array_value(
    expr: &Expr,
    locals: &HashMap<String, Ty>,
    boundary: &str,
    context: &str,
) -> Result<(), String> {
    if expr_is_owned_bool_array(expr, locals) {
        return Err(format!(
            "internal.vcgen.type_error: an owned Boolean array cannot cross {boundary} in {context}"
        ));
    }
    Ok(())
}

fn reject_affine_option_value(
    expr: &Expr,
    locals: &HashMap<String, Ty>,
    boundary: &str,
    context: &str,
) -> Result<(), String> {
    if expr_is_affine_option(expr, locals) {
        return Err(format!(
            "vc.affine_option_boundary: affine options cannot cross {boundary} in {context}"
        ));
    }
    Ok(())
}

fn reject_affine_option_named_source(
    name: &str,
    locals: &HashMap<String, Ty>,
    boundary: &str,
    context: &str,
) -> Result<(), String> {
    if locals.get(name).is_some_and(Ty::is_affine_option) {
        return Err(format!(
            "vc.affine_option_boundary: affine-option local `{name}` cannot be used as {boundary} in {context}"
        ));
    }
    Ok(())
}

fn require_fresh_vc_bindings(
    names: &[&str],
    locals: &HashMap<String, Ty>,
    context: &str,
) -> Result<(), String> {
    let mut fresh = HashSet::new();
    for name in names {
        if locals.contains_key(*name) || !fresh.insert(*name) {
            return Err(format!(
                "vc.duplicate_local: generated binding `{name}` would replace an active or sibling local in {context}"
            ));
        }
    }
    Ok(())
}

/// The checked type an expression contributes to a scalar/option operator.
/// A local name is resolved from the source environment as well as its cached
/// annotation: otherwise a forged AST could relabel an owned Boolean array as
/// `bool`/`u64` and drive the symbolic evaluator into the wrong `Val` arm.
fn vc_semantic_expr_ty(
    expr: &Expr,
    locals: &HashMap<String, Ty>,
    context: &str,
) -> Result<Ty, String> {
    if let ExprKind::Var(name) = &expr.kind {
        if let Some(local_ty) = locals.get(name).cloned() {
            // Checked affine resource variables intentionally may lack a
            // cached expression type: their sealed operand position is the
            // typing authority.  Preserve that phase invariant while still
            // requiring exact cache/local agreement for runtime values.
            if expr.ty != Some(local_ty.clone())
                && !(local_ty.clone().is_resource() && expr.ty.is_none())
            {
                return Err(format!(
                    "internal.vcgen.type_error: `{name}` has an inconsistent cached type in {context}"
                ));
            }
            return Ok(local_ty);
        }
    }
    expr.ty.clone().ok_or_else(|| {
        format!("internal.vcgen.type_error: expression lacks its checked type in {context}")
    })
}

fn require_vc_expr_ty(
    expr: &Expr,
    expected: Ty,
    locals: &HashMap<String, Ty>,
    role: &str,
    context: &str,
) -> Result<(), String> {
    let actual = vc_semantic_expr_ty(expr, locals, context)?;
    if actual != expected {
        return Err(format!(
            "internal.vcgen.type_error: {role} has type `{}`, expected `{}` in {context}",
            actual.name(),
            expected.name()
        ));
    }
    Ok(())
}

fn vc_integer_ty(ty: Ty, allow_param: bool) -> bool {
    matches!(ty, Ty::Int(integer) if !matches!(integer, IntTy::TParam(_)))
        || allow_param && matches!(ty, Ty::Param(_))
}

fn validate_vc_scalar_operator(
    expr: &Expr,
    allow_param: bool,
    context: &str,
    locals: &HashMap<String, Ty>,
) -> Result<(), String> {
    let result = vc_semantic_expr_ty(expr, locals, context)?;
    match &expr.kind {
        ExprKind::Widen { target, arg } => {
            let source = vc_semantic_expr_ty(arg, locals, context)?;
            let (Ty::Int(source), Ty::Int(result_integer)) = (source, result) else {
                return Err(format!(
                    "internal.vcgen.type_error: `widen` requires concrete integer operands and result in {context}"
                ));
            };
            if matches!(source, IntTy::TParam(_))
                || matches!(target, IntTy::TParam(_))
                || result_integer != *target
                || source.min() < target.min()
                || source.max() > target.max()
            {
                return Err(format!(
                    "internal.vcgen.type_error: inconsistent `widen` operand/result types in {context}"
                ));
            }
        }
        ExprKind::Narrow { target, arg } => {
            let source = vc_semantic_expr_ty(arg, locals, context)?;
            if !vc_integer_ty(source, allow_param)
                || matches!(target, IntTy::TParam(_))
                || result != Ty::Int(*target)
            {
                return Err(format!(
                    "internal.vcgen.type_error: inconsistent `narrow` operand/result types in {context}"
                ));
            }
        }
        ExprKind::Unary { op, operand } => {
            let operand = vc_semantic_expr_ty(operand, locals, context)?;
            let coherent = match op {
                UnOp::Neg => {
                    matches!(operand, Ty::Int(integer) if integer.signed()) && result == operand
                }
                UnOp::Not => operand == Ty::Bool && result == Ty::Bool,
            };
            if !coherent {
                return Err(format!(
                    "internal.vcgen.type_error: inconsistent unary operand/result types in {context}"
                ));
            }
        }
        ExprKind::Binary { op, lhs, rhs, .. } => {
            let lhs = vc_semantic_expr_ty(lhs, locals, context)?;
            let rhs = vc_semantic_expr_ty(rhs, locals, context)?;
            let same_integer = lhs == rhs && vc_integer_ty(lhs.clone(), allow_param);
            let coherent = if op.is_arith() {
                same_integer
                    && result == lhs
                    && (!matches!(op, BinOp::Div | BinOp::Rem) || !matches!(lhs, Ty::Param(_)))
            } else if op.is_comparison() {
                same_integer && result == Ty::Bool
            } else {
                lhs == Ty::Bool && rhs == Ty::Bool && result == Ty::Bool
            };
            if !coherent {
                return Err(format!(
                    "internal.vcgen.type_error: inconsistent binary operand/result types in {context}"
                ));
            }
        }
        ExprKind::IntLit(_)
        | ExprKind::BoolLit(_)
        | ExprKind::Var(_)
        | ExprKind::Call { .. }
        | ExprKind::Index { .. }
        | ExprKind::Len { .. }
        | ExprKind::RawOp { .. }
        | ExprKind::DeviceOp { .. }
        | ExprKind::ResOp { .. }
        | ExprKind::SlotOp { .. }
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
        | ExprKind::RecordLit { .. } => {
            unreachable!("scalar-operator validation called for a different expression")
        }
    }
    Ok(())
}

fn validate_vc_option_operator(
    expr: &Expr,
    context: &str,
    locals: &HashMap<String, Ty>,
) -> Result<(), String> {
    let result = vc_semantic_expr_ty(expr, locals, context)?;
    match &expr.kind {
        ExprKind::IsSome { operand } => {
            let operand = vc_semantic_expr_ty(operand, locals, context)?;
            if !matches!(operand, Ty::Option(_) | Ty::OptionRaw(_)) || result != Ty::Bool {
                return Err(format!(
                    "internal.vcgen.type_error: inconsistent `.is_some` operand/result types in {context}"
                ));
            }
        }
        ExprKind::OptValue { operand } => {
            let operand = vc_semantic_expr_ty(operand, locals, context)?;
            let expected = match operand {
                Ty::Option(payload) => *payload,
                Ty::OptionRaw(record) => Ty::RawRecord(record),
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
                | Ty::Unit => {
                    return Err(format!(
                        "internal.vcgen.type_error: `.value` requires an option operand in {context}"
                    ));
                }
            };
            if result != expected {
                return Err(format!(
                    "internal.vcgen.type_error: inconsistent `.value` payload type in {context}"
                ));
            }
        }
        ExprKind::SomeE(inner) => {
            let expected = match result {
                Ty::Option(ref payload) => payload.clone(),
                Ty::OptionRaw(record) => Box::new(Ty::RawRecord(record)),
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
                | Ty::Unit => {
                    return Err(format!(
                        "internal.vcgen.type_error: `some` requires an option result in {context}"
                    ));
                }
            };
            if vc_semantic_expr_ty(inner, locals, context)? != *expected {
                return Err(format!(
                    "internal.vcgen.type_error: inconsistent `some` payload type in {context}"
                ));
            }
            if result.is_affine_option() {
                let class_payload = matches!(expected.as_ref(), Ty::Class(_));
                let admitted = if class_payload {
                    // A class payload wraps a fresh construction or a
                    // named owner the wrap consumes.
                    matches!(inner.kind, ExprKind::CtorCall { .. } | ExprKind::Var(_))
                } else {
                    matches!(inner.kind, ExprKind::AllocArray { elem: Ty::Bool, .. })
                };
                if !admitted {
                    return Err(format!(
                        "vc.affine_option_initializer: `some` for an owning option must \
                         directly wrap a fresh allocation, a fresh construction, or a named \
                         owner in {context}"
                    ));
                }
            }
        }
        ExprKind::NoneE => {
            if !matches!(result, Ty::Option(_) | Ty::OptionRaw(_)) {
                return Err(format!(
                    "internal.vcgen.type_error: `none` requires an option result in {context}"
                ));
            }
        }
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
            unreachable!("option-operator validation called for a different expression")
        }
    }
    Ok(())
}

fn validate_vc_slot_operation(
    expression: &Expr,
    allow_param: bool,
    context: &str,
    locals: &HashMap<String, Ty>,
) -> Result<(), String> {
    let ExprKind::SlotOp { op, args, .. } = &expression.kind else {
        unreachable!("slot validator is called only for slot operations")
    };
    if args.len() != op.arity() {
        return Err(format!(
            "internal.vcgen.slot_transition_shape: `{}` has {} argument(s), expected {} in {context}",
            op.name(),
            args.len(),
            op.arity()
        ));
    }
    match op {
        SlotOp::Alloc { elem } => {
            validate_vc_payload_ty(elem, allow_param, VcAggregateKind::Slots, context)?;
            validate_vc_expr(&args[0], allow_param, context, locals)?;
            require_vc_expr_ty(
                &args[0],
                Ty::Int(IntTy::U64),
                locals,
                "slot-allocation length",
                context,
            )?;
            if expression.ty != Some(Ty::slots(elem.clone())) {
                return Err(format!(
                    "internal.vcgen.slot_transition_shape: `alloc_slots` result disagrees with its payload in {context}"
                ));
            }
        }
        SlotOp::Take | SlotOp::Put => {
            validate_vc_expr(&args[0], allow_param, context, locals)?;
            let container_ty = vc_semantic_expr_ty(&args[0], locals, context)?;
            let Ty::Borrow(Mutability::Mut, referent) = container_ty else {
                return Err(format!(
                    "internal.vcgen.slot_transition_shape: `{}` container is not a unique borrow in {context}",
                    op.name()
                ));
            };
            let Ty::Slots(payload) = referent.as_ref() else {
                return Err(format!(
                    "internal.vcgen.slot_transition_shape: `{}` container does not refer to owner slots in {context}",
                    op.name()
                ));
            };
            validate_vc_payload_ty(payload, allow_param, VcAggregateKind::Slots, context)?;
            validate_vc_expr(&args[1], allow_param, context, locals)?;
            require_vc_expr_ty(&args[1], Ty::Int(IntTy::U64), locals, "slot index", context)?;
            match op {
                SlotOp::Take if expression.ty.as_ref() == Some(payload.as_ref()) => {}
                SlotOp::Put => {
                    validate_vc_expr(&args[2], allow_param, context, locals)?;
                    require_vc_expr_ty(
                        &args[2],
                        payload.as_ref().clone(),
                        locals,
                        "slot-put value",
                        context,
                    )?;
                    if expression.ty != Some(Ty::Unit) {
                        return Err(format!(
                            "internal.vcgen.slot_transition_shape: `slot_put` result is not unit in {context}"
                        ));
                    }
                }
                SlotOp::Take => {
                    return Err(format!(
                        "internal.vcgen.slot_transition_shape: `slot_take` result disagrees with its payload in {context}"
                    ));
                }
                SlotOp::Alloc { .. } => unreachable!(),
            }
        }
    }
    Ok(())
}

fn validate_vc_expr(
    expr: &Expr,
    allow_param: bool,
    context: &str,
    locals: &HashMap<String, Ty>,
) -> Result<(), String> {
    if let Some(ty) = &expr.ty {
        let position = if matches!(expr.kind, ExprKind::Borrow { .. }) {
            VcTypePosition::Borrow
        } else {
            VcTypePosition::Expression
        };
        validate_vc_type_position(ty.clone(), allow_param, position, context)?;
        // The producers of an *owned* Boolean array are enumerated because an
        // owner has to come from somewhere the ownership rules know about. A
        // borrowed one is not produced at all — it names storage that already
        // exists — so it is no more restricted here than `&[T]` is.
        if is_owned_bool_array(ty.clone()) {
            match &expr.kind {
                ExprKind::Var(name) if locals.get(name) == Some(ty) => {}
                // A call joins the list for the reason the list exists: a
                // verified callee hands its owner over (ADR 0085), so the
                // result is storage the ownership rules already accounted for.
                ExprKind::ArrayLit(_) | ExprKind::AllocArray { .. } | ExprKind::Call { .. } => {}
                ExprKind::Var(_) => {
                    return Err(format!(
                        "internal.vcgen.type_error: Boolean array variable has an inconsistent source type in {context}"
                    ));
                }
                ExprKind::IntLit(_)
                | ExprKind::BoolLit(_)
                | ExprKind::Unary { .. }
                | ExprKind::Binary { .. }
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
                    return Err(format!(
                        "internal.vcgen.type_error: Boolean array value has an unsupported producer in {context}"
                    ));
                }
            }
        }
    }
    match &expr.kind {
        ExprKind::SlotOp { .. } => validate_vc_slot_operation(expr, allow_param, context, locals),
        ExprKind::Unary { operand, .. }
        | ExprKind::Widen { arg: operand, .. }
        | ExprKind::Narrow { arg: operand, .. } => {
            validate_vc_expr(operand, allow_param, context, locals)?;
            validate_vc_scalar_operator(expr, allow_param, context, locals)
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            validate_vc_expr(lhs, allow_param, context, locals)?;
            validate_vc_expr(rhs, allow_param, context, locals)?;
            validate_vc_scalar_operator(expr, allow_param, context, locals)
        }
        ExprKind::IsSome { operand } => {
            let operand_ty = vc_semantic_expr_ty(operand, locals, context)?;
            if operand_ty.is_affine_option() {
                validate_vc_ty(operand_ty, allow_param, context)?;
                let ExprKind::Var(option) = &operand.kind else {
                    return Err(format!(
                        "vc.affine_option_temporary: `.is_some` requires a named affine-option local in {context}"
                    ));
                };
                if !locals.get(option).is_some_and(Ty::is_affine_option) {
                    return Err(format!(
                        "internal.vcgen.type_error: `.is_some` affine-option place is not an active local in {context}"
                    ));
                }
                validate_vc_option_operator(expr, context, locals)
            } else {
                validate_vc_expr(operand, allow_param, context, locals)?;
                validate_vc_option_operator(expr, context, locals)
            }
        }
        ExprKind::OptValue { operand } => {
            validate_vc_expr(operand, allow_param, context, locals)?;
            validate_vc_option_operator(expr, context, locals)
        }
        ExprKind::SomeE(operand) => {
            if expr.ty.as_ref().is_some_and(Ty::is_affine_option) {
                validate_vc_option_operator(expr, context, locals)?;
                validate_vc_expr(operand, allow_param, context, locals)
            } else {
                validate_vc_expr(operand, allow_param, context, locals)?;
                validate_vc_option_operator(expr, context, locals)
            }
        }
        // An ordinary call is where an owner may be handed over (ADR 0085);
        // the member, record-literal, and trait boundaries keep their
        // refusal, each closed in the checker by its own name.
        ExprKind::Call { args, .. } => {
            for arg in args {
                reject_affine_option_value(arg, locals, "a call boundary", context)?;
                validate_vc_expr(arg, allow_param, context, locals)?;
            }
            Ok(())
        }
        ExprKind::CtorCall { args, .. }
        | ExprKind::RecordLit { args, .. }
        | ExprKind::TraitCall { args, .. } => {
            for arg in args {
                reject_owned_bool_array_value(arg, locals, "a call boundary", context)?;
                reject_affine_option_value(arg, locals, "a call boundary", context)?;
                validate_vc_expr(arg, allow_param, context, locals)?;
            }
            Ok(())
        }
        ExprKind::MethodCall { recv, args, .. } => {
            reject_affine_option_named_source(recv, locals, "a method receiver", context)?;
            if locals
                .get(recv)
                .as_ref()
                .is_some_and(|ty| ty.is_array_of(&Ty::Bool))
            {
                return Err(format!(
                    "internal.vcgen.type_error: Boolean arrays cannot be method receivers in {context}"
                ));
            }
            for arg in args {
                reject_owned_bool_array_value(arg, locals, "a call boundary", context)?;
                reject_affine_option_value(arg, locals, "a call boundary", context)?;
                validate_vc_expr(arg, allow_param, context, locals)?;
            }
            Ok(())
        }
        ExprKind::RawOp { args, .. }
        | ExprKind::DeviceOp { args, .. }
        | ExprKind::ResOp { args, .. } => {
            for arg in args {
                reject_owned_bool_array_value(arg, locals, "an intrinsic boundary", context)?;
                reject_affine_option_value(arg, locals, "an intrinsic boundary", context)?;
                validate_vc_expr(arg, allow_param, context, locals)?;
            }
            Ok(())
        }
        ExprKind::ArrayLit(elements) => {
            let Some(Ty::Array(ref element)) = expr.ty else {
                return Err(format!(
                    "internal.vcgen.type_error: array literal lacks an owned array type in {context}"
                ));
            };
            validate_vc_payload_ty(element, allow_param, VcAggregateKind::Array, context)?;
            for element_expr in elements {
                validate_vc_expr(element_expr, allow_param, context, locals)?;
                require_vc_expr_ty(
                    element_expr,
                    element.as_ref().clone(),
                    locals,
                    "array-literal element",
                    context,
                )?;
            }
            Ok(())
        }
        ExprKind::Index { array, index, .. } => {
            validate_vc_expr(index, allow_param, context, locals)?;
            require_vc_expr_ty(index, Ty::Int(IntTy::U64), locals, "array index", context)?;
            let Some(element) = locals
                .get(array)
                .and_then(|ty| ty.as_array().map(|(element, _)| element.clone()))
            else {
                return Err(format!(
                    "internal.vcgen.type_error: index source `{array}` is not an active array in {context}"
                ));
            };
            let element = Box::new(element);
            if vc_semantic_expr_ty(expr, locals, context)? != *element {
                return Err(format!(
                    "internal.vcgen.type_error: array index has an inconsistent result type in {context}"
                ));
            }
            Ok(())
        }
        ExprKind::SelfFieldIndex { index, .. } => {
            validate_vc_expr(index, allow_param, context, locals)?;
            require_vc_expr_ty(
                index,
                Ty::Int(IntTy::U64),
                locals,
                "self-field array index",
                context,
            )
        }
        ExprKind::ClassFieldIndex { obj, index, .. } => {
            reject_affine_option_named_source(obj, locals, "a class-field receiver", context)?;
            if locals
                .get(obj)
                .as_ref()
                .is_some_and(|ty| ty.is_array_of(&Ty::Bool))
            {
                return Err(format!(
                    "internal.vcgen.type_error: Boolean arrays cannot be class-field receivers in {context}"
                ));
            }
            validate_vc_expr(index, allow_param, context, locals)?;
            require_vc_expr_ty(
                index,
                Ty::Int(IntTy::U64),
                locals,
                "class-field array index",
                context,
            )
        }
        ExprKind::AllocArray { elem, len, init } => {
            validate_vc_payload_ty(elem, allow_param, VcAggregateKind::Array, context)?;
            if expr.ty != Some(Ty::Array(Box::new(elem.clone()))) {
                return Err(format!(
                    "internal.vcgen.type_error: array allocation has an inconsistent result type in {context}"
                ));
            }
            validate_vc_expr(len, allow_param, context, locals)?;
            require_vc_expr_ty(
                len,
                Ty::Int(IntTy::U64),
                locals,
                "array-allocation length",
                context,
            )?;
            validate_vc_expr(init, allow_param, context, locals)?;
            require_vc_expr_ty(
                init,
                (*elem).clone(),
                locals,
                "array-allocation initializer",
                context,
            )?;
            Ok(())
        }
        ExprKind::Borrow { array, .. } => {
            reject_affine_option_named_source(array, locals, "a borrow source", context)?;
            Ok(())
        }
        ExprKind::Var(name) => {
            if locals.get(name).is_some_and(Ty::is_affine_option) {
                return Err(format!(
                    "vc.affine_option_value: affine-option local `{name}` cannot be copied as a value in {context}"
                ));
            }
            if locals
                .get(name)
                .as_ref()
                .is_some_and(|ty| ty.is_owned_array_of(&Ty::Bool))
                && expr.ty != locals.get(name).cloned()
            {
                return Err(format!(
                    "internal.vcgen.type_error: Boolean array variable lacks its checked owned-local type in {context}"
                ));
            }
            Ok(())
        }
        ExprKind::OptTake { .. } => Err(format!(
            "vc.option_take_position: `.take` is only admitted as the direct initializer of a fresh owned local in {context}"
        )),
        ExprKind::NoneE => validate_vc_option_operator(expr, context, locals),
        ExprKind::IntLit(_)
        | ExprKind::BoolLit(_)
        | ExprKind::SelfField { .. }
        | ExprKind::SelfFieldLen { .. } => Ok(()),
        ExprKind::ClassField { obj, .. }
        | ExprKind::RecordField { obj, .. }
        | ExprKind::ClassFieldLen { obj, .. } => {
            reject_affine_option_named_source(obj, locals, "an aggregate-field receiver", context)?;
            if locals
                .get(obj)
                .as_ref()
                .is_some_and(|ty| ty.is_array_of(&Ty::Bool))
            {
                return Err(format!(
                    "internal.vcgen.type_error: Boolean arrays cannot be aggregate-field receivers in {context}"
                ));
            }
            Ok(())
        }
        ExprKind::Len { array } => {
            if locals
                .get(array)
                .is_none_or(|ty| ty.as_array().is_none() && ty.as_slots().is_none())
            {
                return Err(format!(
                    "internal.vcgen.type_error: length source `{array}` is not an active array or owner-slot container in {context}"
                ));
            }
            if expr.ty != Some(Ty::Int(IntTy::U64)) {
                return Err(format!(
                    "internal.vcgen.type_error: sequence length has a non-u64 result in {context}"
                ));
            }
            Ok(())
        }
    }
}

fn validate_vc_take_initializer(
    expr: &Expr,
    locals: &HashMap<String, Ty>,
    mutable_locals: &HashSet<String>,
    context: &str,
) -> Result<(), String> {
    let ExprKind::OptTake { option, .. } = &expr.kind else {
        return Err(format!(
            "internal.vcgen.type_error: expected an affine-option take initializer in {context}"
        ));
    };
    let source_payload = locals
        .get(option)
        .and_then(|ty| ty.as_affine_option_payload());
    let Some(source_payload) = source_payload else {
        return Err(format!(
            "vc.option_take_not_local: `.take` source `{option}` is not an active owning-option local in {context}"
        ));
    };
    if expr.ty.as_ref() != Some(source_payload) {
        return Err(format!(
            "internal.vcgen.type_error: `.take` result disagrees with its source's payload in {context}"
        ));
    }
    if !mutable_locals.contains(option) {
        return Err(format!(
            "vc.option_take_immutable: `.take` source `{option}` is not mutable in {context}"
        ));
    }
    Ok(())
}

fn validate_vc_block_with_mutability(
    block: &[Stmt],
    allow_param: bool,
    context: &str,
    locals: &mut HashMap<String, Ty>,
    mutable_locals: &mut HashSet<String>,
) -> Result<(), String> {
    for statement in block {
        match statement {
            Stmt::Decl {
                ty,
                name,
                init,
                mutable,
                ..
            } => {
                if locals.contains_key(name) {
                    return Err(format!(
                        "vc.duplicate_local: declaration `{name}` would replace an active local in {context}"
                    ));
                }
                validate_vc_type_position(ty.clone(), allow_param, VcTypePosition::Local, context)?;
                if *ty == Ty::array(Ty::Bool) && init.is_none() {
                    return Err(format!(
                        "internal.vcgen.type_error: owned Boolean array local `{name}` must be initialized in {context}"
                    ));
                }
                if matches!(ty, Ty::Slots(_)) && init.is_none() {
                    return Err(format!(
                        "vc.slots_initializer: owner-slot local `{name}` must be initialized in {context}"
                    ));
                }
                if ty.is_affine_option() && init.is_none() {
                    return Err(format!(
                        "vc.affine_option_initializer: affine-option local `{name}` must be initialized in {context}"
                    ));
                }
                if ty.is_affine_option() && !*mutable {
                    return Err(format!(
                        "vc.affine_option_immutable: affine-option local `{name}` must be mutable in {context}"
                    ));
                }
                if let Some(init) = init {
                    let is_take = matches!(init.kind, ExprKind::OptTake { .. });
                    if is_take {
                        if *ty != Ty::array(Ty::Bool) {
                            return Err(format!(
                                "vc.option_take_position: `.take` must initialize an explicit owned Boolean-array local in {context}"
                            ));
                        }
                        validate_vc_take_initializer(init, locals, mutable_locals, context)?;
                    } else {
                        validate_vc_expr(init, allow_param, context, locals)?;
                    }
                    let declaration_is_bool_array = *ty == Ty::array(Ty::Bool);
                    let initializer_is_bool_array = init.ty == Some(Ty::array(Ty::Bool));
                    if declaration_is_bool_array != initializer_is_bool_array {
                        return Err(format!(
                            "internal.vcgen.type_error: Boolean array declaration has an incompatible initializer in {context}"
                        ));
                    }
                    if declaration_is_bool_array
                        && !is_fresh_bool_array_value(init)
                        && !is_affine_option_take(init)
                    {
                        return Err(format!(
                            "internal.vcgen.type_error: Boolean array local `{name}` must be initialized by a literal, allocation, or affine-option take in {context}"
                        ));
                    }
                    let declaration_is_affine_option = is_affine_bool_option(ty.clone());
                    let initializer_is_affine_option =
                        init.ty.clone().is_some_and(is_affine_bool_option);
                    if declaration_is_affine_option != initializer_is_affine_option {
                        return Err(format!(
                            "vc.affine_option_initializer: affine-option declaration `{name}` has an incompatible initializer in {context}"
                        ));
                    }
                    if declaration_is_affine_option
                        && !matches!(init.kind, ExprKind::NoneE | ExprKind::SomeE(_))
                    {
                        return Err(format!(
                            "vc.affine_option_initializer: affine-option local `{name}` must be initialized by `none` or `some(alloc_array<bool>(...))` in {context}"
                        ));
                    }
                }
                locals.insert(name.clone(), ty.clone());
                if *mutable {
                    mutable_locals.insert(name.clone());
                } else {
                    mutable_locals.remove(name);
                }
            }
            Stmt::VarDecl {
                name,
                init,
                ty,
                mutable,
                ..
            } => {
                if locals.contains_key(name) {
                    return Err(format!(
                        "vc.duplicate_local: declaration `{name}` would replace an active local in {context}"
                    ));
                }
                // `var t = o.take;` — the class-payload extraction route:
                // the take validator owns it, since the expression walk
                // refuses `.take` everywhere else.
                let class_take = matches!(init.kind, ExprKind::OptTake { .. })
                    && matches!(ty, Some(Ty::Class(_)));
                if class_take {
                    validate_vc_take_initializer(init, locals, mutable_locals, context)?;
                } else {
                    validate_vc_expr(init, allow_param, context, locals)?;
                }
                if let Some(ty) = ty {
                    validate_vc_type_position(
                        ty.clone(),
                        allow_param,
                        VcTypePosition::Local,
                        context,
                    )?;
                    if ty.is_affine_option() {
                        return Err(format!(
                            "vc.affine_option_inferred: affine-option local `{name}` requires an explicit type in {context}"
                        ));
                    }
                    let declaration_is_bool_array = *ty == Ty::array(Ty::Bool);
                    let initializer_is_bool_array = init.ty == Some(Ty::array(Ty::Bool));
                    if declaration_is_bool_array != initializer_is_bool_array {
                        return Err(format!(
                            "internal.vcgen.type_error: inferred Boolean array declaration has an incompatible initializer in {context}"
                        ));
                    }
                    if declaration_is_bool_array && !is_fresh_bool_array_value(init) {
                        return Err(format!(
                            "internal.vcgen.type_error: inferred Boolean array local `{name}` must be initialized by a literal or allocation in {context}"
                        ));
                    }
                    locals.insert(name.clone(), ty.clone());
                    if *mutable {
                        mutable_locals.insert(name.clone());
                    } else {
                        mutable_locals.remove(name);
                    }
                } else if init.ty.clone().is_some_and(is_bool_array) {
                    return Err(format!(
                        "internal.vcgen.type_error: inferred Boolean array local lacks its checked type in {context}"
                    ));
                } else if init.ty.clone().is_some_and(is_affine_bool_option) {
                    return Err(format!(
                        "vc.affine_option_inferred: inferred affine-option local `{name}` lacks an explicit checked type in {context}"
                    ));
                }
            }
            Stmt::Assign { name, value, .. } => {
                validate_vc_expr(value, allow_param, context, locals)?;
                if locals.get(name).is_some_and(Ty::is_affine_option)
                    || expr_is_affine_option(value, locals)
                {
                    return Err(format!(
                        "vc.affine_option_assign: affine-option local `{name}` cannot be rebound in {context}"
                    ));
                }
                let target_is_bool_array = locals
                    .get(name)
                    .is_some_and(|ty| ty.is_owned_array_of(&Ty::Bool));
                let value_is_bool_array = value.ty == Some(Ty::array(Ty::Bool));
                if target_is_bool_array {
                    return Err(format!(
                        "internal.vcgen.type_error: Boolean array local `{name}` cannot be rebound in {context}"
                    ));
                }
                if target_is_bool_array != value_is_bool_array {
                    return Err(format!(
                        "internal.vcgen.type_error: Boolean array assignment has an incompatible value in {context}"
                    ));
                }
            }
            Stmt::FieldAssign { value, .. } => {
                reject_affine_option_value(value, locals, "a field boundary", context)?;
                validate_vc_expr(value, allow_param, context, locals)?;
            }
            Stmt::ExprStmt(value) => {
                reject_owned_bool_array_value(value, locals, "an expression statement", context)?;
                reject_affine_option_value(value, locals, "an expression statement", context)?;
                validate_vc_expr(value, allow_param, context, locals)?;
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                validate_vc_expr(cond, allow_param, context, locals)?;
                require_vc_expr_ty(cond, Ty::Bool, locals, "`if` condition", context)?;
                let mut then_locals = locals.clone();
                let mut then_mutable_locals = mutable_locals.clone();
                validate_vc_block_with_mutability(
                    then_block,
                    allow_param,
                    context,
                    &mut then_locals,
                    &mut then_mutable_locals,
                )?;
                if let Some(else_block) = else_block {
                    let mut else_locals = locals.clone();
                    let mut else_mutable_locals = mutable_locals.clone();
                    validate_vc_block_with_mutability(
                        else_block,
                        allow_param,
                        context,
                        &mut else_locals,
                        &mut else_mutable_locals,
                    )?;
                }
            }
            Stmt::Return { value, .. } => {
                if let Some(value) = value {
                    // No owned-Boolean-array refusal here: a return is where
                    // an owner is handed over (ADR 0085), and
                    // `VcTypePosition::Return` below is what states which
                    // shapes may cross. The remaining boundaries — a call
                    // argument, an expression statement, a field store —
                    // keep theirs.
                    reject_affine_option_value(value, locals, "a function return", context)?;
                    if let Some(ty) = &value.ty {
                        validate_vc_type_position(
                            ty.clone(),
                            allow_param,
                            VcTypePosition::Return,
                            context,
                        )?;
                    }
                    validate_vc_expr(value, allow_param, context, locals)?;
                }
            }
            Stmt::FieldStore { index, value, .. } => {
                validate_vc_expr(index, allow_param, context, locals)?;
                require_vc_expr_ty(
                    index,
                    Ty::Int(IntTy::U64),
                    locals,
                    "field-store index",
                    context,
                )?;
                validate_vc_expr(value, allow_param, context, locals)?;
                reject_owned_bool_array_value(value, locals, "a field-store value", context)?;
                reject_affine_option_value(value, locals, "a field-store value", context)?;
            }
            Stmt::Store {
                array,
                index,
                value,
                ..
            } => {
                reject_affine_option_value(index, locals, "an array-store index", context)?;
                validate_vc_expr(index, allow_param, context, locals)?;
                require_vc_expr_ty(
                    index,
                    Ty::Int(IntTy::U64),
                    locals,
                    "array-store index",
                    context,
                )?;
                reject_affine_option_value(value, locals, "an array-store value", context)?;
                validate_vc_expr(value, allow_param, context, locals)?;
                let Some(element) = locals
                    .get(array)
                    .and_then(|ty| ty.as_array().map(|(element, _)| element.clone()))
                else {
                    return Err(format!(
                        "internal.vcgen.type_error: array-store target `{array}` is not an active array in {context}"
                    ));
                };
                let element = Box::new(element);
                require_vc_expr_ty(
                    value,
                    element.as_ref().clone(),
                    locals,
                    "array-store value",
                    context,
                )?;
            }
            Stmt::While { cond, body, .. } => {
                validate_vc_expr(cond, allow_param, context, locals)?;
                require_vc_expr_ty(cond, Ty::Bool, locals, "`while` condition", context)?;
                let mut body_locals = locals.clone();
                let mut body_mutable_locals = mutable_locals.clone();
                validate_vc_block_with_mutability(
                    body,
                    allow_param,
                    context,
                    &mut body_locals,
                    &mut body_mutable_locals,
                )?;
            }
            // Unsafe is a marker rather than a scope, so declarations made
            // inside it remain available to the following statements.
            Stmt::Unsafe { body, .. } => {
                validate_vc_block_with_mutability(
                    body,
                    allow_param,
                    context,
                    locals,
                    mutable_locals,
                )?;
            }
            Stmt::Expose {
                array,
                ptr,
                res,
                body,
                ..
            } => {
                reject_affine_option_named_source(array, locals, "an exposure source", context)?;
                match locals.get(array) {
                    Some(found) => match checked_array_payload(found) {
                        Some(Ty::Bool) => {
                            return Err(format!(
                                "internal.vcgen.type_error: Boolean array exposure is not supported in {context}"
                            ));
                        }
                        Some(Ty::Int(
                            IntTy::U8
                            | IntTy::U16
                            | IntTy::U32
                            | IntTy::U64
                            | IntTy::I8
                            | IntTy::I16
                            | IntTy::I32
                            | IntTy::I64,
                        )) => {}
                        Some(
                            Ty::Int(IntTy::TParam(_))
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
                            return Err(format!(
                                "internal.vcgen.type_error: exposure source `{array}` is not an executable integer array in {context}"
                            ));
                        }
                    },
                    None => {
                        return Err(format!(
                            "internal.vcgen.type_error: exposure source `{array}` is not an executable integer array in {context}"
                        ));
                    }
                }
                require_fresh_vc_bindings(&[ptr, res], locals, context)?;
                let mut body_locals = locals.clone();
                body_locals.insert(ptr.clone(), Ty::Raw(IntTy::U8));
                body_locals.insert(res.clone(), Ty::Res(ResKind::RawSpan));
                let mut body_mutable_locals = mutable_locals.clone();
                validate_vc_block_with_mutability(
                    body,
                    allow_param,
                    context,
                    &mut body_locals,
                    &mut body_mutable_locals,
                )?;
            }
            Stmt::StaticAlloc { size, ptr, res, .. } => {
                validate_vc_expr(size, allow_param, context, locals)?;
                require_vc_expr_ty(
                    size,
                    Ty::Int(IntTy::U64),
                    locals,
                    "static-allocation size",
                    context,
                )?;
                require_fresh_vc_bindings(&[ptr, res], locals, context)?;
                locals.insert(ptr.clone(), Ty::Raw(IntTy::U8));
                locals.insert(res.clone(), Ty::Res(ResKind::RawSpan));
            }
            Stmt::SystemAlloc {
                size,
                ptr,
                res,
                release,
                ..
            } => {
                validate_vc_expr(size, allow_param, context, locals)?;
                require_vc_expr_ty(
                    size,
                    Ty::Int(IntTy::U64),
                    locals,
                    "system-allocation size",
                    context,
                )?;
                require_fresh_vc_bindings(&[ptr, res, release], locals, context)?;
                locals.insert(ptr.clone(), Ty::Raw(IntTy::U8));
                locals.insert(res.clone(), Ty::Res(ResKind::RawSpan));
                locals.insert(release.clone(), Ty::Res(ResKind::SystemDealloc));
            }
            Stmt::SystemDealloc {
                ptr, res, release, ..
            } => {
                validate_vc_expr(ptr, allow_param, context, locals)?;
                require_vc_expr_ty(
                    ptr,
                    Ty::Raw(IntTy::U8),
                    locals,
                    "system-deallocation pointer",
                    context,
                )?;
                validate_vc_expr(res, allow_param, context, locals)?;
                require_vc_expr_ty(
                    res,
                    Ty::Res(ResKind::RawSpan),
                    locals,
                    "system-deallocation byte authority",
                    context,
                )?;
                validate_vc_expr(release, allow_param, context, locals)?;
                require_vc_expr_ty(
                    release,
                    Ty::Res(ResKind::SystemDealloc),
                    locals,
                    "system-deallocation release authority",
                    context,
                )?;
            }
            Stmt::Assert(_) => {}
        }
    }
    Ok(())
}

fn validate_vc_block(
    block: &[Stmt],
    allow_param: bool,
    context: &str,
    locals: &mut HashMap<String, Ty>,
) -> Result<(), String> {
    // This wrapper serves synthetic/unit callers that do not carry checked
    // declaration mutability. Conservatively treat their pre-seeded locals
    // as mutable; real functions enter through `validate_vc_fn`, which starts
    // empty and records each declaration's actual `mut` bit.
    let mut mutable_locals: HashSet<String> = locals.keys().cloned().collect();
    validate_vc_block_with_mutability(block, allow_param, context, locals, &mut mutable_locals)
}

fn validate_vc_fn(
    function: &Fn,
    allow_param: bool,
    trait_signature: bool,
    context: &str,
) -> Result<(), String> {
    for parameter in &function.params {
        validate_vc_type_position(
            parameter.ty.clone(),
            allow_param,
            if trait_signature {
                VcTypePosition::TraitParameter
            } else {
                VcTypePosition::Parameter
            },
            context,
        )?;
    }
    validate_vc_type_position(
        function.ret.clone(),
        allow_param,
        if trait_signature {
            VcTypePosition::TraitReturn
        } else {
            VcTypePosition::Return
        },
        context,
    )?;
    let mut locals: HashMap<String, Ty> = function
        .params
        .iter()
        .map(|parameter| (parameter.name.clone(), parameter.ty.clone()))
        .collect();
    let mut mutable_locals = HashSet::new();
    validate_vc_block_with_mutability(
        &function.body,
        allow_param,
        context,
        &mut locals,
        &mut mutable_locals,
    )
}

fn validate_vc_trait_fn(function: &Fn, context: &str) -> Result<(), String> {
    validate_vc_fn(function, true, true, context)?;
    if function
        .params
        .iter()
        .any(|parameter| matches!(parameter.ty, Ty::Bool | Ty::Record(_)))
    {
        return Err(format!(
            "internal.vcgen.type_error: Boolean and POD-record trait parameters are not supported in {context}"
        ));
    }
    if matches!(function.ret, Ty::Bool | Ty::Record(_)) {
        return Err(format!(
            "internal.vcgen.type_error: Boolean and POD-record trait returns are not supported in {context}"
        ));
    }
    Ok(())
}

fn validate_vc_method(function: &Fn, allow_param: bool, context: &str) -> Result<(), String> {
    validate_vc_fn(function, allow_param, false, context)?;
    if matches!(function.ret, Ty::Record(_)) {
        return Err(format!(
            "internal.vcgen.type_error: POD-record method returns are not supported in {context}"
        ));
    }
    Ok(())
}

fn seed_class_state_types(
    class: &ClassDecl,
    allow_param: bool,
    locals: &mut HashMap<String, Ty>,
    context: &str,
) -> Result<(), String> {
    for field in &class.fields {
        validate_vc_type_position(
            field.ty.clone(),
            allow_param,
            VcTypePosition::ClassField,
            context,
        )?;
        locals.insert(format!("self.{}", field.name), field.ty.clone());
    }
    Ok(())
}

fn validate_vc_class(class: &ClassDecl, allow_param: bool) -> Result<(), String> {
    let context = format!("class `{}`", class.name);
    for field in &class.fields {
        validate_vc_type_position(
            field.ty.clone(),
            allow_param,
            VcTypePosition::ClassField,
            &context,
        )?;
    }
    for init in &class.inits {
        validate_vc_fn(init, allow_param, false, &context)?;
    }
    for method in &class.methods {
        validate_vc_method(&method.f, allow_param, &context)?;
    }
    if let Some(deinit) = &class.deinit {
        let mut locals = HashMap::new();
        seed_class_state_types(class, allow_param, &mut locals, &context)?;
        validate_vc_block(deinit, allow_param, &context, &mut locals)?;
    }
    Ok(())
}

fn validate_vc_type_domain(program: &Program) -> Result<(), String> {
    for function in &program.fns {
        validate_vc_fn(
            function,
            false,
            false,
            &format!("function `{}`", function.name),
        )?;
    }
    for function in &program.fn_templates {
        validate_vc_fn(
            function,
            true,
            false,
            &format!("template `{}`", function.name),
        )?;
    }
    for class in &program.classes {
        validate_vc_class(class, false)?;
    }
    for class in &program.class_templates {
        validate_vc_class(class, true)?;
    }
    for record in &program.records {
        for field in &record.fields {
            validate_vc_type_position(
                field.ty.clone(),
                false,
                VcTypePosition::RecordField,
                &format!("record `{}`", record.name),
            )?;
        }
    }
    for trait_decl in &program.traits {
        for method in &trait_decl.methods {
            validate_vc_trait_fn(method, &format!("trait `{}`", trait_decl.name))?;
        }
    }
    for implementation in &program.impls {
        for function in &implementation.fns {
            validate_vc_fn(
                function,
                false,
                true,
                &format!("impl `{}`", implementation.trait_name),
            )?;
        }
    }
    Ok(())
}

/// A field's Lean type. Binding mode does not reach Lean: `[T]`, `&[T]`, and
/// `&mut [T]` are one `Sable.Seq T`, and a class or resource borrow is the
/// same structure or view its owner is. What mutability decides is binder
/// naming and havoc, never the type — so this dispatches on what the type
/// names and never on how it is bound.
fn lean_field_ty(ty: Ty, classes: &[ClassDecl], records: &[RecordDecl]) -> String {
    match ty.referent() {
        Ty::Int(_) | Ty::Param(_) => "Int".into(),
        Ty::Bool => "Bool".into(),
        Ty::Array(element) => lean_array_ty(element, records),
        Ty::Slots(payload) => lean_slots_ty(payload, classes, records),
        // A class-valued field is a nested structure (ADR 0020).
        Ty::Class(ci) => lean_class_name(&classes[*ci].name),
        Ty::Record(ri) => lean_record_name(&records[*ri].name),
        // A resource field contributes its *view* to the structure. The
        // authority it carries stays a checker property, so the class
        // gains a value and no obligation (ADR 0024/0029).
        Ty::Res(k) => lean_res_view_ty(*k, records),
        Ty::Raw(_) | Ty::RawRecord(_) => "Sable.RawPtr".into(),
        Ty::Option(element) => lean_option_ty(element, classes),
        Ty::OptionRaw(_) => "Option Sable.RawPtr".into(),
        Ty::Borrow(..) | Ty::Unit => unreachable!("checked: field types"),
    }
}

fn lean_record_field_layout(ty: Ty) -> String {
    match ty {
        Ty::Int(it) => it.lean_layout(),
        Ty::RawRecord(_) | Ty::OptionRaw(_) => "Sable.rawPtr.layout".into(),
        Ty::Bool
        | Ty::Param(_)
        | Ty::Class(_)
        | Ty::Record(_)
        | Ty::Array(_)
        | Ty::Slots(_)
        | Ty::Option(_)
        | Ty::Res(_)
        | Ty::Raw(_)
        | Ty::Borrow(..)
        | Ty::Unit => unreachable!("checked: record fields are raw-storable"),
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
        kind @ (ResKind::RawSpan
        | ResKind::PointsToU64
        | ResKind::OpenFile
        | ResKind::PosixWorld
        | ResKind::Uart
        | ResKind::SystemDealloc
        | ResKind::AllocatorState
        | ResKind::BlockLease
        | ResKind::LeasedPointsToU64
        | ResKind::FreeBlock
        | ResKind::FreeHeader
        | ResKind::ResourceMapPointsToU64) => kind.view_ty().into(),
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

/// Present a class destructor body to the ordinary callable generator.
///
/// Destructors have no source-level `Fn`, but both concrete classes and
/// retained ADR 0009 templates must traverse exactly the same symbolic body.
/// Keeping the synthetic signature here prevents those two verification
/// loops from silently disagreeing about what a destructor is.
fn synthesized_deinit(class: &ClassDecl) -> Option<Fn> {
    class
        .deinit
        .as_ref()
        .filter(|body| !body.is_empty())
        .map(|body| Fn {
            is_pub: false,
            extern_info: None,
            name: "deinit".to_string(),
            name_span: class.name_span,
            type_params: Vec::new(),
            type_bounds: Vec::new(),
            requires: Vec::new(),
            proof_reuse: ProofReuse::None,
            params: Vec::new(),
            ret: Ty::Unit,
            pres: Vec::new(),
            posts: Vec::new(),
            variant: None,
            body: body.clone(),
            span: class.span,
        })
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
        match p.ty.referent() {
            Ty::Int(_) | Ty::Param(_) => binders.push((p.name.clone(), "Int".into())),
            Ty::Bool => binders.push((p.name.clone(), "Bool".into())),
            Ty::Raw(_) | Ty::RawRecord(_) => binders.push((p.name.clone(), "Sable.RawPtr".into())),
            Ty::Res(k) => {
                binders.push((p.name.clone(), lean_res_view_ty(*k, &program.records)));
                if p.ty.is_unique_borrow() {
                    binders.push((
                        format!("_old_{}", p.name),
                        lean_res_view_ty(*k, &program.records),
                    ));
                }
            }
            Ty::Array(element) => {
                binders.push((p.name.clone(), lean_array_ty(element, &program.records)))
            }
            Ty::Slots(_) => {
                refuse_vc_type(
                    "internal.vcgen.slots_unsupported: extern owner-slot binder has no Lean type"
                        .into(),
                );
            }
            Ty::Class(ci) => {
                binders.push((p.name.clone(), lean_class_name(&program.classes[*ci].name)))
            }
            Ty::Record(ri) => {
                binders.push((p.name.clone(), lean_record_name(&program.records[*ri].name)))
            }
            Ty::OptionRaw(_) => binders.push((p.name.clone(), "Option Sable.RawPtr".into())),
            // `extern.param_abi` allows no option through the foreign
            // boundary, so an extern clause never binds one.
            Ty::Option(_) => unreachable!("extern.param_abi rejects option parameters"),
            Ty::Borrow(..) | Ty::Unit => {}
        }
    }
    for (i, c) in f.pres.iter().enumerate() {
        let owner = CallOwner::Function(f.name.clone());
        result.clause_wfs.push(ClauseWf {
            def_name: callable_lean_name("wf", &owner, "pre", i + 1),
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
        let owner = CallOwner::Function(f.name.clone());
        result.clause_wfs.push(ClauseWf {
            def_name: callable_lean_name("wf", &owner, "post", i + 1),
            binders: post_binders.clone(),
            text: preprocess_old_params(&c.text, &f.params),
            span: c.span,
            desc: format!("`post` of extern `{}`", f.name),
            result_ty: "Prop",
        });
    }
}

pub(crate) fn generate(
    program: &Program,
    checked: &CheckResult,
    source: &str,
    repo_root: &Path,
) -> Result<VcResult, String> {
    // The latch is per-generation: clear it here so a refusal left by an
    // earlier failed generation on this thread cannot be attributed to this one.
    let _ = take_vc_type_refusal();
    validate_vc_type_domain(program)?;
    let sigs = &checked.sigs;
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
            crate::profile::uart_poll_v1_hash(repo_root)
                .map(|hash| vec![(crate::profile::UART_POLL_V1_ID.into(), hash)])
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
                            lean_field_ty(f.ty.clone(), &program.classes, &program.records),
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
                        lean_ty: lean_field_ty(f.ty.clone(), &program.classes, &program.records),
                        layout: lean_record_field_layout(f.ty.clone()),
                        offset: f.offset,
                        wf: match f.ty {
                            Ty::Int(it) => Some(format!(
                                "{} ≤ value.{} ∧ value.{} ≤ {}",
                                it.lean_min(),
                                f.name,
                                f.name,
                                it.lean_max()
                            )),
                            Ty::Bool
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
                            | Ty::Unit => None,
                        },
                    })
                    .collect(),
                layout: r.layout,
                span: r.name_span,
            })
            .collect(),
        clause_wfs: Vec::new(),
        obligations: Vec::new(),
        transition_certificates: Vec::new(),
        argument_schedule_certificates: Vec::new(),
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
                        lean_field_ty(f.ty.clone(), &program.classes, &program.records),
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
                    lean_field_ty(f.ty.clone(), &program.classes, &program.records),
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
                def_name: injective_lean_components(
                    "wf",
                    &["class", c.name.as_str(), "invariant", &(i + 1).to_string()],
                ),
                binders: wf_binders,
                text: inv.text.clone(),
                span: inv.span,
                desc: format!("class invariant of `{}`", c.name),
                result_ty: "Prop",
            });
        }
    }

    let run_one = |f: &Fn,
                   fname: String,
                   call_owner: CallOwner,
                   cctx: Cctx,
                   result: &mut VcResult|
     -> Result<(), String> {
        let control = checked.control.body(&call_owner, f.span).map_err(|error| {
            format!(
                "internal.vcgen.control_plan_missing: {} at {}..{}",
                error.message, error.span.start, error.span.end
            )
        })?;
        let mut generator = Generator {
            f,
            fname,
            call_owner,
            cctx,
            control: Some(control),
            classes: &program.classes,
            records: &program.records,
            sigs,
            ownership: &checked.ownership,
            visited_checked_calls: HashSet::new(),
            checked_call_visits: HashMap::new(),
            checked_slot_visits: HashMap::new(),
            visited_option_takes: HashSet::new(),
            visited_slot_transitions: HashSet::new(),
            visited_slot_actions: HashSet::new(),
            visited_exposures: HashSet::new(),
            visited_sealed_operations: HashSet::new(),
            visited_loops: HashSet::new(),
            visited_value_transfers: HashSet::new(),
            visited_assignments: HashSet::new(),
            visited_field_assignments: HashSet::new(),
            visited_temporary_drops: HashSet::new(),
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
        generator.finish_checked_ownership();
        Ok(())
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
        if let ProofReuse::Adr0009IntModel(reuse) = &f.proof_reuse {
            let tname = reuse.template();
            if !program
                .fn_templates
                .iter()
                .any(|template| template.name == *tname)
            {
                return Err(format!(
                    "internal proof-reuse error: function `{}` names missing ADR 0009 template `{tname}`",
                    f.name
                ));
            }
            for (i, req) in f.requires.iter().enumerate() {
                let name = format!("{}.requires.{}", f.name, cslug(req));
                let owner = CallOwner::Function(f.name.clone()).certificate_component();
                result.obligations.push(Obligation {
                    thm_name: injective_lean_components(
                        "vc",
                        &[owner.as_str(), name.as_str(), &(i + 1).to_string()],
                    ),
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
        run_one(
            f,
            f.name.clone(),
            CallOwner::Function(f.name.clone()),
            Cctx::None,
            &mut result,
        )?;
    }

    // Fn templates (ADR 0009): verified once against the abstract
    // model — obligations bind `(T : Sable.IntModel)` with `T.wf` and
    // the declared `requires` as hypotheses.
    for f in &program.fn_templates {
        let call_owner = CallOwner::Function(f.name.clone());
        let control = checked.control.body(&call_owner, f.span).map_err(|error| {
            format!(
                "internal.vcgen.control_plan_missing: {} at {}..{}",
                error.message, error.span.start, error.span.end
            )
        })?;
        let mut generator = Generator {
            f,
            fname: f.name.clone(),
            call_owner,
            cctx: Cctx::None,
            control: Some(control),
            classes: &program.classes,
            records: &program.records,
            sigs,
            ownership: &checked.ownership,
            visited_checked_calls: HashSet::new(),
            checked_call_visits: HashMap::new(),
            checked_slot_visits: HashMap::new(),
            visited_option_takes: HashSet::new(),
            visited_slot_transitions: HashSet::new(),
            visited_slot_actions: HashSet::new(),
            visited_exposures: HashSet::new(),
            visited_sealed_operations: HashSet::new(),
            visited_loops: HashSet::new(),
            visited_value_transfers: HashSet::new(),
            visited_assignments: HashSet::new(),
            visited_field_assignments: HashSet::new(),
            visited_temporary_drops: HashSet::new(),
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
        generator.finish_checked_ownership();
    }

    // Class templates (ADR 0009): members, including the destructor, are
    // verified once against the abstract model — the acceptance test is
    // Vec<T>'s per-instance discharges collapsing to one template set.
    for c in &program.class_templates {
        // A destructor has no source-level `Fn`; retain this synthetic owner
        // through the member loop so its body visits the checker's
        // `<Template>::deinit` call records under the same abstract context.
        let deinit = synthesized_deinit(c);
        let members: Vec<(&Fn, String, CallOwner, Cctx)> = c
            .inits
            .iter()
            .map(|i| {
                (
                    i,
                    format!("{}::{}", c.name, i.name),
                    CallOwner::Constructor {
                        class: c.name.clone(),
                        init: i.name.clone(),
                    },
                    Cctx::Init(c),
                )
            })
            .chain(c.methods.iter().map(|m| {
                (
                    &m.f,
                    format!("{}::{}", c.name, m.f.name),
                    CallOwner::Method {
                        class: c.name.clone(),
                        method: m.f.name.clone(),
                    },
                    Cctx::Method(c, m.self_kind),
                )
            }))
            .chain(deinit.iter().map(|f| {
                (
                    f,
                    format!("{}::deinit", c.name),
                    CallOwner::Deinitializer {
                        class: c.name.clone(),
                    },
                    Cctx::Deinit(c),
                )
            }))
            .collect();
        for (f, fname, call_owner, cctx) in members {
            let control = checked.control.body(&call_owner, f.span).map_err(|error| {
                format!(
                    "internal.vcgen.control_plan_missing: {} at {}..{}",
                    error.message, error.span.start, error.span.end
                )
            })?;
            let mut generator = Generator {
                f,
                fname,
                call_owner,
                cctx,
                control: Some(control),
                classes: &program.classes,
                records: &program.records,
                sigs,
                ownership: &checked.ownership,
                visited_checked_calls: HashSet::new(),
                checked_call_visits: HashMap::new(),
                checked_slot_visits: HashMap::new(),
                visited_option_takes: HashSet::new(),
                visited_slot_transitions: HashSet::new(),
                visited_slot_actions: HashSet::new(),
                visited_exposures: HashSet::new(),
                visited_sealed_operations: HashSet::new(),
                visited_loops: HashSet::new(),
                visited_value_transfers: HashSet::new(),
                visited_assignments: HashSet::new(),
                visited_field_assignments: HashSet::new(),
                visited_temporary_drops: HashSet::new(),
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
            generator.finish_checked_ownership();
        }
    }
    // Destructor bodies are collected first and run after, because the
    // synthesized `Fn` each needs must outlive the generator that reads it.
    let mut deinit_fns: Vec<(Fn, &ClassDecl)> = Vec::new();
    for c in &program.classes {
        // Template-verified class instances (ADR 0009): the
        // template's theorems cover their member obligations.
        if let ProofReuse::Adr0009IntModel(reuse) = &c.proof_reuse {
            let template = reuse.template();
            if !program
                .class_templates
                .iter()
                .any(|retained| retained.name == *template)
            {
                return Err(format!(
                    "internal proof-reuse error: class `{}` names missing ADR 0009 template `{template}`",
                    c.name
                ));
            }
            continue;
        }
        for init in &c.inits {
            run_one(
                init,
                format!("{}::{}", c.name, init.name),
                CallOwner::Constructor {
                    class: c.name.clone(),
                    init: init.name.clone(),
                },
                Cctx::Init(c),
                &mut result,
            )?;
        }
        for m in &c.methods {
            run_one(
                &m.f,
                format!("{}::{}", c.name, m.f.name),
                CallOwner::Method {
                    class: c.name.clone(),
                    method: m.f.name.clone(),
                },
                Cctx::Method(c, m.self_kind),
                &mut result,
            )?;
        }
        // A destructor's body is verified like any other: its statements
        // owe their own obligations. What it does *not* owe is the class
        // invariant at exit (ADR 0029).
        if let Some(synth) = synthesized_deinit(c) {
            deinit_fns.push((synth, c));
        }
    }
    for (f, c) in &deinit_fns {
        run_one(
            f,
            format!("{}::deinit", c.name),
            CallOwner::Deinitializer {
                class: c.name.clone(),
            },
            Cctx::Deinit(c),
            &mut result,
        )?;
    }
    // A type the preflight should have refused reached a helper with no error
    // channel. Fail here rather than publish a theorem naming a Lean type that
    // does not exist.
    if let Some(refusal) = take_vc_type_refusal() {
        return Err(refusal);
    }
    // This is intentionally a post-check, post-generation pass over the typed
    // AST and the sealed ownership records.  Running it here preserves each
    // existing VC consumer's own fail-closed diagnostics while still making a
    // complete schedule certificate mandatory before any result can escape.
    result.argument_schedule_certificates =
        crate::argument_schedule::extract(program, &checked.ownership)?;
    Ok(result)
}

/// The length relation a site supplies for a fresh sequence state. The facts
/// every inhabitant of an array or owner-slot type satisfies do not include
/// one: what a fresh length equals depends on where the fresh state is made.
/// In particular, array stores and slot take/put preserve length, while a
/// whole owner-slot replacement does not.
enum LenFact {
    /// `0 ≤ len ∧ len ≤ u64.max` — a parameter's entry state.
    Bounded,
    /// `len = (<prior>.len)` — a havoc that replaces a still-nameable state.
    Eq(String),
    /// No usable relation (the prior chain died with a body-local name).
    Skip,
}

/// Which checked call boundary is asking for a result state.
///
/// Ordinary functions transport records and owned arrays. Member calls have
/// not admitted those two result shapes yet, so the shared result dispatcher
/// keeps their defensive VC refusal until the checker boundary moves with it.
#[derive(Clone, Copy, PartialEq, Eq)]
enum CallResultSite {
    Function,
    Member,
}

#[derive(Debug, Clone)]
enum Val {
    Int(String),
    Prop(String),
    Opt(String),
    /// Symbolic array value: entry binder or a `.set` chain over it.
    Arr(String),
    /// Symbolic owner-slot value: a `Seq (Option payload)` binder or `.set`
    /// chain. Kept distinct from arrays so no copy-index rule can consume it.
    Slots(String),
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

impl Val {
    /// The Lean term stored in the symbolic environment for place write-back.
    fn writeback_term(&self) -> Option<String> {
        match self {
            Val::Int(term)
            | Val::Opt(term)
            | Val::Arr(term)
            | Val::Slots(term)
            | Val::Obj(term)
            | Val::Record(term)
            | Val::View(term)
            | Val::Ptr(term) => Some(term.clone()),
            Val::Prop(proposition) => Some(lean_bool_value(proposition)),
            Val::Unit => None,
        }
    }
}

/// Exhaustive VC-side view of the element carried by an owned or borrowed
/// array.  This is intentionally local to the trusted generator: a new `Ty`
/// or loan mode must receive an explicit symbolic-array decision before the
/// generator compiles.
fn checked_array_payload(ty: &Ty) -> Option<&Ty> {
    match ty {
        Ty::Array(element) => Some(element),
        Ty::Borrow(Mutability::Shared, referent) | Ty::Borrow(Mutability::Mut, referent) => {
            match referent.as_ref() {
                Ty::Array(element) => Some(element),
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
            }
        }
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

/// Convert one evaluated array element to its Lean term.  Both axes are
/// exhaustive instead of ending a `(Ty, Val)` product match in a wildcard;
/// extending either semantic enum therefore forces a compiler error here.
fn checked_array_payload_value(
    payload: &Ty,
    evaluated: Val,
    unsupported: impl std::ops::Fn(&Ty) -> String,
) -> String {
    let reject = |payload: &Ty| {
        refuse_vc_type(unsupported(payload));
        UNSUPPORTED_LEAN_VALUE.to_string()
    };
    match payload {
        Ty::Bool => match evaluated {
            Val::Prop(proposition) => lean_bool_value(&proposition),
            Val::Int(_)
            | Val::Opt(_)
            | Val::Arr(_)
            | Val::Slots(_)
            | Val::Obj(_)
            | Val::Record(_)
            | Val::View(_)
            | Val::Ptr(_)
            | Val::Unit => reject(payload),
        },
        Ty::Int(_) | Ty::Param(_) => match evaluated {
            Val::Int(value) => value,
            Val::Prop(_)
            | Val::Opt(_)
            | Val::Arr(_)
            | Val::Slots(_)
            | Val::Obj(_)
            | Val::Record(_)
            | Val::View(_)
            | Val::Ptr(_)
            | Val::Unit => reject(payload),
        },
        Ty::Record(_) => match evaluated {
            Val::Record(value) => value,
            Val::Int(_)
            | Val::Prop(_)
            | Val::Opt(_)
            | Val::Arr(_)
            | Val::Slots(_)
            | Val::Obj(_)
            | Val::View(_)
            | Val::Ptr(_)
            | Val::Unit => reject(payload),
        },
        Ty::Class(_)
        | Ty::Array(_)
        | Ty::Slots(_)
        | Ty::Option(_)
        | Ty::OptionRaw(_)
        | Ty::Res(_)
        | Ty::Raw(_)
        | Ty::RawRecord(_)
        | Ty::Borrow(..)
        | Ty::Unit => reject(payload),
    }
}

/// A typed dead-end value for a latched internal refusal. The generator never
/// publishes it: [`generate`] returns the refusal instead. Keeping the shape
/// aligned with the checked expression prevents a failed trap-site lookup
/// from cascading into an unrelated pattern-match panic on the way out.
fn refused_expression_value(expression: &Expr) -> Val {
    match expression.ty.as_ref().map(Ty::referent) {
        Some(Ty::Int(_) | Ty::Param(_)) => Val::Int(UNSUPPORTED_LEAN_VALUE.into()),
        Some(Ty::Bool) => Val::Prop("False".into()),
        Some(Ty::Option(_) | Ty::OptionRaw(_)) => Val::Opt(UNSUPPORTED_LEAN_VALUE.into()),
        Some(Ty::Array(_)) => Val::Arr(UNSUPPORTED_LEAN_VALUE.into()),
        Some(Ty::Slots(_)) => Val::Slots(UNSUPPORTED_LEAN_VALUE.into()),
        Some(Ty::Class(_)) => Val::Obj(UNSUPPORTED_LEAN_VALUE.into()),
        Some(Ty::Record(_)) => Val::Record(UNSUPPORTED_LEAN_VALUE.into()),
        Some(Ty::Res(_)) => Val::View(UNSUPPORTED_LEAN_VALUE.into()),
        Some(Ty::Raw(_) | Ty::RawRecord(_)) => Val::Ptr(UNSUPPORTED_LEAN_VALUE.into()),
        Some(Ty::Borrow(..) | Ty::Unit) | None => Val::Unit,
    }
}

#[derive(Clone)]
enum Tail<'a> {
    FnEnd,
    /// The end of a lexical branch arm. Falling through consumes the exact
    /// checked scope route before symbolic execution resumes in the parent
    /// scope. Keeping the continuation explicit prevents an arm local from
    /// leaking into `rest` when paths are flattened for symbolic execution.
    Scope {
        normal_exit: Option<ExitRoute>,
        rest: Vec<&'a Stmt>,
        parent_scope: ScopeId,
        outer: Box<Tail<'a>>,
    },
    Loop {
        backedge: Option<ExitRoute>,
        invariants: &'a [Clause],
        variant: &'a Clause,
        v0: String,
    },
    /// The body of a lexical exposure. Falling off its end is where the
    /// array is reconstructed, which is why an exposure body may not
    /// `return`: leaving any other way would skip the reconstruction.
    Expose {
        body_exit: ExitRoute,
        close: ExitRoute,
        parent_scope: ScopeId,
        array: String,
        res: String,
        mutable: bool,
        kw_span: Span,
        release_loan: Place,
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
    /// Flavor-preserving identity for the checker-authored call handoff.
    call_owner: CallOwner,
    cctx: Cctx<'a>,
    /// The checker-sealed lexical plan for this exact semantic owner.
    /// Symbolic execution consumes its branch, loop, exposure, and return
    /// routes and direct source trap sites; missing/aliased body,
    /// parent-scope, or trap identities fail before a path can mutate proof
    /// state.
    control: Option<&'a ControlBody>,
    classes: &'a [ClassDecl],
    records: &'a [RecordDecl],
    sigs: &'a HashMap<String, FnSig>,
    ownership: &'a CheckedOwnershipPlan,
    /// Checked call sites reached by at least one symbolic path. The facts
    /// themselves remain immutable: a join can make the same source call
    /// execute once per incoming symbolic path.
    visited_checked_calls: HashSet<CallSiteKey>,
    /// Deterministic DFS visit ordinal for each source call. Each visit
    /// performs a distinct havoc and therefore receives a distinct fixed
    /// transition certificate.
    checked_call_visits: HashMap<CallSiteKey, usize>,
    /// Deterministic DFS visit ordinal for each checked owner-slot operation.
    /// A branch join can revisit one immutable source transition, and every
    /// resulting write-back receives an injective certificate identity.
    checked_slot_visits: HashMap<EffectSiteKey, usize>,
    /// Checker-authored non-call ownership effects reached by at least one
    /// symbolic path. Like calls, the records are immutable and may be
    /// revisited after a path split; this set proves per-body coverage.
    visited_option_takes: HashSet<EffectSiteKey>,
    visited_slot_transitions: HashSet<EffectSiteKey>,
    visited_slot_actions: HashSet<(ScopeId, Span)>,
    visited_exposures: HashSet<EffectSiteKey>,
    visited_sealed_operations: HashSet<EffectSiteKey>,
    visited_loops: HashSet<EffectSiteKey>,
    visited_value_transfers: HashSet<crate::ownership::ValueTransferKey>,
    /// Retained cleanup actions reached by at least one symbolic path. A set
    /// (rather than destructive consumption) deliberately permits the same
    /// source action to be revisited after a symbolic branch split.
    visited_assignments: HashSet<(ScopeId, Span)>,
    visited_field_assignments: HashSet<(ScopeId, Span)>,
    visited_temporary_drops: HashSet<(ScopeId, Span)>,
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
                        Some(Val::Int(s)) | Some(Val::Arr(s)) | Some(Val::Slots(s))
                        | Some(Val::Obj(s)) | Some(Val::View(s)) | Some(Val::Ptr(s)) => {
                            format!("{s}")
                        }
                        Some(Val::Prop(p)) => lean_bool_value(p),
                        // Parenthesized so an option chain stays one
                        // constructor argument: `some (7)` spliced bare
                        // would parse as two.
                        Some(Val::Opt(s)) => format!("({s})"),
                        // A field state this constructor literal cannot
                        // splice is a named refusal, never a silent `0`:
                        // a wrong literal here is a false-proof machine
                        // (ADR 0074), not a crash.
                        Some(Val::Record(_)) | Some(Val::Unit) | None => {
                            refuse_vc_type(format!(
                                "internal.vcgen.field_state_unsupported: field `{}` of \
                                 `{}` has no constructor-literal state",
                                fld.name, class.name
                            ));
                            "0".to_string()
                        }
                    }
                })
                .collect::<Vec<_>>()
                .join(" ")
        );
        let mut map = HashMap::new();
        map.insert("self".to_string(), literal.clone());
        for fld in &class.fields {
            match self.env.get(&format!("self.{}", fld.name)) {
                Some(Val::Int(s)) | Some(Val::Arr(s)) | Some(Val::Slots(s)) | Some(Val::Obj(s))
                | Some(Val::View(s)) | Some(Val::Ptr(s)) => {
                    map.insert(fld.name.clone(), s.clone());
                }
                Some(Val::Prop(p)) => {
                    map.insert(fld.name.clone(), lean_bool_value(p));
                }
                // Parenthesized as at a call: dot-notation in the init's
                // posts must bind the whole chain.
                Some(Val::Opt(s)) => {
                    map.insert(fld.name.clone(), format!("({s})"));
                }
                // A field silently missing from the substitution map makes
                // an init post about that field vacuously unbindable; refuse
                // by name instead.
                Some(Val::Record(_)) | Some(Val::Unit) | None => {
                    refuse_vc_type(format!(
                        "internal.vcgen.field_state_unsupported: field `{}` of `{}` has \
                         no substitution state",
                        fld.name, class.name
                    ));
                }
            }
        }
        (literal, map)
    }

    /// The Lean binder type of a local or parameter.
    fn lean_ty_of(&self, name: &str) -> String {
        match self.var_tys.get(name).map(Ty::referent) {
            Some(Ty::Class(ci)) => lean_class_name(&self.classes[*ci].name),
            Some(Ty::Record(ri)) => lean_record_name(&self.records[*ri].name),
            Some(Ty::Res(k)) => lean_res_view_ty(*k, self.records),
            Some(Ty::Raw(_)) | Some(Ty::RawRecord(_)) => "Sable.RawPtr".to_string(),
            Some(Ty::OptionRaw(_)) => "Option Sable.RawPtr".to_string(),
            Some(Ty::Option(element)) => lean_option_ty(element, self.classes),
            Some(Ty::Int(_)) | Some(Ty::Param(_)) => "Int".to_string(),
            Some(Ty::Bool) => "Bool".to_string(),
            Some(Ty::Array(element)) => lean_array_ty(element, self.records),
            Some(Ty::Slots(payload)) => lean_slots_ty(payload, self.classes, self.records),
            Some(Ty::Unit) | Some(Ty::Borrow(..)) | None => {
                unreachable!("checked: value has a Lean binder type")
            }
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
            .filter_map(|(name, ty)| match ty.referent() {
                Ty::Int(_) | Ty::Param(_) => Some((name.clone(), "Int".to_string())),
                Ty::Bool => Some((name.clone(), "Bool".to_string())),
                Ty::Array(element) => Some((name.clone(), lean_array_ty(element, self.records))),
                Ty::Slots(payload) => Some((
                    name.clone(),
                    lean_slots_ty(payload, self.classes, self.records),
                )),
                Ty::Class(ci) => Some((name.clone(), lean_class_name(&self.classes[*ci].name))),
                Ty::Record(ri) => Some((name.clone(), lean_record_name(&self.records[*ri].name))),
                // A resource binds its *view*; the authority it names is
                // a checker property and appears nowhere in Lean.
                Ty::Res(k) => Some((name.clone(), lean_res_view_ty(*k, self.records))),
                Ty::Raw(_) | Ty::RawRecord(_) => Some((name.clone(), "Sable.RawPtr".to_string())),
                Ty::OptionRaw(_) => Some((name.clone(), "Option Sable.RawPtr".to_string())),
                Ty::Option(element) => Some((name.clone(), lean_option_ty(element, self.classes))),
                Ty::Borrow(..) | Ty::Unit => None,
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
    /// The payload fact a checked option state carries, over its value
    /// chain: an integer leaf's `.value` is in range whether present or
    /// junk-on-none (`getD default = 0`, ADR 0008), and a nested payload's
    /// fact sits one `.value` deeper — an absent level reads `none`, whose
    /// own `.value` reads the junk of the level below, so the composed
    /// fact holds on every path. One fact per chain, at the integer leaf.
    fn push_option_value_facts(&mut self, payload: &Ty, base: &str, term: &str) {
        match payload {
            Ty::Int(it) => {
                self.push_hyp_unique(
                    format!("h_{base}_range"),
                    self.r_prop(&format!("(({term}).value)"), *it),
                );
            }
            Ty::Option(inner) => {
                let deeper = format!("(({term}).value)");
                self.push_option_value_facts(inner, base, &deeper);
            }
            // `Bool` is its own complete domain, and an abstract payload
            // deliberately carries no fact (the flat rule); the rest have
            // no copy-option value chain to state a fact over.
            Ty::Bool
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
            | Ty::Unit => {}
        }
    }

    /// Facts every present slot payload carries. They are stated under the
    /// occupancy equation, so allocation establishes them vacuously, put
    /// transports them from its staged value, and take may recover them for
    /// the unique returned payload.
    fn slot_payload_fact_props(&self, payload: &Ty, value: &str) -> Vec<(String, String)> {
        match payload {
            Ty::Bool => Vec::new(),
            ty @ (Ty::Int(_) | Ty::Param(_)) => vec![(
                "range".into(),
                self.r_prop(value, adr0009_ty_int_model(ty.clone())),
            )],
            Ty::Record(record) => vec![(
                "wf".into(),
                format!(
                    "{}.wf {value}",
                    lean_record_name(&self.records[*record].name)
                ),
            )],
            Ty::Class(class) => {
                let declaration = &self.classes[*class];
                let map = self.class_state_map(declaration, value);
                declaration
                    .invariants
                    .iter()
                    .map(|invariant| {
                        (
                            format!("inv_{}", chslug(invariant)),
                            substitute(&invariant.text, &map, None),
                        )
                    })
                    .collect()
            }
            Ty::Array(_)
            | Ty::Slots(_)
            | Ty::Option(_)
            | Ty::OptionRaw(_)
            | Ty::Res(_)
            | Ty::Raw(_)
            | Ty::RawRecord(_)
            | Ty::Borrow(..)
            | Ty::Unit => {
                refuse_vc_type(format!(
                    "internal.vcgen.slot_payload_unsupported: `{}` has no present-cell fact",
                    payload.name()
                ));
                Vec::new()
            }
        }
    }

    fn push_slot_payload_facts(&mut self, payload: &Ty, base: &str, slots: &str) {
        for (suffix, fact) in self.slot_payload_fact_props(payload, "value") {
            self.push_hyp_unique(
                format!("h_{base}_present_{suffix}"),
                format!(
                    "∀ k, 0 ≤ k → k < ({slots}.len) → ∀ value, ({slots}.get k) = some value → ({fact})"
                ),
            );
        }
    }

    fn push_class_state_facts(&mut self, class: &ClassDecl, binder: &str) {
        // Deduped (`_2` suffixes) like class invariants: two borrowed
        // arguments of the same class must not shadow each other's facts
        // (`cmp(&Nat a, &Nat b)` needs both).
        for fld in &class.fields {
            match &fld.ty {
                Ty::Int(it) => {
                    self.push_hyp_unique(
                        format!("h_field_{}_range", fld.name),
                        self.r_prop(&format!("({binder}.{})", fld.name), *it),
                    );
                }
                Ty::Param(parameter) => {
                    let model = adr0009_ty_int_model(Ty::Param(*parameter));
                    self.push_hyp_unique(
                        format!("h_field_{}_range", fld.name),
                        self.r_prop(&format!("({binder}.{})", fld.name), model),
                    );
                }
                Ty::Array(elem) => {
                    let path = format!("({binder}.{})", fld.name);
                    self.push_hyp_unique(
                        format!("h_field_{}_len", fld.name),
                        format!("0 ≤ {path}.len ∧ {path}.len ≤ u64.max"),
                    );
                    if let Some(prop) = self.array_element_range_prop(&path, &elem.clone()) {
                        self.push_hyp_unique(format!("h_field_{}_elems", fld.name), prop);
                    }
                }
                // A class-valued field carries its own class's facts and
                // invariant, one level down (ADR 0020).
                Ty::Class(ci) => {
                    let inner = self.classes[*ci].clone();
                    let path = format!("{binder}.{}", fld.name);
                    self.push_class_state_facts(&inner, &path);
                    self.push_invariant_hyps(&inner, &path);
                }
                // A resource field contributes its view's well-formedness:
                // every view a field can hold carried it at the binding
                // site the value came from (a parameter, an allocation, or
                // a sealed operation's fresh state).
                Ty::Res(k) => {
                    let path = format!("({binder}.{})", fld.name);
                    for (h, prop) in
                        view_wf_hyps(*k, &format!("field_{}", fld.name), &path, self.records)
                    {
                        self.push_hyp_unique(h, prop);
                    }
                }
                // A copyable option field carries its integer payload's
                // range fact over `.value`, exactly as a fresh option
                // parameter does: the absent case reads the typed junk
                // model (`getD default = 0`, ADR 0008), in range for every
                // integer type. A `bool` payload needs no fact.
                Ty::Option(payload) => {
                    if let Ty::Int(it) = payload.as_ref() {
                        self.push_hyp_unique(
                            format!("h_field_{}_range", fld.name),
                            self.r_prop(&format!("(({binder}.{}).value)", fld.name), *it),
                        );
                    }
                }
                Ty::Slots(_) => {
                    let Ty::Slots(payload) = &fld.ty else {
                        unreachable!()
                    };
                    let path = format!("({binder}.{})", fld.name);
                    self.push_hyp_unique(
                        format!("h_field_{}_len", fld.name),
                        format!("0 ≤ {path}.len ∧ {path}.len ≤ u64.max"),
                    );
                    self.push_slot_payload_facts(payload, &format!("field_{}", fld.name), &path);
                }
                // No representability fact exists for the rest: `Bool` is
                // its own complete domain and a raw pointer is
                // unconstrained data.
                Ty::Bool
                | Ty::Raw(_)
                | Ty::RawRecord(_)
                | Ty::OptionRaw(_)
                | Ty::Record(_)
                | Ty::Unit
                | Ty::Borrow(..) => {}
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
            .filter_map(|(p, aval)| {
                p.ty.as_class_borrow()
                    .map(|(aci, _)| (p.name.clone(), aci, aval.clone()))
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

    /// What a fresh symbolic state for a value of a type *is*: one binder of
    /// the type's Lean shape, the facts every checked inhabitant satisfies,
    /// and the environment value that holds it. Parameter entry, the
    /// call-site havoc, and both loop-head havoc branches all read their
    /// answer here — the three divergent copies of this dispatch are where
    /// every stale-chain hole has lived (ADR 0074).
    ///
    /// Exhaustive over `Ty` with no wildcard: a shape with no fresh-state
    /// story latches a named fail-closed refusal instead of leaving a
    /// pre-havoc chain in the environment, and a new `Ty` constructor is a
    /// compile error here rather than a shape no havoc ever looked at.
    ///
    /// `binder` is the fresh binder's name — that is site policy (`_old_p`,
    /// `_selfN_f`, `_arrN`, a source-hinted symbol) and never decides the
    /// Lean shape. `base` anchors hypothesis names (`h_{base}_range`,
    /// `h_{base}_len`, ...), so discharge scripts survive where the sites
    /// already agreed on them.
    fn fresh_state_for(&mut self, ty: &Ty, binder: &str, base: &str, len: LenFact) -> Val {
        // Dispatch on what the type *names*: `&mut [T]`'s fresh state is a
        // sequence exactly as `[T]`'s is, and how the storage is bound was
        // the caller's question (a shared borrow is never havocked, and a
        // unique borrow's binder name is the caller's choice).
        match ty.referent() {
            Ty::Int(it) => {
                let it = *it;
                self.binders.push((binder.to_string(), "Int".into()));
                self.push_hyp_unique(format!("h_{base}_range"), self.r_prop(binder, it));
                Val::Int(binder.to_string())
            }
            Ty::Param(parameter) => {
                let model = adr0009_ty_int_model(Ty::Param(*parameter));
                self.binders.push((binder.to_string(), "Int".into()));
                self.push_hyp_unique(format!("h_{base}_range"), self.r_prop(binder, model));
                Val::Int(binder.to_string())
            }
            Ty::Bool => {
                self.binders.push((binder.to_string(), "Bool".into()));
                Val::Prop(format!("({binder} = true)"))
            }
            // A fresh option holds a checked program value when present, so
            // an integer payload carries its range fact over `.value` (the
            // absent case reads `getD default = 0`, in range for every
            // integer type — ADR 0008's junk-value model). `Bool` is its own
            // complete domain and needs no fact.
            Ty::Option(element) => {
                let element = element.as_ref().clone();
                self.binders
                    .push((binder.to_string(), lean_option_ty(&element, self.classes)));
                self.push_option_value_facts(&element, base, binder);
                Val::Opt(binder.to_string())
            }
            Ty::OptionRaw(_) => {
                self.binders
                    .push((binder.to_string(), "Option Sable.RawPtr".into()));
                Val::Opt(binder.to_string())
            }
            Ty::Record(ri) => {
                let record = lean_record_name(&self.records[*ri].name);
                self.binders.push((binder.to_string(), record.clone()));
                // Nominal well-formedness is an implicit checked-type
                // postcondition: every record value a program can hold was
                // built through the checked constructor.
                self.push_hyp_unique(format!("h_{base}_wf"), format!("{record}.wf {binder}"));
                Val::Record(binder.to_string())
            }
            // A fresh class state carries its field facts and the class
            // invariant: class values only arise from init/method exits,
            // each of which re-establishes it. (The one state that may NOT
            // assume the invariant — mid-member `self` — is versioned by the
            // havoc's own `self` branch, never through here.)
            Ty::Class(ci) => {
                let cd = &self.classes[*ci];
                self.binders
                    .push((binder.to_string(), lean_class_name(&cd.name)));
                self.push_class_state_facts(cd, binder);
                self.push_invariant_hyps(cd, binder);
                Val::Obj(binder.to_string())
            }
            // A fresh resource state is a fresh *view* with the view's own
            // well-formedness; the token it belongs to is a checker property
            // and appears nowhere here (ADR 0024).
            Ty::Res(k) => {
                let k = *k;
                self.binders
                    .push((binder.to_string(), lean_res_view_ty(k, self.records)));
                for (h, prop) in view_wf_hyps(k, base, binder, self.records) {
                    self.push_hyp_unique(h, prop);
                }
                Val::View(binder.to_string())
            }
            // A raw pointer is data — provenance and an offset, no
            // authority. A fresh one is unconstrained: whatever is known
            // about it must come from the site's own facts or invariants.
            Ty::Raw(_) | Ty::RawRecord(_) => {
                self.binders
                    .push((binder.to_string(), "Sable.RawPtr".into()));
                Val::Ptr(binder.to_string())
            }
            Ty::Array(element) => {
                let element = element.as_ref().clone();
                self.binders
                    .push((binder.to_string(), lean_array_ty(&element, self.records)));
                match len {
                    LenFact::Bounded => self.push_hyp_unique(
                        format!("h_{base}_len"),
                        format!("0 ≤ {binder}.len ∧ {binder}.len ≤ u64.max"),
                    ),
                    LenFact::Eq(prior) => self.push_hyp_unique(
                        format!("h_{base}_len"),
                        format!("({binder}.len) = ({prior}.len)"),
                    ),
                    LenFact::Skip => {}
                }
                if let Some(prop) = self.array_element_range_prop(binder, &element) {
                    self.push_hyp_unique(format!("h_{base}_elems"), prop);
                }
                Val::Arr(binder.to_string())
            }
            Ty::Slots(payload) => {
                self.binders.push((
                    binder.to_string(),
                    lean_slots_ty(payload, self.classes, self.records),
                ));
                match len {
                    LenFact::Bounded => self.push_hyp_unique(
                        format!("h_{base}_len"),
                        format!("0 ≤ {binder}.len ∧ {binder}.len ≤ u64.max"),
                    ),
                    LenFact::Eq(prior) => self.push_hyp_unique(
                        format!("h_{base}_len"),
                        format!("({binder}.len) = ({prior}.len)"),
                    ),
                    LenFact::Skip => {}
                }
                self.push_slot_payload_facts(payload, base, binder);
                Val::Slots(binder.to_string())
            }
            Ty::Unit => {
                refuse_vc_type(format!(
                    "internal.vcgen.fresh_state_unsupported: `()` has no fresh symbolic \
                     state (for `{base}`)"
                ));
                Val::Unit
            }
            // `referent` looks through one borrow, so this arm is a borrow
            // of a borrow — a shape no checked program holds storage under.
            Ty::Borrow(..) => {
                refuse_vc_type(format!(
                    "internal.vcgen.fresh_state_unsupported: a borrow of a borrow reached \
                     a havoc path (for `{base}`)"
                ));
                Val::Unit
            }
        }
    }

    /// Bind one call result and return its symbolic value.
    ///
    /// Free and member calls used to carry four parallel `Ty` case lists:
    /// two that chose the Lean binder/facts and two that reconstructed the
    /// corresponding [`Val`]. Keeping those lists synchronized is a semantic
    /// requirement, not presentation, so the answer lives in one exhaustive
    /// dispatch. Option payload facts remain at each caller after user posts;
    /// a match-shaped post must not capture their motive (ADR 0074).
    fn bind_call_result(&mut self, ty: &Ty, binder: &str, site: CallResultSite) -> Val {
        let base = binder.trim_start_matches('_').to_string();
        match ty {
            ty @ (Ty::Int(_) | Ty::Param(_)) => {
                self.binders.push((binder.to_string(), "Int".into()));
                self.push_hyp_unique(
                    format!("h_{base}_range"),
                    self.r_prop(binder, adr0009_ty_int_model(ty.clone())),
                );
                Val::Int(binder.to_string())
            }
            Ty::Bool => {
                // A call result is the logic's proposition `result`; other
                // fresh Boolean program states are `Bool` binders read as a
                // proposition. This is why call results do not simply use
                // `fresh_state_for` (ADR 0074).
                self.binders.push((binder.to_string(), "Prop".into()));
                Val::Prop(binder.to_string())
            }
            Ty::Option(element) => {
                self.binders
                    .push((binder.to_string(), lean_option_ty(element, self.classes)));
                Val::Opt(binder.to_string())
            }
            Ty::OptionRaw(_) => {
                self.binders
                    .push((binder.to_string(), "Option Sable.RawPtr".into()));
                Val::Opt(binder.to_string())
            }
            Ty::Class(ci) => {
                let class = self.classes[*ci].clone();
                self.binders
                    .push((binder.to_string(), lean_class_name(&class.name)));
                self.push_class_state_facts(&class, binder);
                self.push_invariant_hyps(&class, binder);
                Val::Obj(binder.to_string())
            }
            Ty::Record(ri) if site == CallResultSite::Function => {
                let record = lean_record_name(&self.records[*ri].name);
                self.binders.push((binder.to_string(), record.clone()));
                self.push_hyp_unique(format!("h_{base}_wf"), format!("{record}.wf {binder}"));
                Val::Record(binder.to_string())
            }
            Ty::Array(_) if site == CallResultSite::Function => {
                // A return names fresh storage, not a mutation of a prior
                // chain, so it gets a representability bound rather than an
                // equality length fact (ADR 0085).
                self.fresh_state_for(ty, binder, &base, LenFact::Bounded)
            }
            Ty::Res(kind) => {
                self.binders
                    .push((binder.to_string(), lean_res_view_ty(*kind, self.records)));
                for (name, prop) in view_wf_hyps(*kind, binder, binder, self.records) {
                    self.push_hyp_unique(name, prop);
                }
                Val::View(binder.to_string())
            }
            Ty::Raw(_) | Ty::RawRecord(_) => {
                self.binders
                    .push((binder.to_string(), "Sable.RawPtr".into()));
                Val::Ptr(binder.to_string())
            }
            Ty::Unit => Val::Unit,
            Ty::Slots(_) => {
                refuse_vc_type(format!(
                    "internal.vcgen.slots_unsupported: owner slots have no call-result state (for `{base}`)"
                ));
                Val::Unit
            }
            returned @ (Ty::Record(_) | Ty::Array(_) | Ty::Borrow(..)) => {
                // Records/arrays arrive here only at a member boundary; a
                // borrow has no result-state story at either boundary. The
                // checker refuses all three first, and this latch keeps the
                // trusted generator fail-closed if that gate drifts.
                refuse_vc_type(format!(
                    "internal.vcgen.call_return_unsupported: `{}` has no call-result state",
                    returned.name()
                ));
                self.binders
                    .push((binder.to_string(), UNSUPPORTED_LEAN_TY.into()));
                Val::Int(binder.to_string())
            }
        }
    }

    /// Validate and visit the checker-authored record for this exact call
    /// boundary.
    ///
    /// The lookup deliberately happens at the boundary where havoc used to
    /// decode the arguments, after nested arguments have been evaluated. This
    /// preserves source evaluation order while making the checker the only
    /// authority for which place a unique borrow names.
    fn checked_call(
        &mut self,
        target: CallTarget,
        span: Span,
        params: &[Param],
        args: &[Expr],
        expected_receiver: Option<(&str, Place, Mutability, Span, Ty)>,
    ) -> (CheckedCallTransition, usize) {
        let key = CallSiteKey {
            owner: self.call_owner.clone(),
            span,
            target,
        };
        let empty = || CheckedCallTransition {
            key: key.clone(),
            receiver: None,
            arguments: Vec::new(),
        };

        let Some(call) = self.ownership.calls.get(&key).cloned() else {
            refuse_vc_type(format!(
                "internal.vcgen.call_transition_missing: no checked effect for {} at {}..{} inside {}",
                key.target.render(),
                span.start,
                span.end,
                self.call_owner.render()
            ));
            return (empty(), 0);
        };

        let mismatch = if call.key != key {
            Some("the stored record carries a different call-site key".to_string())
        } else if args.len() != params.len() {
            Some(format!(
                "the checked signature has {} parameter(s), but the AST has {} argument(s)",
                params.len(),
                args.len()
            ))
        } else if call.arguments.len() != params.len() {
            Some(format!(
                "the signature has {} parameter(s), but the checker supplied {} argument effect(s)",
                params.len(),
                call.arguments.len()
            ))
        } else {
            let receiver_mismatch = match (&call.receiver, &expected_receiver) {
                (None, None) => None,
                (Some(_actual_receiver), None) => {
                    Some("the checker supplied an unexpected method receiver".into())
                }
                (None, Some(_expected_receiver)) => {
                    Some("the checked method call has no receiver effect".into())
                }
                (Some(actual), Some((class, place, mutability, receiver_span, referent))) => {
                    let expected_effect = match mutability {
                        Mutability::Shared => CallEffect::SharedLoan,
                        Mutability::Mut => CallEffect::HavocUniqueBorrow,
                    };
                    if actual.class != *class {
                        Some(format!(
                            "receiver effect names class `{}`, expected `{class}`",
                            actual.class
                        ))
                    } else if actual.transition.place != *place {
                        Some(format!(
                            "receiver effect names `{}`, expected `{}`",
                            actual.transition.place.render(),
                            place.render()
                        ))
                    } else if actual.transition.referent != *referent {
                        Some(format!(
                            "receiver effect has referent `{}`, expected `{}`",
                            actual.transition.referent.name(),
                            referent.name()
                        ))
                    } else if actual.transition.effect != expected_effect {
                        Some("receiver effect has the wrong mutability".into())
                    } else if actual.transition.span != *receiver_span {
                        Some(format!(
                            "receiver effect has span {}..{}, expected {}..{}",
                            actual.transition.span.start,
                            actual.transition.span.end,
                            receiver_span.start,
                            receiver_span.end
                        ))
                    } else {
                        None
                    }
                }
            };
            receiver_mismatch.or_else(|| {
                call.arguments.iter().zip(params.iter().zip(args)).enumerate().find_map(
                |(index, (actual, (parameter, argument)))| {
                    if actual.parameter_index != index {
                        Some(format!(
                            "effect {} names parameter index {}, expected {}",
                            actual.parameter, actual.parameter_index, index
                        ))
                    } else if actual.parameter != parameter.name {
                        Some(format!(
                            "effect at index {index} names parameter `{}`, expected `{}`",
                            actual.parameter, parameter.name
                        ))
                    } else if actual.parameter_ty != parameter.ty {
                        Some(format!(
                            "effect for `{}` has parameter type `{}`, expected `{}`",
                            parameter.name,
                            actual.parameter_ty.name(),
                            parameter.ty.name()
                        ))
                    } else if actual.argument_span != argument.span {
                        Some(format!(
                            "effect for `{}` has argument span {}..{}, expected {}..{}",
                            parameter.name,
                            actual.argument_span.start,
                            actual.argument_span.end,
                            argument.span.start,
                            argument.span.end
                        ))
                    } else {
                        match (&parameter.ty, &actual.effect) {
                            (Ty::Slots(_), CallArgumentEffect::Loan(_))
                            | (Ty::Slots(_), CallArgumentEffect::Value(_)) => Some(format!(
                                "internal.vcgen.slots_unsupported: parameter `{}` has no checked call transition",
                                parameter.name
                            )),
                            (Ty::Borrow(mutability, referent), CallArgumentEffect::Loan(loan)) => {
                                let expected_place = BorrowedPlace::from_expr(argument)
                                    .map(BorrowedPlace::into_place)
                                    .or_else(|| Place::from_value_expr(argument));
                                let expected_effect = match mutability {
                                    Mutability::Shared => CallEffect::SharedLoan,
                                    Mutability::Mut => CallEffect::HavocUniqueBorrow,
                                };
                                if expected_place.as_ref() != Some(&loan.place) {
                                    Some(format!(
                                        "loan for `{}` names a different place",
                                        parameter.name
                                    ))
                                } else if loan.referent != **referent {
                                    Some(format!(
                                        "loan for `{}` has referent `{}`, expected `{}`",
                                        parameter.name,
                                        loan.referent.name(),
                                        referent.name()
                                    ))
                                } else if loan.effect != expected_effect {
                                    Some(format!("loan for `{}` has the wrong mutability", parameter.name))
                                } else if loan.span != argument.span {
                                    Some(format!("loan for `{}` has the wrong source span", parameter.name))
                                } else {
                                    None
                                }
                            }
                            (Ty::Borrow(..), CallArgumentEffect::Value(_value)) => Some(format!(
                                "borrowed parameter `{}` was recorded as a value transfer",
                                parameter.name
                            )),
                            (Ty::Int(_)
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
                            | Ty::Unit, CallArgumentEffect::Loan(_)) => Some(format!(
                                "by-value parameter `{}` was recorded as a loan",
                                parameter.name
                            )),
                            (Ty::Int(_)
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
                            | Ty::Unit, CallArgumentEffect::Value(value)) => {
                                let expected_source = Place::from_value_expr(argument);
                                let expected_kind = if parameter.ty.is_affine() {
                                    if expected_source.is_some() {
                                        ValueTransferKind::Move
                                    } else {
                                        ValueTransferKind::Fresh
                                    }
                                } else {
                                    ValueTransferKind::Copy
                                };
                                if value.value_ty != parameter.ty || value.span != argument.span {
                                    Some(format!(
                                        "value transfer for `{}` disagrees with its checked type or span",
                                        parameter.name
                                    ))
                                } else if value.source != expected_source
                                    || value.kind != expected_kind
                                {
                                    Some(format!(
                                        "value transfer for `{}` names a different source or transfer kind",
                                        parameter.name
                                    ))
                                } else {
                                    None
                                }
                            }
                        }
                    }
                },
            )
            })
        };
        if let Some(detail) = mismatch {
            refuse_vc_type(format!(
                "internal.vcgen.call_transition_mismatch: {} at {}..{} inside {}: {detail}",
                key.target.render(),
                span.start,
                span.end,
                self.call_owner.render()
            ));
            return (empty(), 0);
        }
        self.visited_checked_calls.insert(key.clone());
        let visit = self.checked_call_visits.entry(key).or_default();
        *visit += 1;
        (call, *visit)
    }

    /// Validate the checker-authored ownership transition for one affine
    /// option extraction. The record remains immutable so a symbolic path
    /// split may revisit the source expression; coverage is at least once.
    fn checked_option_take(
        &mut self,
        expression: &Expr,
        option: &str,
        source_span: Span,
    ) -> CheckedOptionTake {
        let key = EffectSiteKey {
            owner: self.call_owner.clone(),
            span: expression.span,
        };
        let expected_source = Place::local(option);
        let expected_payload = expression.ty.clone().unwrap_or(Ty::Unit);
        let fallback = || CheckedOptionTake {
            key: key.clone(),
            source: expected_source.clone(),
            source_span,
            payload: expected_payload.clone(),
        };
        let Some(effect) = self.ownership.option_take(&key).cloned() else {
            refuse_vc_type(format!(
                "internal.vcgen.option_take_missing: no checked ownership effect at {}..{} inside {}",
                key.span.start,
                key.span.end,
                self.call_owner.render()
            ));
            return fallback();
        };
        let mismatch = if effect.key != key {
            Some("the stored record carries a different effect-site key")
        } else if effect.source != expected_source {
            Some("the stored record names a different option place")
        } else if effect.source_span != source_span {
            Some("the stored record carries a different source span")
        } else if effect.payload != expected_payload {
            Some("the stored record carries a different payload type")
        } else {
            None
        };
        if let Some(detail) = mismatch {
            refuse_vc_type(format!(
                "internal.vcgen.option_take_mismatch: checked ownership effect at {}..{} inside {}: {detail}",
                key.span.start,
                key.span.end,
                self.call_owner.render()
            ));
            return fallback();
        }
        self.visited_option_takes.insert(key);
        effect
    }

    /// Resolve one owner-slot operation through both immutable authorities.
    /// Nothing about the symbolic state may change until the typed AST, the
    /// ownership transition, the control action, the put staging transfer,
    /// and every direct trap route agree exactly.
    fn checked_slot_transition_action(
        &mut self,
        scope: ScopeId,
        expression: &Expr,
    ) -> Option<(CheckedSlotTransition, SlotAction, usize)> {
        let ExprKind::SlotOp { op, op_span, args } = &expression.kind else {
            unreachable!("slot transition lookup is called only for slot operations")
        };
        let key = EffectSiteKey {
            owner: self.call_owner.clone(),
            span: expression.span,
        };
        let result_ty = expression.ty.clone().unwrap_or(Ty::Unit);
        let malformed = |detail: &str| {
            refuse_vc_type(format!(
                "internal.vcgen.slot_transition_shape: `{}` at {}..{} inside {} {detail}",
                op.name(),
                expression.span.start,
                expression.span.end,
                self.call_owner.render()
            ));
        };
        if args.len() != op.arity() {
            malformed("has a different arity than its sealed operation");
            return None;
        }

        let (payload, expected_kind) = match op {
            SlotOp::Alloc { elem } => (
                elem.clone(),
                CheckedSlotTransitionKind::Alloc {
                    length_ty: args[0].ty.clone().unwrap_or(Ty::Unit),
                    length_span: args[0].span,
                },
            ),
            SlotOp::Take | SlotOp::Put => {
                let Some(borrowed) = BorrowedPlace::from_expr(&args[0]) else {
                    malformed("does not retain an explicit container borrow");
                    return None;
                };
                if borrowed.mutability() != Mutability::Mut {
                    malformed("does not retain a unique container borrow");
                    return None;
                }
                let Some(Ty::Borrow(Mutability::Mut, referent)) = args[0].ty.as_ref() else {
                    malformed("has no checked unique-borrow container type");
                    return None;
                };
                let Ty::Slots(payload) = referent.as_ref() else {
                    malformed("does not borrow owner-slot storage");
                    return None;
                };
                let container = borrowed.into_place();
                let index_ty = args[1].ty.clone().unwrap_or(Ty::Unit);
                let kind = match op {
                    SlotOp::Take => CheckedSlotTransitionKind::Take {
                        container,
                        container_span: args[0].span,
                        index_ty,
                        index_span: args[1].span,
                    },
                    SlotOp::Put => CheckedSlotTransitionKind::Put {
                        value_transfer: ValueTransferKey {
                            owner: self.call_owner.clone(),
                            span: args[2].span,
                            sink: ValueTransferSink::SlotPut(container.clone()),
                        },
                        container,
                        container_span: args[0].span,
                        index_ty,
                        index_span: args[1].span,
                        value_span: args[2].span,
                    },
                    SlotOp::Alloc { .. } => unreachable!(),
                };
                (payload.as_ref().clone(), kind)
            }
        };
        let expected = CheckedSlotTransition {
            key: key.clone(),
            op_span: *op_span,
            payload,
            result_ty,
            kind: expected_kind,
        };
        let Some(transition) = self.ownership.slot_transition(&key).cloned() else {
            refuse_vc_type(format!(
                "internal.vcgen.slot_transition_missing: no checked `{}` transition at {}..{} inside {}",
                op.name(),
                key.span.start,
                key.span.end,
                self.call_owner.render()
            ));
            return None;
        };
        if transition != expected {
            refuse_vc_type(format!(
                "internal.vcgen.slot_transition_mismatch: checked `{}` transition at {}..{} inside {} disagrees with the typed operation",
                op.name(),
                key.span.start,
                key.span.end,
                self.call_owner.render()
            ));
            return None;
        }

        let action = {
            let plan = self.control_plan()?;
            let action = match plan.slot_action(scope, expression) {
                Ok(action) => action.clone(),
                Err(error) => {
                    refuse_vc_type(format!(
                        "internal.vcgen.slot_action_missing_or_mismatch: {} at {}..{} inside {}",
                        error.message,
                        error.span.start,
                        error.span.end,
                        self.call_owner.render()
                    ));
                    return None;
                }
            };
            let sites = match plan.slot_action_trap_sites(&action) {
                Ok(sites) => sites,
                Err(error) => {
                    refuse_vc_type(format!(
                        "internal.vcgen.slot_action_trap_mismatch: {} at {}..{} inside {}",
                        error.message,
                        error.span.start,
                        error.span.end,
                        self.call_owner.render()
                    ));
                    return None;
                }
            };
            if !self.consume_trap_sites(plan, &sites) {
                return None;
            }
            action
        };
        let common_matches = action.scope() == scope
            && action.span() == expression.span
            && action.effect_key() == &transition.key
            && action.op_span() == transition.op_span
            && action.payload() == &transition.payload
            && action.result_ty() == &transition.result_ty;
        let shape_matches = match (&transition.kind, action.kind()) {
            (
                CheckedSlotTransitionKind::Alloc { length_span, .. },
                SlotActionKind::Alloc {
                    length_span: action_length,
                },
            ) => length_span == action_length,
            (
                CheckedSlotTransitionKind::Take {
                    container,
                    container_span,
                    index_span,
                    ..
                },
                SlotActionKind::Take {
                    container: action_container,
                    container_span: action_container_span,
                    index_span: action_index_span,
                },
            ) => {
                container == action_container
                    && container_span == action_container_span
                    && index_span == action_index_span
            }
            (
                CheckedSlotTransitionKind::Put {
                    container,
                    container_span,
                    index_span,
                    value_span,
                    value_transfer,
                    ..
                },
                SlotActionKind::Put {
                    container: action_container,
                    container_span: action_container_span,
                    index_span: action_index_span,
                    value_span: action_value_span,
                    value_transfer: action_transfer,
                    staging,
                },
            ) => {
                let expected_staging = self.control_plan().and_then(|plan| {
                    plan.compiler_temp(scope, expression.span, CompilerTempKind::SlotPutValue)
                        .ok()
                });
                container == action_container
                    && container_span == action_container_span
                    && index_span == action_index_span
                    && value_span == action_value_span
                    && value_transfer == action_transfer
                    && expected_staging == Some(staging)
            }
            (CheckedSlotTransitionKind::Alloc { .. }, SlotActionKind::Take { .. })
            | (CheckedSlotTransitionKind::Alloc { .. }, SlotActionKind::Put { .. })
            | (CheckedSlotTransitionKind::Take { .. }, SlotActionKind::Alloc { .. })
            | (CheckedSlotTransitionKind::Take { .. }, SlotActionKind::Put { .. })
            | (CheckedSlotTransitionKind::Put { .. }, SlotActionKind::Alloc { .. })
            | (CheckedSlotTransitionKind::Put { .. }, SlotActionKind::Take { .. }) => false,
        };
        if !common_matches || !shape_matches {
            refuse_vc_type(format!(
                "internal.vcgen.slot_action_transition_mismatch: retained `{}` action at {}..{} inside {} disagrees with its checked ownership transition",
                op.name(),
                expression.span.start,
                expression.span.end,
                self.call_owner.render()
            ));
            return None;
        }
        self.visited_slot_transitions.insert(key.clone());
        self.visited_slot_actions.insert((scope, expression.span));
        let visit = self.checked_slot_visits.entry(key).or_default();
        *visit += 1;
        Some((transition, action, *visit))
    }

    /// Validate the checker-authored exposure boundary before opening its
    /// symbolic loan. Exact binder/type matching prevents a forged typed AST
    /// from redirecting the checker's ownership fact to different storage.
    fn checked_exposure(
        &mut self,
        key: &EffectSiteKey,
        owner_place: &Place,
        array_span: Span,
        owner_ty: &Ty,
        mutability: Mutability,
        pointer: &str,
        pointer_span: Span,
        resource: &str,
        resource_span: Span,
    ) -> Option<CheckedExposure> {
        let Some(effect) = self.ownership.exposure(key).cloned() else {
            refuse_vc_type(format!(
                "internal.vcgen.exposure_missing: no checked ownership effect at {}..{} inside {}",
                key.span.start,
                key.span.end,
                self.call_owner.render()
            ));
            return None;
        };
        let mismatch = if effect.key != *key {
            Some("the stored record carries a different effect-site key")
        } else if effect.owner_place != *owner_place {
            Some("the stored record names a different exposed place")
        } else if effect.owner_span != array_span {
            Some("the stored record carries a different owner span")
        } else if effect.owner_ty != *owner_ty {
            Some("the stored record carries a different owner type")
        } else if effect.mutability != mutability {
            Some("the stored record carries a different exposure mutability")
        } else if effect.pointer != pointer || effect.pointer_span != pointer_span {
            Some("the stored record carries a different pointer binding")
        } else if effect.resource != resource || effect.resource_span != resource_span {
            Some("the stored record carries a different resource binding")
        } else {
            None
        };
        if let Some(detail) = mismatch {
            refuse_vc_type(format!(
                "internal.vcgen.exposure_mismatch: checked ownership effect at {}..{} inside {}: {detail}",
                key.span.start,
                key.span.end,
                self.call_owner.render()
            ));
            return None;
        }
        self.visited_exposures.insert(key.clone());
        Some(effect)
    }

    /// Validate and visit one checker-authored sealed-operation boundary.
    /// Child expressions are evaluated before this lookup by each family arm;
    /// the returned record is the only proof-state authority for loan places,
    /// resource roles, and the resolved result shape.
    fn checked_sealed_operation(
        &mut self,
        target: CheckedSealedTarget,
        expression: &Expr,
        arguments: &[Expr],
    ) -> CheckedSealedOperation {
        let key = EffectSiteKey {
            owner: self.call_owner.clone(),
            span: expression.span,
        };
        let expected_result = expression.ty.clone().unwrap_or(Ty::Unit);
        let fallback = || CheckedSealedOperation {
            key: key.clone(),
            target,
            arguments: arguments
                .iter()
                .enumerate()
                .map(|(index, argument)| {
                    let argument_ty = argument.ty.clone().unwrap_or(Ty::Unit);
                    CheckedSealedArgument {
                        index,
                        argument_ty: argument_ty.clone(),
                        argument_span: argument.span,
                        // A missing/mismatched checked record has already
                        // latched a fatal refusal. Keep walking with an inert
                        // placeholder so downstream arms cannot accidentally
                        // recover ownership facts from source syntax.
                        effect: CallArgumentEffect::Value(ValueTransfer {
                            source: None,
                            value_ty: argument_ty,
                            kind: ValueTransferKind::Copy,
                            carried_obligation: false,
                            branded: false,
                            span: argument.span,
                        }),
                    }
                })
                .collect(),
            result_ty: expected_result.clone(),
        };
        let Some(operation) = self.ownership.sealed_operation(&key).cloned() else {
            refuse_vc_type(format!(
                "internal.vcgen.sealed_transition_missing: no checked `{}` effect at {}..{} inside {}",
                target.render(),
                key.span.start,
                key.span.end,
                self.call_owner.render()
            ));
            return fallback();
        };
        let mismatch = if operation.key != key {
            Some("the stored record carries a different effect-site key".to_string())
        } else if operation.target != target {
            Some(format!(
                "the stored target is `{}`, expected `{}`",
                operation.target.render(),
                target.render()
            ))
        } else if operation.result_ty != expected_result {
            Some("the stored record carries a different result type".to_string())
        } else if operation.arguments.len() != arguments.len() {
            Some(format!(
                "the checker supplied {} argument effect(s), but the AST has {} argument(s)",
                operation.arguments.len(),
                arguments.len()
            ))
        } else {
            operation
                .arguments
                .iter()
                .zip(arguments)
                .enumerate()
                .find_map(|(index, (actual, argument))| {
                    let expected_ty = argument.ty.clone().unwrap_or(Ty::Unit);
                    if actual.index != index {
                        Some(format!(
                            "effect at position {index} names argument index {}",
                            actual.index
                        ))
                    } else if actual.argument_ty != expected_ty {
                        Some(format!("argument {index} has a different checked type"))
                    } else if actual.argument_span != argument.span {
                        Some(format!("argument {index} has a different checked span"))
                    } else {
                        match (&expected_ty, &actual.effect) {
                            (Ty::Slots(_), CallArgumentEffect::Loan(_))
                            | (Ty::Slots(_), CallArgumentEffect::Value(_)) => Some(format!(
                                "internal.vcgen.slots_unsupported: sealed argument {index} has no transition"
                            )),
                            (Ty::Borrow(mutability, referent), CallArgumentEffect::Loan(loan)) => {
                                let expected_place = BorrowedPlace::from_expr(argument)
                                    .map(BorrowedPlace::into_place);
                                let expected_effect = match mutability {
                                    Mutability::Shared => CallEffect::SharedLoan,
                                    Mutability::Mut => CallEffect::HavocUniqueBorrow,
                                };
                                if expected_place.as_ref() != Some(&loan.place) {
                                    Some(format!("loan argument {index} names a different place"))
                                } else if loan.referent != **referent {
                                    Some(format!(
                                        "loan argument {index} has a different referent type"
                                    ))
                                } else if loan.effect != expected_effect {
                                    Some(format!("loan argument {index} has the wrong mutability"))
                                } else if loan.span != argument.span {
                                    Some(format!("loan argument {index} has a different span"))
                                } else {
                                    None
                                }
                            }
                            (Ty::Borrow(..), CallArgumentEffect::Value(_value)) => Some(format!(
                                "borrowed argument {index} was recorded as a value transfer"
                            )),
                            (
                                Ty::Int(_)
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
                                | Ty::Unit,
                                CallArgumentEffect::Loan(_),
                            ) => Some(format!("by-value argument {index} was recorded as a loan")),
                            (
                                Ty::Int(_)
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
                                | Ty::Unit,
                                CallArgumentEffect::Value(value),
                            ) => {
                                let expected_source = Place::from_value_expr(argument);
                                let expected_kind = if expected_ty.is_affine() {
                                    if expected_source.is_some() {
                                        ValueTransferKind::Move
                                    } else {
                                        ValueTransferKind::Fresh
                                    }
                                } else {
                                    ValueTransferKind::Copy
                                };
                                if value.value_ty != expected_ty || value.span != argument.span {
                                    Some(format!(
                                        "value argument {index} has a different type or span"
                                    ))
                                } else if value.source != expected_source
                                    || value.kind != expected_kind
                                {
                                    Some(format!(
                                        "value argument {index} has a different transfer identity"
                                    ))
                                } else {
                                    None
                                }
                            }
                        }
                    }
                })
        };
        if let Some(detail) = mismatch {
            refuse_vc_type(format!(
                "internal.vcgen.sealed_transition_mismatch: checked `{}` effect at {}..{} inside {}: {detail}",
                target.render(),
                key.span.start,
                key.span.end,
                self.call_owner.render()
            ));
            return fallback();
        }
        self.visited_sealed_operations.insert(key);
        operation
    }

    /// Exact immutable lookup of the mutation set the checker computed for
    /// one loop transition. Symbolic revisits are allowed, but every checked
    /// loop in a verified body must be reached at least once.
    fn checked_loop_effects(
        &mut self,
        key: &EffectSiteKey,
        condition_span: Span,
    ) -> Option<CheckedLoopEffects> {
        let Some(effects) = self.ownership.loop_effects(key).cloned() else {
            refuse_vc_type(format!(
                "internal.vcgen.loop_effect_missing: no checked loop effect at {}..{} inside {}",
                key.span.start,
                key.span.end,
                self.call_owner.render()
            ));
            return None;
        };
        for mutation in &effects.mutations {
            let CheckedMutation::Slot {
                key: slot_key,
                operation,
                container,
                payload,
            } = mutation
            else {
                continue;
            };
            let Some(transition) = self.ownership.slot_transition(slot_key) else {
                refuse_vc_type(format!(
                    "internal.vcgen.loop_slot_transition_missing: loop effect at {}..{} inside {} references no checked slot transition at {}..{}",
                    key.span.start,
                    key.span.end,
                    self.call_owner.render(),
                    slot_key.span.start,
                    slot_key.span.end
                ));
                return None;
            };
            let kind_matches = match (operation, &transition.kind) {
                (
                    CheckedSlotMutationKind::Take,
                    CheckedSlotTransitionKind::Take {
                        container: checked_container,
                        ..
                    },
                ) => checked_container == container && transition.result_ty == *payload,
                (
                    CheckedSlotMutationKind::Put,
                    CheckedSlotTransitionKind::Put {
                        container: checked_container,
                        ..
                    },
                ) => checked_container == container && transition.result_ty == Ty::Unit,
                (CheckedSlotMutationKind::Take, CheckedSlotTransitionKind::Alloc { .. })
                | (CheckedSlotMutationKind::Take, CheckedSlotTransitionKind::Put { .. })
                | (CheckedSlotMutationKind::Put, CheckedSlotTransitionKind::Alloc { .. })
                | (CheckedSlotMutationKind::Put, CheckedSlotTransitionKind::Take { .. }) => false,
            };
            if slot_key.owner != self.call_owner
                || transition.key != *slot_key
                || transition.payload != *payload
                || !kind_matches
            {
                refuse_vc_type(format!(
                    "internal.vcgen.loop_slot_transition_mismatch: loop effect at {}..{} inside {} disagrees with referenced slot transition at {}..{}",
                    key.span.start,
                    key.span.end,
                    self.call_owner.render(),
                    slot_key.span.start,
                    slot_key.span.end
                ));
                return None;
            }
        }
        let mismatch = if effects.key != *key {
            Some("the stored record carries a different effect-site key")
        } else if effects.condition_span != condition_span {
            Some("the stored record carries a different condition span")
        } else if effects.mutations.iter().any(|mutation| match mutation {
            CheckedMutation::UniqueLoan(transition) => {
                transition.effect != CallEffect::HavocUniqueBorrow
            }
            CheckedMutation::DirectWrite { .. }
            | CheckedMutation::OptionTake { .. }
            | CheckedMutation::Slot { .. }
            | CheckedMutation::ExposureRebuild { .. } => false,
        }) {
            Some("the stored mutation set contains a non-unique loan")
        } else {
            None
        };
        if let Some(detail) = mismatch {
            refuse_vc_type(format!(
                "internal.vcgen.loop_effect_mismatch: checked loop effect at {}..{} inside {}: {detail}",
                key.span.start,
                key.span.end,
                self.call_owner.render()
            ));
            return None;
        }
        self.visited_loops.insert(key.clone());
        Some(effects)
    }

    /// Consume one retained local replacement action before evaluating its
    /// RHS. Symbolic destruction has no separate heap effect in the VC model,
    /// but it is not omitted structurally: the exact old drop candidate and
    /// staging temporary are authenticated here before the later environment
    /// update forgets the previous symbolic value.
    fn checked_assignment_action(
        &mut self,
        scope: ScopeId,
        span: Span,
        destination: &Place,
        value: &Expr,
    ) -> Option<AssignmentAction> {
        let action = {
            let plan = self.control_plan()?;
            let action = match plan.assignment(scope, span, destination) {
                Ok(action) => action,
                Err(error) => {
                    refuse_vc_type(format!(
                        "internal.vcgen.assignment_action_missing: {} at {}..{} inside {}",
                        error.message,
                        error.span.start,
                        error.span.end,
                        self.call_owner.render()
                    ));
                    return None;
                }
            };
            let Some(value_ty) = value.ty.as_ref() else {
                refuse_vc_type(format!(
                    "internal.vcgen.assignment_action_mismatch: assignment at {}..{} inside {} has no checked RHS type",
                    span.start,
                    span.end,
                    self.call_owner.render()
                ));
                return None;
            };
            let expected_previous = plan
                .candidate_for_place(destination)
                .map(|candidate| candidate.id());
            let expected_key = ValueTransferKey {
                owner: self.call_owner.clone(),
                span: value.span,
                sink: ValueTransferSink::Assignment(destination.clone()),
            };
            let expected_staging = match expected_previous {
                Some(_) => {
                    let temporary = match plan.compiler_temp(
                        scope,
                        span,
                        CompilerTempKind::AssignmentValue,
                    ) {
                        Ok(temporary) => temporary.clone(),
                        Err(error) => {
                            refuse_vc_type(format!(
                                "internal.vcgen.assignment_action_mismatch: {} at {}..{} inside {}",
                                error.message,
                                error.span.start,
                                error.span.end,
                                self.call_owner.render()
                            ));
                            return None;
                        }
                    };
                    AssignmentStaging::Temporary(temporary)
                }
                None => AssignmentStaging::Direct,
            };
            let binding_ty = self.var_tys.get(destination.root());
            if action.scope() != scope
                || action.span() != span
                || action.destination() != destination
                || action.ty() != value_ty
                || binding_ty != Some(action.ty())
                || action.transfer_key() != &expected_key
                || action.previous() != expected_previous
                || action.staging() != &expected_staging
            {
                refuse_vc_type(format!(
                    "internal.vcgen.assignment_action_mismatch: retained assignment to `{}` at {}..{} inside {} disagrees with its scope, type, drop candidate, or staging temporary",
                    destination.render(),
                    span.start,
                    span.end,
                    self.call_owner.render()
                ));
                return None;
            }
            if let Some(previous) = action.previous() {
                let candidate = plan.candidate(previous);
                if candidate.place() != destination || candidate.ty() != action.ty() {
                    refuse_vc_type(format!(
                        "internal.vcgen.assignment_action_mismatch: retained assignment to `{}` inside {} names a different cleanup candidate",
                        destination.render(),
                        self.call_owner.render()
                    ));
                    return None;
                }
            }
            action.clone()
        };
        self.visited_assignments.insert((scope, span));
        Some(action)
    }

    /// Consume one retained field replacement/install action and its exact
    /// checker-authored ownership handoff. Constructor first-install and
    /// method replacement deliberately share this structural rule; dynamic
    /// field liveness decides whether the authenticated conditional drop has
    /// an old value to destroy.
    fn checked_field_assignment_action(
        &mut self,
        scope: ScopeId,
        span: Span,
        destination: &Place,
        value: &Expr,
    ) -> Option<FieldAssignmentAction> {
        let action = {
            let plan = self.control_plan()?;
            let action = match plan.field_assignment(scope, span, destination, value) {
                Ok(action) => action,
                Err(error) => {
                    refuse_vc_type(format!(
                        "internal.vcgen.field_assignment_action_missing: {} at {}..{} inside {}",
                        error.message,
                        error.span.start,
                        error.span.end,
                        self.call_owner.render()
                    ));
                    return None;
                }
            };
            let Some(value_ty) = value.ty.as_ref() else {
                refuse_vc_type(format!(
                    "internal.vcgen.field_assignment_action_mismatch: field assignment at {}..{} inside {} has no checked RHS type",
                    span.start,
                    span.end,
                    self.call_owner.render()
                ));
                return None;
            };
            let expected_key = ValueTransferKey {
                owner: self.call_owner.clone(),
                span: value.span,
                sink: ValueTransferSink::FieldAssignment(destination.clone()),
            };
            let cleanup_bearing = matches!(value_ty, Ty::Class(_) | Ty::Array(_) | Ty::Slots(_))
                || value_ty.is_affine_option();
            let expected_staging = if cleanup_bearing {
                let temporary = match plan.compiler_temp(
                    scope,
                    span,
                    CompilerTempKind::FieldAssignmentValue,
                ) {
                    Ok(temporary) => temporary.clone(),
                    Err(error) => {
                        refuse_vc_type(format!(
                            "internal.vcgen.field_assignment_action_mismatch: {} at {}..{} inside {}",
                            error.message,
                            error.span.start,
                            error.span.end,
                            self.call_owner.render()
                        ));
                        return None;
                    }
                };
                AssignmentStaging::Temporary(temporary)
            } else {
                AssignmentStaging::Direct
            };
            let expected_class = if let Ty::Class(class) = value_ty {
                Some(*class)
            } else {
                None
            };
            let retained_class = action.drop_action().and_then(|drop| match drop.recipe() {
                ValueDropRecipe::DropClass(class) => Some(class.class()),
                ValueDropRecipe::ReleaseArray { .. }
                | ValueDropRecipe::ReleaseSlots { .. }
                | ValueDropRecipe::DropPresent(_) => None,
            });
            let bad_terminal = action
                .drop_action()
                .is_some_and(|drop| match drop.recipe() {
                    ValueDropRecipe::DropClass(class) => {
                        class.terminal_trap_route() != &plan.trap_route()
                    }
                    ValueDropRecipe::ReleaseArray { .. }
                    | ValueDropRecipe::ReleaseSlots { .. }
                    | ValueDropRecipe::DropPresent(_) => false,
                });
            if action.scope() != scope
                || action.span() != span
                || action.destination() != destination
                || action.ty() != value_ty
                || action.transfer_key() != &expected_key
                || action.drop_if_present() != cleanup_bearing
                || action.staging() != &expected_staging
                || retained_class != expected_class
                || bad_terminal
            {
                refuse_vc_type(format!(
                    "internal.vcgen.field_assignment_action_mismatch: retained field assignment to `{}` at {}..{} inside {} disagrees with its type, transfer, staging, conditional drop, or terminal no-unwind class action",
                    destination.render(),
                    span.start,
                    span.end,
                    self.call_owner.render()
                ));
                return None;
            }
            action.clone()
        };
        self.visited_field_assignments.insert((scope, span));
        Some(action)
    }

    /// Consume the mandatory statement-end destruction of one discarded
    /// fresh class result. The destruction itself is a proof no-op: a fresh
    /// result has no symbolic place to update, and class destruction has no
    /// normal-return state. Its type, compiler temporary, transfer identity,
    /// concrete class, and terminal no-unwind route are nevertheless exact
    /// retained inputs, validated before expression evaluation.
    fn checked_temporary_drop_action(
        &mut self,
        scope: ScopeId,
        expression: &Expr,
    ) -> Option<TemporaryDropAction> {
        let span = expression.span;
        let action = {
            let plan = self.control_plan()?;
            let action = match plan.temporary_drop(scope, expression) {
                Ok(action) => action,
                Err(error) => {
                    refuse_vc_type(format!(
                        "internal.vcgen.temporary_drop_action_missing: {} at {}..{} inside {}",
                        error.message,
                        error.span.start,
                        error.span.end,
                        self.call_owner.render()
                    ));
                    return None;
                }
            };
            let Some(value_ty) = expression.ty.as_ref() else {
                refuse_vc_type(format!(
                    "internal.vcgen.temporary_drop_action_mismatch: discarded value at {}..{} inside {} has no checked type",
                    span.start,
                    span.end,
                    self.call_owner.render()
                ));
                return None;
            };
            let expected_key = ValueTransferKey {
                owner: self.call_owner.clone(),
                span,
                sink: ValueTransferSink::DiscardTemporary,
            };
            let expected_temporary =
                match plan.compiler_temp(scope, span, CompilerTempKind::DiscardedClassValue) {
                    Ok(temporary) => temporary,
                    Err(error) => {
                        refuse_vc_type(format!(
                            "internal.vcgen.temporary_drop_action_mismatch: {} at {}..{} inside {}",
                            error.message,
                            error.span.start,
                            error.span.end,
                            self.call_owner.render()
                        ));
                        return None;
                    }
                };
            let expected_class = if let Ty::Class(class) = value_ty {
                Some(*class)
            } else {
                None
            };
            let retained_class = match action.drop_action().recipe() {
                ValueDropRecipe::DropClass(class) => Some(class),
                ValueDropRecipe::ReleaseArray { .. }
                | ValueDropRecipe::ReleaseSlots { .. }
                | ValueDropRecipe::DropPresent(_) => None,
            };
            if action.scope() != scope
                || action.span() != span
                || action.ty() != value_ty
                || action.transfer_key() != &expected_key
                || action.temporary() != expected_temporary
                || retained_class.map(|class| class.class()) != expected_class
                || retained_class
                    .is_none_or(|class| class.terminal_trap_route() != &plan.trap_route())
            {
                refuse_vc_type(format!(
                    "internal.vcgen.temporary_drop_action_mismatch: retained discarded value at {}..{} inside {} disagrees with its class type, transfer, compiler temporary, or terminal no-unwind action",
                    span.start,
                    span.end,
                    self.call_owner.render()
                ));
                return None;
            }
            action.clone()
        };
        self.visited_temporary_drops.insert((scope, span));
        Some(action)
    }

    /// Validate a checker-authored value transfer at a non-call sink. The
    /// flow-sensitive obligation/brand payload is intentionally consumed as
    /// data rather than recomputed; only structural identity can be checked
    /// against the typed expression here.
    fn checked_value_transfer(
        &mut self,
        expression: &Expr,
        sink: ValueTransferSink,
    ) -> ValueTransfer {
        let key = ValueTransferKey {
            owner: self.call_owner.clone(),
            span: expression.span,
            sink,
        };
        self.checked_value_transfer_key(expression, &key)
    }

    /// Consume a transfer through a cleanup action's retained identity. This
    /// prevents the VC path from independently selecting a field/discard sink
    /// after the control plan has already sealed that semantic boundary.
    fn checked_value_transfer_key(
        &mut self,
        expression: &Expr,
        key: &ValueTransferKey,
    ) -> ValueTransfer {
        let expected_ty = expression.ty.clone().unwrap_or(Ty::Unit);
        let expected_source = Place::from_value_expr(expression);
        let expected_kind = if expected_ty.is_affine() {
            if expected_source.is_some() {
                ValueTransferKind::Move
            } else {
                ValueTransferKind::Fresh
            }
        } else {
            ValueTransferKind::Copy
        };
        let fallback = || ValueTransfer {
            source: expected_source.clone(),
            value_ty: expected_ty.clone(),
            kind: expected_kind,
            carried_obligation: false,
            branded: false,
            span: expression.span,
        };
        if key.owner != self.call_owner || key.span != expression.span {
            refuse_vc_type(format!(
                "internal.vcgen.value_transfer_key_mismatch: retained transfer for {} at {}..{} does not identify this expression inside {}",
                key.sink.render(),
                key.span.start,
                key.span.end,
                self.call_owner.render()
            ));
            return fallback();
        }
        let Some(transfer) = self.ownership.value_transfer(key).cloned() else {
            refuse_vc_type(format!(
                "internal.vcgen.value_transfer_missing: no checked value transfer for {} at {}..{} inside {}",
                key.sink.render(),
                key.span.start,
                key.span.end,
                self.call_owner.render()
            ));
            return fallback();
        };
        if transfer.value_ty != expected_ty
            || transfer.source != expected_source
            || transfer.kind != expected_kind
            || transfer.span != expression.span
        {
            refuse_vc_type(format!(
                "internal.vcgen.value_transfer_mismatch: checked value transfer for {} at {}..{} inside {} disagrees with the typed expression",
                key.sink.render(),
                key.span.start,
                key.span.end,
                self.call_owner.render()
            ));
            return fallback();
        }
        self.visited_value_transfers.insert(key.clone());
        transfer
    }

    /// Every checker record for a verified callable must be visited by at
    /// least one path in the corresponding symbolic walk. Tests, externs, and
    /// proof-reuse bodies do not construct a `Generator`, so their
    /// intentionally skipped records are outside this per-callable assertion.
    fn finish_checked_ownership(&self) {
        if let Some((key, _)) = self
            .ownership
            .calls
            .for_owner(&self.call_owner)
            .filter(|(key, _)| !self.visited_checked_calls.contains(*key))
            .min_by_key(|(key, _)| (key.span.start, key.span.end, key.target.render()))
        {
            refuse_vc_type(format!(
                "internal.vcgen.call_transition_unvisited: checked effect for {} at {}..{} inside {} was not visited",
                key.target.render(),
                key.span.start,
                key.span.end,
                self.call_owner.render()
            ));
        }
        if let Some((key, _)) = self
            .ownership
            .option_takes_for_owner(&self.call_owner)
            .filter(|(key, _)| !self.visited_option_takes.contains(*key))
            .min_by_key(|(key, _)| (key.span.start, key.span.end))
        {
            refuse_vc_type(format!(
                "internal.vcgen.option_take_unvisited: checked ownership effect at {}..{} inside {} was not visited",
                key.span.start,
                key.span.end,
                self.call_owner.render()
            ));
        }
        if let Some((key, _)) = self
            .ownership
            .slot_transitions_for_owner(&self.call_owner)
            .filter(|(key, _)| !self.visited_slot_transitions.contains(*key))
            .min_by_key(|(key, _)| (key.span.start, key.span.end))
        {
            refuse_vc_type(format!(
                "internal.vcgen.slot_transition_unvisited: checked ownership transition at {}..{} inside {} was not visited",
                key.span.start,
                key.span.end,
                self.call_owner.render()
            ));
        }
        if let Some((key, _)) = self
            .ownership
            .exposures_for_owner(&self.call_owner)
            .filter(|(key, _)| !self.visited_exposures.contains(*key))
            .min_by_key(|(key, _)| (key.span.start, key.span.end))
        {
            refuse_vc_type(format!(
                "internal.vcgen.exposure_unvisited: checked ownership effect at {}..{} inside {} was not visited",
                key.span.start,
                key.span.end,
                self.call_owner.render()
            ));
        }
        if let Some((key, operation)) = self
            .ownership
            .sealed_operations_for_owner(&self.call_owner)
            .filter(|(key, _)| !self.visited_sealed_operations.contains(*key))
            .min_by_key(|(key, operation)| {
                (key.span.start, key.span.end, operation.target.render())
            })
        {
            refuse_vc_type(format!(
                "internal.vcgen.sealed_transition_unvisited: checked `{}` effect at {}..{} inside {} was not visited",
                operation.target.render(),
                key.span.start,
                key.span.end,
                self.call_owner.render()
            ));
        }
        if let Some((key, _)) = self
            .ownership
            .loops_for_owner(&self.call_owner)
            .filter(|(key, _)| !self.visited_loops.contains(*key))
            .min_by_key(|(key, _)| (key.span.start, key.span.end))
        {
            refuse_vc_type(format!(
                "internal.vcgen.loop_effect_unvisited: checked loop effect at {}..{} inside {} was not visited",
                key.span.start,
                key.span.end,
                self.call_owner.render()
            ));
        }
        if let Some((key, _)) = self
            .ownership
            .value_transfers_for_owner(&self.call_owner)
            .filter(|(key, _)| !self.visited_value_transfers.contains(*key))
            .min_by_key(|(key, _)| (key.span.start, key.span.end, key.sink.render()))
        {
            refuse_vc_type(format!(
                "internal.vcgen.value_transfer_unvisited: checked value transfer for {} at {}..{} inside {} was not visited",
                key.sink.render(),
                key.span.start,
                key.span.end,
                self.call_owner.render()
            ));
        }
        if let Some(control) = self.control {
            let plan = control.plan();
            if let Some(action) = plan
                .slot_actions()
                .filter(|action| {
                    !self
                        .visited_slot_actions
                        .contains(&(action.scope(), action.span()))
                })
                .min_by_key(|action| (action.span().start, action.span().end))
            {
                refuse_vc_type(format!(
                    "internal.vcgen.slot_action_unvisited: retained slot action at {}..{} inside {} was not visited",
                    action.span().start,
                    action.span().end,
                    self.call_owner.render()
                ));
            }
            if let Some(action) = plan
                .assignments()
                .filter(|action| {
                    !self
                        .visited_assignments
                        .contains(&(action.scope(), action.span()))
                })
                .min_by_key(|action| {
                    (
                        action.span().start,
                        action.span().end,
                        action.destination().render(),
                    )
                })
            {
                refuse_vc_type(format!(
                    "internal.vcgen.assignment_action_unvisited: retained assignment to `{}` at {}..{} inside {} was not visited",
                    action.destination().render(),
                    action.span().start,
                    action.span().end,
                    self.call_owner.render()
                ));
            }
            if let Some(action) = plan
                .field_assignments()
                .filter(|action| {
                    !self
                        .visited_field_assignments
                        .contains(&(action.scope(), action.span()))
                })
                .min_by_key(|action| {
                    (
                        action.span().start,
                        action.span().end,
                        action.destination().render(),
                    )
                })
            {
                refuse_vc_type(format!(
                    "internal.vcgen.field_assignment_action_unvisited: retained field assignment to `{}` at {}..{} inside {} was not visited",
                    action.destination().render(),
                    action.span().start,
                    action.span().end,
                    self.call_owner.render()
                ));
            }
            if let Some(action) = plan
                .temporary_drops()
                .filter(|action| {
                    !self
                        .visited_temporary_drops
                        .contains(&(action.scope(), action.span()))
                })
                .min_by_key(|action| (action.span().start, action.span().end))
            {
                refuse_vc_type(format!(
                    "internal.vcgen.temporary_drop_action_unvisited: retained discarded class temporary at {}..{} inside {} was not visited",
                    action.span().start,
                    action.span().end,
                    self.call_owner.render()
                ));
            }
        }
    }

    /// The exact checker-sealed control plan for this generator. Production
    /// construction always supplies one; keeping this as a fallible lookup
    /// makes forged unit fixtures latch the same named refusal instead of
    /// silently rebuilding scope identity from the AST.
    fn control_plan(&self) -> Option<&BodyPlan> {
        let Some(control) = self.control else {
            refuse_vc_type(format!(
                "internal.vcgen.control_plan_missing: no retained checked plan for {}",
                self.call_owner.render()
            ));
            return None;
        };
        if control.owner() != &self.call_owner || control.declaration_span() != self.f.span {
            refuse_vc_type(format!(
                "internal.vcgen.control_plan_mismatch: retained plan for {} at {}..{} does not match {} at {}..{}",
                control.owner().render(),
                control.declaration_span().start,
                control.declaration_span().end,
                self.call_owner.render(),
                self.f.span.start,
                self.f.span.end
            ));
            return None;
        }
        Some(control.plan())
    }

    /// Reconcile the whole retained callable before symbolic execution can
    /// add a binder, hypothesis, or obligation. Per-node lookups below still
    /// consume each direct trap edge when the corresponding source node is
    /// reached, including repeated visits along distinct symbolic paths.
    fn checked_body_scope(&self) -> Option<ScopeId> {
        let plan = self.control_plan()?;
        if let Err(error) = plan.validate_callable(&self.f.params, &self.f.body) {
            refuse_vc_type(format!(
                "internal.vcgen.control_plan_shape_mismatch: {} at {}..{} inside {}",
                error.message,
                error.span.start,
                error.span.end,
                self.call_owner.render()
            ));
            return None;
        }
        let block = plan.body_block();
        if block.scope() != plan.body_scope() {
            refuse_vc_type(format!(
                "internal.vcgen.control_plan_body_edge_mismatch: retained root block inside {} does not use the checked body scope",
                self.call_owner.render()
            ));
            return None;
        }
        Some(block.scope())
    }

    /// Consume the exact checker-sealed trap sites for one reached source
    /// expression. The shared plan owns classification and structural keys;
    /// VC generation only checks that every retained edge is the canonical
    /// empty no-unwind route. Some operational traps (for example allocator
    /// failure or a callee trapping) have no proof obligation on the normal
    /// continuation, but their source edge is still consumed here.
    fn consume_expression_trap_sites(&self, scope: ScopeId, expression: &Expr) -> bool {
        let plan = match self.control_plan() {
            Some(plan) => plan,
            None => return false,
        };
        let sites = match plan.expression_trap_sites(scope, expression) {
            Ok(sites) => sites,
            Err(error) => {
                refuse_vc_type(format!(
                    "internal.vcgen.control_plan_trap_site_missing: {} at {}..{} inside {}",
                    error.message,
                    error.span.start,
                    error.span.end,
                    self.call_owner.render()
                ));
                return false;
            }
        };
        self.consume_trap_sites(plan, &sites)
    }

    /// Statement sites are direct only. Child expressions and structured
    /// bodies consume their own sites upon entry, preserving short-circuit
    /// and branch evaluation order instead of pre-walking descendants.
    fn consume_statement_trap_sites(&self, scope: ScopeId, statement: &Stmt) -> bool {
        let plan = match self.control_plan() {
            Some(plan) => plan,
            None => return false,
        };
        let sites = match plan.statement_trap_sites(scope, statement) {
            Ok(sites) => sites,
            Err(error) => {
                refuse_vc_type(format!(
                    "internal.vcgen.control_plan_trap_site_missing: {} at {}..{} inside {}",
                    error.message,
                    error.span.start,
                    error.span.end,
                    self.call_owner.render()
                ));
                return false;
            }
        };
        self.consume_trap_sites(plan, &sites)
    }

    fn consume_trap_sites(&self, plan: &BodyPlan, sites: &[&TrapSite]) -> bool {
        // A source trap identity is not an obligation identity. The normal
        // path may need zero obligations (allocator/callee failure), one
        // guard, or several clauses (exposure close and loop reasoning).
        // What this handoff seals uniformly is the abort edge: none of those
        // failures may acquire lexical cleanup or be mistaken for a join.
        let canonical = plan.trap_route();
        if let Some(site) = sites.iter().find(|site| site.route() != &canonical) {
            refuse_vc_type(format!(
                "internal.vcgen.control_plan_trap_route_mismatch: trap site at {}..{} inside {} does not use the canonical empty no-unwind route",
                site.span().start,
                site.span().end,
                self.call_owner.render()
            ));
            return false;
        }
        true
    }

    fn checked_return_routes(
        &self,
        span: Span,
        scope: ScopeId,
        has_value: bool,
    ) -> Option<ReturnRoutes> {
        let plan = self.control_plan()?;
        let routes = match plan.explicit_return(span, scope) {
            Ok(routes) => routes,
            Err(error) => {
                refuse_vc_type(format!(
                    "internal.vcgen.control_plan_return_missing: {} at {}..{} inside {}",
                    error.message,
                    error.span.start,
                    error.span.end,
                    self.call_owner.render()
                ));
                return None;
            }
        };
        if routes.result_slot().is_some() != has_value {
            refuse_vc_type(format!(
                "internal.vcgen.control_plan_return_mismatch: return at {}..{} inside {} changed valued/unit shape after checking",
                span.start,
                span.end,
                self.call_owner.render()
            ));
            return None;
        }
        Some(routes)
    }

    /// Consume one normalized lexical edge. VC generation has no runtime
    /// destructor to execute, but it does consume the exact drop identities
    /// and ordering before removing every source binding whose lifetime ends
    /// on the edge. Historical Lean binders and hypotheses deliberately stay:
    /// they are pure facts that may witness an outer value, while the removed
    /// source maps ensure later clauses cannot name dead storage.
    fn apply_control_route(&mut self, route: &ExitRoute, expected: ExitKind) -> bool {
        if route.kind() != expected {
            refuse_vc_type(format!(
                "internal.vcgen.control_plan_route_mismatch: {} route inside {} was expected to be {expected:?}, found {:?}",
                self.fname,
                self.call_owner.render(),
                route.kind()
            ));
            return false;
        }

        // Validate the entire edge before mutating any proof state. A future
        // plan extension that accidentally puts a projection here must fail
        // atomically rather than partly clearing the environment.
        if let Some(place) = route.clears().iter().find(|place| !place.is_root()) {
            refuse_vc_type(format!(
                "internal.vcgen.control_plan_place_unsupported: lexical route inside {} contains projected clear `{}`",
                self.call_owner.render(),
                place.render()
            ));
            return false;
        }

        let drop_places = {
            let Some(plan) = self.control_plan() else {
                return false;
            };
            route
                .drops()
                .iter()
                .map(|drop| plan.candidate(*drop).place().clone())
                .collect::<Vec<_>>()
        };
        if let Some(place) = drop_places
            .iter()
            .find(|place| !place.is_root() || !route.clears().contains(place))
        {
            refuse_vc_type(format!(
                "internal.vcgen.control_plan_drop_mismatch: lexical route inside {} drops `{}` without the matching root clear",
                self.call_owner.render(),
                place.render()
            ));
            return false;
        }

        for place in route.clears() {
            let name = place.root();
            self.env.remove(name);
            self.var_tys.remove(name);
            self.entry_states.remove(name);
        }
        true
    }

    fn apply_scope_route(&mut self, route: &ExitRoute, scope: ScopeId, expected: ExitKind) -> bool {
        if route.scopes() != [scope] {
            refuse_vc_type(format!(
                "internal.vcgen.control_plan_active_scope_mismatch: lexical route inside {} does not exit the active checked scope",
                self.call_owner.render()
            ));
            return false;
        }
        self.apply_control_route(route, expected)
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
    /// A `&mut [T]` argument is the same move again with a sequence: the
    /// callee may have stored into it arbitrarily (within its posts), and
    /// omitting this havoc asserts posts over the pre-call state and yields
    /// inconsistent hypotheses. Length and element ranges are preserved by
    /// construction (stores are the only mutation); the callee's posts,
    /// substituted over the fresh symbol, say the rest.
    ///
    /// Returns param name → post-call state, for the callee's posts.
    fn havoc_mut_borrow_args(
        &mut self,
        checked_call: &CheckedCallTransition,
        symbolic_visit: usize,
    ) -> Vec<(String, String)> {
        // The borrowed *place*, which may be a field: `&mut self.w` names
        // `w` inside `self`, so the fresh state has to be written back into
        // the object rather than replacing it. Getting this wrong replaced
        // `self` with a view and lost the whole self-chain.
        //
        let mut out = Vec::new();
        for argument in &checked_call.arguments {
            let CallArgumentEffect::Loan(transition) = &argument.effect else {
                continue;
            };
            match transition.effect {
                CallEffect::SharedLoan => continue,
                CallEffect::HavocUniqueBorrow => {}
            }
            let pname = argument.parameter.clone();
            let transition = transition.clone();
            let referent = transition.referent.clone();
            let place = transition.place.clone();
            let array = place.root().to_string();
            let hint = place.binder_hint();
            let field = if place.is_root() {
                None
            } else if let Some(field) = place.direct_field() {
                Some(field.to_string())
            } else {
                refuse_vc_type(format!(
                    "internal.vcgen.mut_borrow_arg_place: `&mut` argument `{}` has a \
                     projected place the call write-back does not support",
                    place.render()
                ));
                continue;
            };
            // Binder naming is site policy: an array keeps its positional
            // `_arrN` name, a class state or view its source-anchored hint.
            // (The `_st` fallback names shapes `fresh_state_for` refuses.)
            let mut array_before = None;
            let (b, len) = match &referent {
                Ty::Array(_) => {
                    let chain = if let Some(field) = field.as_deref() {
                        if let Some(Val::Obj(base)) = self.env.get(array.as_str()) {
                            Some(project_field(base, field))
                        } else {
                            None
                        }
                    } else if let Some(Val::Arr(sequence)) = self.env.get(array.as_str()) {
                        Some(sequence.clone())
                    } else {
                        None
                    };
                    array_before = chain.clone();
                    let len = match chain {
                        Some(prior) => LenFact::Eq(prior),
                        None => {
                            refuse_vc_type(format!(
                                "internal.vcgen.mut_borrow_arg_state: `&mut` array \
                                 argument `{hint}` has no pre-call sequence state"
                            ));
                            LenFact::Skip
                        }
                    };
                    self.fresh += 1;
                    (format!("_arr{}", self.fresh), len)
                }
                Ty::Class(_) => (self.hinted_sym("_obj", Some(hint)), LenFact::Skip),
                Ty::Res(_) => (self.hinted_sym("_view", Some(hint)), LenFact::Skip),
                Ty::Slots(_) => {
                    refuse_vc_type(format!(
                        "internal.vcgen.slots_unsupported: mutable slot loan `{hint}` has no symbolic write-back"
                    ));
                    (self.hinted_sym("_slots", Some(hint)), LenFact::Skip)
                }
                Ty::Int(_)
                | Ty::Bool
                | Ty::Param(_)
                | Ty::Record(_)
                | Ty::Raw(_)
                | Ty::RawRecord(_)
                | Ty::Option(_)
                | Ty::OptionRaw(_)
                | Ty::Borrow(..)
                | Ty::Unit => (self.hinted_sym("_st", Some(hint)), LenFact::Skip),
            };
            let first_fresh_hyp = self.hyps.len();
            let fresh = self.fresh_state_for(&referent, &b, &array, len);
            let length_hyp = array_before.as_ref().and_then(|before| {
                let expected = format!("({b}.len) = ({before}.len)");
                self.hyps[first_fresh_hyp..]
                    .iter()
                    .find(|(_, proposition)| proposition == &expected)
                    .map(|(name, _)| name.clone())
            });
            match field.as_deref() {
                // A whole place: the name now holds the fresh state.
                None => {
                    self.env.insert(array.clone(), fresh);
                }
                // A field place: write the fresh state back into the base,
                // leaving every sibling where it was.
                Some(f) => {
                    let Some(vs) = fresh.writeback_term() else {
                        // `fresh_state_for` refused the shape and latched;
                        // leave the base untouched rather than write junk.
                        continue;
                    };
                    let base = self
                        .env
                        .get(array.as_str())
                        .and_then(|value| {
                            if let Val::Obj(chain) = value {
                                Some(chain.clone())
                            } else {
                                None
                            }
                        })
                        .unwrap_or_else(|| array.clone());
                    self.env.insert(
                        array.clone(),
                        Val::Obj(format!("{{ {base} with {f} := {vs} }}")),
                    );
                }
            }

            // Read the target back from the environment after write-back.
            // The fixed Lean proof below cannot close if this still names the
            // pre-call state, the wrong field, or the owning object itself.
            let observed = match field.as_deref() {
                None => self.env.get(array.as_str()).and_then(Val::writeback_term),
                Some(field) => match self.env.get(array.as_str()) {
                    Some(Val::Obj(base)) => Some(project_field(base, field)),
                    Some(
                        Val::Int(_)
                        | Val::Prop(_)
                        | Val::Opt(_)
                        | Val::Arr(_)
                        | Val::Slots(_)
                        | Val::Record(_)
                        | Val::View(_)
                        | Val::Ptr(_)
                        | Val::Unit,
                    )
                    | None => None,
                },
            }
            .unwrap_or_default();
            let Some(call_start) = checked_call.key.span.start.checked_sub(self.f.span.start)
            else {
                refuse_vc_type(format!(
                    "internal.transition_certificate_identity: call span {}..{} precedes its {} body",
                    checked_call.key.span.start,
                    checked_call.key.span.end,
                    self.call_owner.render()
                ));
                continue;
            };
            let Some(call_end) = checked_call.key.span.end.checked_sub(self.f.span.start) else {
                refuse_vc_type(format!(
                    "internal.transition_certificate_identity: call span {}..{} precedes its {} body",
                    checked_call.key.span.start,
                    checked_call.key.span.end,
                    self.call_owner.render()
                ));
                continue;
            };
            let owner = self.call_owner.certificate_component();
            let target = checked_call.key.target.certificate_component();
            let raw_place = place.render();
            let occurrence = format!("{call_start}:{call_end}");
            let parameter_index = argument.parameter_index.to_string();
            let symbolic_visit = symbolic_visit.to_string();
            let cert_name = format!(
                "transition.{owner}.call_havoc.{raw_place}.site.{call_start}-{call_end}.arg.{}.visit.{symbolic_visit}.to.{target}",
                argument.parameter_index,
            );
            let thm_name = injective_lean_components(
                "cert",
                &[
                    owner.as_str(),
                    target.as_str(),
                    raw_place.as_str(),
                    occurrence.as_str(),
                    parameter_index.as_str(),
                    symbolic_visit.as_str(),
                ],
            );
            match TransitionCertificate::call_havoc(
                cert_name,
                thm_name,
                transition,
                b.clone(),
                observed,
                array_before,
                length_hyp,
                self.binders.clone(),
                self.hyps.clone(),
            ) {
                Ok(certificate) => self.out.transition_certificates.push(certificate),
                Err(message) => refuse_vc_type(message),
            }
            out.push((pname, b));
        }
        out
    }

    fn run(&mut self) {
        let Some(body_scope) = self.checked_body_scope() else {
            return;
        };
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
            self.var_tys.insert(p.name.clone(), p.ty.clone());
            // How a parameter is bound decides the binder's *name*, never
            // its Lean shape — `fresh_state_for` reads the shape off what
            // the type names. A unique borrow's binder is the *entry* state
            // `_old_p`, exactly as a `&mut` array's or a `&mut C`'s is: the
            // current state lives in the symbolic env and is replaced by
            // stores, `&mut self` method calls, and havoc, while `old p` in
            // clauses resolves to the binder (ADR 0023).
            let binder = if p.ty.is_unique_borrow() {
                let b = format!("_old_{}", p.name);
                self.entry_states.insert(p.name.clone(), b.clone());
                b
            } else {
                p.name.clone()
            };
            let ty = p.ty.clone();
            let name = p.name.clone();
            let value = self.fresh_state_for(&ty, &binder, &name, LenFact::Bounded);
            self.env.insert(name, value);
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
                def_name: callable_lean_name("wf", &self.call_owner, "pre", i + 1),
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
                def_name: callable_lean_name("wf", &self.call_owner, "post", i + 1),
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
                def_name: callable_lean_name("wf", &self.call_owner, "variant", 1),
                binders,
                text: self.preprocess(&v.text),
                span: v.span,
                desc: format!("`variant` clause of `{}`", self.fname),
                result_ty: "Int",
            });
        }

        let stmts: Vec<&Stmt> = self.f.body.iter().collect();
        self.exec(&stmts, body_scope, &Tail::FnEnd);
    }

    fn result_lean_ty(&self) -> String {
        match &self.f.ret {
            Ty::Int(_) | Ty::Param(_) => "Int".into(),
            Ty::Option(element) => lean_option_ty(&element.clone(), self.classes),
            Ty::OptionRaw(_) => "Option Sable.RawPtr".into(),
            // Bool results are Prop-valued in the logic: posts like
            // `result → P` splice with no coercion noise.
            Ty::Bool => "Prop".into(),
            // A returned class value is its structure (ADR 0010).
            Ty::Class(ci) => lean_class_name(&self.classes[*ci].name),
            Ty::Record(ri) => lean_record_name(&self.records[*ri].name),
            // A returned resource is its view: the authority moves, and
            // the logic sees only what the view says (ADR 0024).
            Ty::Res(k) => lean_res_view_ty(*k, self.records),
            Ty::Raw(_) | Ty::RawRecord(_) => "Sable.RawPtr".into(),
            Ty::Unit => "Unit".into(),
            // A returned array is its sequence, the same lift `&[T]` and
            // `[T]` already share — binding mode never reached this type
            // (ADR 0067), and returning the owner is what ADR 0085 opened.
            Ty::Array(element) => lean_array_ty(element, self.records),
            Ty::Slots(_) => {
                refuse_vc_type(
                    "internal.vcgen.slots_unsupported: owner-slot return has no Lean type".into(),
                );
                UNSUPPORTED_LEAN_TY.into()
            }
            Ty::Borrow(..) => {
                unreachable!("checked: borrowed values are not return types")
            }
        }
    }

    fn exec(&mut self, stmts: &[&'a Stmt], scope: ScopeId, tail: &Tail<'a>) {
        let Some((stmt, rest)) = stmts.split_first() else {
            match tail {
                Tail::FnEnd => {
                    let Some(plan) = self.control_plan() else {
                        return;
                    };
                    if scope != plan.body_scope() {
                        refuse_vc_type(format!(
                            "internal.vcgen.control_plan_active_scope_mismatch: function end inside {} is not in the checked body scope",
                            self.call_owner.render()
                        ));
                        return;
                    }
                    // Falling off a procedure body is its implicit return:
                    // lexical locals die before posts, while parameter-frame
                    // state remains available until after the posts.
                    if self.f.ret != Ty::Unit {
                        refuse_vc_type(format!(
                            "internal.vcgen.control_plan_nonunit_fallthrough: non-unit function {} reached its checked body end without a return edge",
                            self.call_owner.render()
                        ));
                        return;
                    }
                    let routes = plan.implicit_return();
                    if !self.apply_control_route(routes.lexical(), ExitKind::Return) {
                        return;
                    }
                    self.emit_posts(None);
                    let _ = self.apply_control_route(routes.frame(), ExitKind::Return);
                }
                Tail::Scope {
                    normal_exit,
                    rest,
                    parent_scope,
                    outer,
                } => {
                    let Some(exit) = normal_exit else {
                        refuse_vc_type(format!(
                            "internal.vcgen.control_plan_branch_normal_edge_missing: a checked non-fallthrough branch arm inside {} reached its parent continuation",
                            self.call_owner.render()
                        ));
                        return;
                    };
                    if !self.apply_scope_route(exit, scope, ExitKind::Fallthrough) {
                        return;
                    }
                    let rest = rest.clone();
                    let outer = (**outer).clone();
                    self.exec(&rest, *parent_scope, &outer);
                }
                Tail::Loop {
                    backedge,
                    invariants,
                    variant,
                    v0,
                } => {
                    let Some(exit) = backedge else {
                        refuse_vc_type(format!(
                            "internal.vcgen.control_plan_loop_backedge_missing: a checked non-fallthrough loop body inside {} reached its header",
                            self.call_owner.render()
                        ));
                        return;
                    };
                    // Loop-body storage dies on the backedge before the
                    // preservation obligations are stated.
                    if !self.apply_scope_route(exit, scope, ExitKind::Backedge) {
                        return;
                    }
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
                Tail::Expose {
                    body_exit,
                    close,
                    parent_scope,
                    array,
                    res,
                    mutable,
                    kw_span,
                    release_loan,
                    loan,
                    entry_arr,
                    rest,
                    outer,
                } => {
                    // Snapshot the final view before its source binding dies;
                    // reconstruction consumes the pure Lean term afterward.
                    let view = self.view_str(res);
                    if !self.apply_scope_route(body_exit, scope, ExitKind::Fallthrough) {
                        return;
                    }
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
                            format!(
                                "∀ k, 0 ≤ k → k < {a2}.len → 0 ≤ {a2}.get k ∧ {a2}.get k ≤ u8.max"
                            ),
                        );
                        self.env.insert(array.clone(), Val::Arr(a2));
                    }
                    if !close.clears().contains(release_loan) {
                        refuse_vc_type(format!(
                            "internal.vcgen.control_plan_exposure_release_missing: checked exposure close inside {} does not release its retained loan identity",
                            self.call_owner.render()
                        ));
                        return;
                    }
                    if !self.apply_control_route(close, ExitKind::ExposureClose) {
                        return;
                    }
                    let rest = rest.clone();
                    let outer = (**outer).clone();
                    self.exec(&rest, *parent_scope, &outer);
                }
            }
            return;
        };
        if !self.consume_statement_trap_sites(scope, stmt) {
            return;
        }
        match stmt {
            Stmt::Decl { name, ty, init, .. } => {
                self.var_tys.insert(name.clone(), ty.clone());
                if let Some(e) = init {
                    if matches!(
                        e.kind,
                        ExprKind::Call { .. }
                            | ExprKind::MethodCall { .. }
                            | ExprKind::CtorCall { .. }
                            | ExprKind::TraitCall { .. }
                            | ExprKind::DeviceOp { .. }
                            | ExprKind::AllocArray { .. }
                            | ExprKind::SlotOp { .. }
                            | ExprKind::ArrayLit(_)
                    ) {
                        self.name_hint = Some(name.clone());
                    }
                    let v = self.eval(e, scope);
                    let _transfer = self.checked_value_transfer(
                        e,
                        crate::ownership::ValueTransferSink::Binding(name.clone()),
                    );
                    self.name_hint = None;
                    self.env.insert(name.clone(), v);
                } else {
                    self.env.remove(name);
                }
                self.exec(rest, scope, tail);
            }
            Stmt::Assign {
                name,
                name_span,
                value,
            } => {
                let destination = Place::local(name);
                let Some(action) =
                    self.checked_assignment_action(scope, *name_span, &destination, value)
                else {
                    return;
                };
                if matches!(
                    value.kind,
                    ExprKind::Call { .. }
                        | ExprKind::MethodCall { .. }
                        | ExprKind::CtorCall { .. }
                        | ExprKind::TraitCall { .. }
                        | ExprKind::DeviceOp { .. }
                        | ExprKind::AllocArray { .. }
                        | ExprKind::SlotOp { .. }
                        | ExprKind::ArrayLit(_)
                ) {
                    self.name_hint = Some(name.clone());
                }
                let v = self.eval(value, scope);
                let _transfer = self.checked_value_transfer_key(value, action.transfer_key());
                self.name_hint = None;
                // The exact conditional destruction/staging action was
                // consumed above. Destruction contributes no normal-state
                // proposition in this symbolic value model; installing `v`
                // is the observable post-action state.
                self.env.insert(name.clone(), v);
                self.exec(rest, scope, tail);
            }
            Stmt::Return { value, span } => {
                // Validate the checked edge identity before evaluating a
                // possibly forged replacement result. The lookup is static;
                // runtime ordering remains evaluate-result, then cleanup.
                let Some(routes) = self.checked_return_routes(*span, scope, value.is_some()) else {
                    return;
                };
                let result_eq = value.as_ref().map(|value| {
                    let evaluated = self.eval(value, scope);
                    let _transfer = self
                        .checked_value_transfer(value, crate::ownership::ValueTransferSink::Return);
                    match evaluated {
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
                        // A returned array is the sequence its name holds.
                        // There is no `ret_inv` analogue: an array's checked
                        // facts are its length and its element domain, both
                        // true of every state the callee could have left it
                        // in, and neither is a user invariant to re-establish.
                        Val::Arr(chain) | Val::Slots(chain) => {
                            format!("(result = {chain})")
                        }
                        // Returning a resource returns its authority; in
                        // the logic that is just its view. There is no
                        // `ret_inv` analogue — a view carries its own
                        // well-formedness, not a user invariant.
                        Val::View(chain) => format!("(result = {chain})"),
                        // A raw pointer is data: provenance and an offset,
                        // no authority, nothing to re-establish (ADR 0026).
                        Val::Ptr(chain) => format!("(result = {chain})"),
                        Val::Unit => unreachable!("unit values cannot be returned"),
                    }
                });
                if !self.apply_control_route(routes.lexical(), ExitKind::Return) {
                    return;
                }
                self.emit_posts(result_eq);
                let _ = self.apply_control_route(routes.frame(), ExitKind::Return);
            }
            // `unsafe { ... }`: a marker with no verification content of
            // its own. Splice the body into the continuation, which is
            // also why locals declared inside outlive it.
            Stmt::Unsafe { body, .. } => {
                let mut inner: Vec<&Stmt> = body.iter().collect();
                inner.extend_from_slice(rest);
                self.exec(&inner, scope, tail);
            }
            Stmt::StaticAlloc { size, ptr, res, .. } => {
                let Val::Int(n) = self.eval(size, scope) else {
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
                self.exec(rest, scope, tail);
            }
            Stmt::SystemAlloc {
                size,
                ptr,
                res,
                release,
                ..
            } => {
                let Val::Int(n) = self.eval(size, scope) else {
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
                self.exec(rest, scope, tail);
            }
            Stmt::SystemDealloc {
                ptr, res, release, ..
            } => {
                let Val::Ptr(p) = self.eval(ptr, scope) else {
                    unreachable!("checked: raw pointer")
                };
                let Val::View(bytes) = self.eval(res, scope) else {
                    unreachable!("checked: RawSpan")
                };
                let _resource_transfer = self.checked_value_transfer(
                    res,
                    crate::ownership::ValueTransferSink::SystemDeallocResource,
                );
                let Val::View(rel) = self.eval(release, scope) else {
                    unreachable!("checked: SystemDealloc")
                };
                let _release_transfer = self.checked_value_transfer(
                    release,
                    crate::ownership::ValueTransferSink::SystemDeallocRelease,
                );
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
                self.exec(rest, scope, tail);
            }
            // Lexical exposure. Entry hands the body a span whose bytes
            // are the array's elements, all initialized, at offset 0 of a
            // fresh loan allocation. Exit takes it back: the array becomes
            // what the bytes say, under three obligations that together
            // are what "the safe world owns this again" means (ADR 0026).
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
                ..
            } => {
                // Resolve the complete normal phase and link its effect key
                // before opening a symbolic loan. Source syntax is checked
                // against the retained rebuild action, but never becomes a
                // second authority for names, type, mutability, or exits.
                let (
                    exposure_scope,
                    effect_key,
                    body_exit,
                    close,
                    parent_scope,
                    capture,
                    planned_owner,
                    owner_ty,
                    planned_mutability,
                    planned_pointer,
                    planned_resource,
                    planned_keyword,
                    release_loan,
                ) = {
                    let Some(plan) = self.control_plan() else {
                        return;
                    };
                    let exposure = match plan.exposure_plan(scope, *kw_span) {
                        Ok(exposure) => exposure,
                        Err(error) => {
                            refuse_vc_type(format!(
                                "internal.vcgen.control_plan_exposure_edge_missing: {} at {}..{} inside {}",
                                error.message,
                                error.span.start,
                                error.span.end,
                                self.call_owner.render()
                            ));
                            return;
                        }
                    };
                    let body_plan = plan.block(exposure.body());
                    if body_plan.scope() != exposure.body_scope()
                        || body_plan.flow() != exposure.body_flow()
                        || exposure.body_flow().can_fall_through() != exposure.normal().is_some()
                    {
                        refuse_vc_type(format!(
                            "internal.vcgen.control_plan_exposure_edge_mismatch: retained exposure body inside {} disagrees with its sealed normal edge",
                            self.call_owner.render()
                        ));
                        return;
                    }
                    let Some(normal) = exposure.normal() else {
                        refuse_vc_type(format!(
                            "internal.vcgen.control_plan_exposure_normal_missing: exposure at {}..{} inside {} has no checked reconstruction edge",
                            kw_span.start,
                            kw_span.end,
                            self.call_owner.render()
                        ));
                        return;
                    };
                    if exposure.body_flow().contains_return() {
                        refuse_vc_type(format!(
                            "internal.vcgen.control_plan_exposure_return_edge: exposure at {}..{} inside {} contains a retained return edge that would bypass reconstruction",
                            kw_span.start,
                            kw_span.end,
                            self.call_owner.render()
                        ));
                        return;
                    }
                    let rebuild = normal.rebuild();
                    let expected_owner = Place::local(array);
                    let expected_pointer = Place::local(ptr);
                    let expected_resource = Place::local(res);
                    let expected_mutability = if *mutable {
                        Mutability::Mut
                    } else {
                        Mutability::Shared
                    };
                    if normal.parent_scope() != scope
                        || normal.capture() != rebuild.resource()
                        || normal.body_exit().kind() != ExitKind::Fallthrough
                        || normal.body_exit().scopes() != [exposure.body_scope()]
                        || normal.close().kind() != ExitKind::ExposureClose
                        || !normal.close().clears().contains(normal.release_loan())
                        || rebuild.owner() != &expected_owner
                        || rebuild.pointer() != &expected_pointer
                        || rebuild.resource() != &expected_resource
                        || rebuild.mutability() != expected_mutability
                        || rebuild.keyword_span() != *kw_span
                        || self.var_tys.get(array) != Some(rebuild.owner_ty())
                    {
                        refuse_vc_type(format!(
                            "internal.vcgen.control_plan_exposure_edge_mismatch: retained exposure phases at {}..{} inside {} disagree with the checked source edge",
                            kw_span.start,
                            kw_span.end,
                            self.call_owner.render()
                        ));
                        return;
                    }
                    if exposure.effect_key().owner != self.call_owner
                        || exposure.effect_key().span != *kw_span
                    {
                        refuse_vc_type(format!(
                            "internal.vcgen.control_plan_exposure_effect_mismatch: retained exposure edge inside {} names a different ownership effect",
                            self.call_owner.render()
                        ));
                        return;
                    }
                    (
                        exposure.body_scope(),
                        exposure.effect_key().clone(),
                        normal.body_exit().clone(),
                        normal.close().clone(),
                        normal.parent_scope(),
                        normal.capture().clone(),
                        rebuild.owner().clone(),
                        rebuild.owner_ty().clone(),
                        rebuild.mutability(),
                        rebuild.pointer().clone(),
                        rebuild.resource().clone(),
                        rebuild.keyword_span(),
                        normal.release_loan().clone(),
                    )
                };
                let Some(_effect) = self.checked_exposure(
                    &effect_key,
                    &planned_owner,
                    *array_span,
                    &owner_ty,
                    planned_mutability,
                    planned_pointer.root(),
                    *ptr_span,
                    planned_resource.root(),
                    *res_span,
                ) else {
                    return;
                };
                let array = planned_owner.root().to_string();
                let ptr = planned_pointer.root().to_string();
                let res = capture.root().to_string();
                let mutable = planned_mutability == Mutability::Mut;
                let entry_arr = self.arr_str(&array);
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
                    body_exit,
                    close,
                    parent_scope,
                    array,
                    res,
                    mutable,
                    kw_span: planned_keyword,
                    release_loan,
                    loan,
                    entry_arr,
                    rest: rest.to_vec(),
                    outer: Box::new(tail.clone()),
                };
                self.exec(&inner, exposure_scope, &etail);
            }
            Stmt::ExprStmt(e) => {
                let temporary_drop = if matches!(e.ty.as_ref(), Some(Ty::Class(_))) {
                    let Some(action) = self.checked_temporary_drop_action(scope, e) else {
                        return;
                    };
                    Some(action)
                } else {
                    None
                };
                // Evaluated for obligations/assumptions. A retained class
                // result then transfers into its compiler temporary and is
                // destroyed before the continuation; destruction is the
                // authenticated proof no-op described by the action helper.
                let _ = self.eval(e, scope);
                if let Some(action) = temporary_drop.as_ref() {
                    let _transfer = self.checked_value_transfer_key(e, action.transfer_key());
                }
                self.exec(rest, scope, tail);
            }
            Stmt::VarDecl { name, init, ty, .. } => {
                if matches!(
                    init.kind,
                    ExprKind::Call { .. }
                        | ExprKind::MethodCall { .. }
                        | ExprKind::CtorCall { .. }
                        | ExprKind::TraitCall { .. }
                        | ExprKind::AllocArray { .. }
                        | ExprKind::SlotOp { .. }
                        | ExprKind::ArrayLit(_)
                ) {
                    self.name_hint = Some(name.clone());
                }
                let v = self.eval(init, scope);
                let _transfer = self.checked_value_transfer(
                    init,
                    crate::ownership::ValueTransferSink::Binding(name.clone()),
                );
                self.name_hint = None;
                self.var_tys
                    .insert(name.clone(), ty.clone().expect("checked: var type"));
                self.env.insert(name.clone(), v);
                self.exec(rest, scope, tail);
            }
            Stmt::FieldAssign {
                field,
                field_span,
                value,
            } => {
                let destination = Place::field("self", field);
                let Some(action) =
                    self.checked_field_assignment_action(scope, *field_span, &destination, value)
                else {
                    return;
                };
                let v = self.eval(value, scope);
                let _transfer = self.checked_value_transfer_key(value, action.transfer_key());
                // The retained action has already authenticated conditional
                // destruction of the old field and RHS staging. The proof
                // state models only the normal installed value.
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
                            | Val::Slots(s)
                            | Val::Obj(s)
                            | Val::View(s)
                            | Val::Ptr(s) => s,
                            Val::Prop(p) => lean_bool_value(&p),
                            // Parenthesized so the option chain stays one
                            // structure-update argument.
                            Val::Opt(s) => format!("({s})"),
                            Val::Record(_) | Val::Unit => {
                                refuse_vc_type(format!(
                                    "internal.vcgen.field_state_unsupported: `self.{field}` \
                                     has no field-store rule for this value"
                                ));
                                "0".to_string()
                            }
                        };
                        let chain = self.self_chain();
                        self.env.insert(
                            "self".to_string(),
                            Val::Obj(format!("{{ {chain} with {field} := {vs} }}")),
                        );
                    }
                    Cctx::None => unreachable!("checked: fields only in members"),
                }
                self.exec(rest, scope, tail);
            }
            Stmt::FieldStore {
                field,
                field_span,
                index,
                value,
            } => {
                let Val::Int(i) = self.eval(index, scope) else {
                    unreachable!()
                };
                let v = match self.eval(value, scope) {
                    Val::Int(v) | Val::Record(v) => v,
                    Val::Prop(p) => lean_bool_value(&p),
                    Val::Arr(_)
                    | Val::Slots(_)
                    | Val::Obj(_)
                    | Val::View(_)
                    | Val::Ptr(_)
                    | Val::Opt(_)
                    | Val::Unit => {
                        refuse_vc_type(format!(
                            "internal.vcgen.field_state_unsupported: `self.{field}[..]` has \
                             no element-store value for this type"
                        ));
                        "0".to_string()
                    }
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
                self.exec(rest, scope, tail);
            }
            Stmt::Store {
                array,
                array_span,
                index,
                value,
            } => {
                let Val::Int(i) = self.eval(index, scope) else {
                    unreachable!()
                };
                let evaluated = self.eval(value, scope);
                let v = match self.var_tys.get(array).cloned() {
                    Some(found) => match checked_array_payload(&found) {
                        Some(payload) => {
                            checked_array_payload_value(payload, evaluated, |_payload| {
                                format!(
                                    "internal.vcgen.lean_type_unsupported: an element store into `{}` \
                                 has no proof value",
                                    found.name()
                                )
                            })
                        }
                        None => {
                            refuse_vc_type(format!(
                                "internal.vcgen.lean_type_unsupported: an element store into `{}` \
                                 has no proof value",
                                found.name()
                            ));
                            UNSUPPORTED_LEAN_VALUE.into()
                        }
                    },
                    None => {
                        refuse_vc_type(
                            "internal.vcgen.lean_type_unsupported: an element store into \
                             `<unknown>` has no proof value"
                                .to_string(),
                        );
                        UNSUPPORTED_LEAN_VALUE.into()
                    }
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
                self.exec(rest, scope, tail);
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                let (then_scope, then_normal_exit, else_control) = {
                    let Some(plan) = self.control_plan() else {
                        return;
                    };
                    let branch = match plan.branch(scope, cond.span, else_block.is_some()) {
                        Ok(branch) => branch,
                        Err(error) => {
                            refuse_vc_type(format!(
                                "internal.vcgen.control_plan_branch_edge_missing: {} at {}..{} inside {}",
                                error.message,
                                error.span.start,
                                error.span.end,
                                self.call_owner.render()
                            ));
                            return;
                        }
                    };
                    let then_arm = branch.then_arm();
                    let then_block_plan = plan.block(then_arm.block());
                    if then_block_plan.scope() != then_arm.scope()
                        || then_block_plan.flow() != then_arm.flow()
                    {
                        refuse_vc_type(format!(
                            "internal.vcgen.control_plan_branch_edge_mismatch: retained then-arm block inside {} disagrees with its sealed edge",
                            self.call_owner.render()
                        ));
                        return;
                    }
                    let else_control = branch.else_arm().map(|arm| {
                        let block = plan.block(arm.block());
                        (block, arm)
                    });
                    if else_control.as_ref().is_some_and(|(block, arm)| {
                        block.scope() != arm.scope() || block.flow() != arm.flow()
                    }) {
                        refuse_vc_type(format!(
                            "internal.vcgen.control_plan_branch_edge_mismatch: retained else-arm block inside {} disagrees with its sealed edge",
                            self.call_owner.render()
                        ));
                        return;
                    }
                    let else_control =
                        else_control.map(|(_, arm)| (arm.scope(), arm.normal_exit().cloned()));
                    let reaches_continuation = then_arm.normal_exit().is_some()
                        || else_control
                            .as_ref()
                            .is_none_or(|(_, normal_exit)| normal_exit.is_some());
                    if branch.flow().can_fall_through() != reaches_continuation {
                        refuse_vc_type(format!(
                            "internal.vcgen.control_plan_branch_edge_mismatch: retained branch flow inside {} disagrees with its normal exits",
                            self.call_owner.render()
                        ));
                        return;
                    }
                    (
                        then_arm.scope(),
                        then_arm.normal_exit().cloned(),
                        else_control,
                    )
                };
                let p = self.eval_prop(cond, scope);
                // Full clones, not length-truncation: a havoc in a
                // nested loop REWRITES earlier hypotheses in place
                // (SSA versioning), which truncation cannot undo.
                let snap_env = self.env.clone();
                let snap_hyps = self.hyps.clone();
                let snap_ctx = self.context.clone();
                let snap_var_tys = self.var_tys.clone();
                let snap_entry_states = self.entry_states.clone();

                self.hyps.push((format!("h_path_{}", hslug(&p)), p.clone()));
                self.context.push((format!("path {p}"), cond.span));
                let then_stmts: Vec<&Stmt> = then_block.iter().collect();
                let then_tail = Tail::Scope {
                    normal_exit: then_normal_exit,
                    rest: rest.to_vec(),
                    parent_scope: scope,
                    outer: Box::new(tail.clone()),
                };
                self.exec(&then_stmts, then_scope, &then_tail);

                self.env = snap_env.clone();
                self.hyps = snap_hyps.clone();
                self.context = snap_ctx.clone();
                self.var_tys = snap_var_tys.clone();
                self.entry_states = snap_entry_states.clone();

                self.hyps
                    .push((format!("h_path_not_{}", hslug(&p)), format!("¬{p}")));
                self.context.push((format!("path ¬{p}"), cond.span));
                match (else_block, else_control) {
                    (Some(else_block), Some((else_scope, else_normal_exit))) => {
                        let else_stmts: Vec<&Stmt> = else_block.iter().collect();
                        let else_tail = Tail::Scope {
                            normal_exit: else_normal_exit,
                            rest: rest.to_vec(),
                            parent_scope: scope,
                            outer: Box::new(tail.clone()),
                        };
                        self.exec(&else_stmts, else_scope, &else_tail);
                    }
                    (None, None) => self.exec(rest, scope, tail),
                    (Some(_else_block), None) => {
                        refuse_vc_type(format!(
                            "internal.vcgen.control_plan_branch_mismatch: checked branch shape inside {} disagrees with its retained routes",
                            self.call_owner.render()
                        ));
                    }
                    (None, Some(_else_control)) => {
                        refuse_vc_type(format!(
                            "internal.vcgen.control_plan_branch_mismatch: checked branch shape inside {} disagrees with its retained routes",
                            self.call_owner.render()
                        ));
                    }
                }
                self.env = snap_env;
                self.hyps = snap_hyps;
                self.context = snap_ctx;
                self.var_tys = snap_var_tys;
                self.entry_states = snap_entry_states;
            }
            Stmt::Assert(clause) => {
                // Well-formedness def so a clause that fails to elaborate
                // maps to its own span.
                self.fresh += 1;
                self.out.clause_wfs.push(ClauseWf {
                    def_name: callable_lean_name("wf", &self.call_owner, "assert", self.fresh),
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
                self.exec(rest, scope, tail);
            }
            Stmt::While {
                cond,
                invariants,
                variant,
                kw_span,
                body,
                ..
            } => {
                // Resolve and link both retained authorities before emitting a
                // clause definition, obligation, binder, hypothesis, or havoc.
                let (body_scope, backedge, effect_key) = {
                    let Some(plan) = self.control_plan() else {
                        return;
                    };
                    let loop_plan = match plan.loop_plan(scope, *kw_span, cond.span) {
                        Ok(loop_plan) => loop_plan,
                        Err(error) => {
                            refuse_vc_type(format!(
                                "internal.vcgen.control_plan_loop_edge_missing: {} at {}..{} inside {}",
                                error.message,
                                error.span.start,
                                error.span.end,
                                self.call_owner.render()
                            ));
                            return;
                        }
                    };
                    let body_plan = plan.block(loop_plan.body());
                    if body_plan.scope() != loop_plan.body_scope()
                        || body_plan.flow() != loop_plan.body_flow()
                        || loop_plan.body_flow().can_fall_through()
                            != loop_plan.backedge().is_some()
                    {
                        refuse_vc_type(format!(
                            "internal.vcgen.control_plan_loop_edge_mismatch: retained loop body inside {} disagrees with its sealed backedge",
                            self.call_owner.render()
                        ));
                        return;
                    }
                    if loop_plan.effect_key().owner != self.call_owner
                        || loop_plan.effect_key().span != *kw_span
                    {
                        refuse_vc_type(format!(
                            "internal.vcgen.control_plan_loop_effect_mismatch: retained loop edge inside {} names a different ownership effect",
                            self.call_owner.render()
                        ));
                        return;
                    }
                    (
                        loop_plan.body_scope(),
                        loop_plan.backedge().cloned(),
                        loop_plan.effect_key().clone(),
                    )
                };
                let Some(loop_effects) = self.checked_loop_effects(&effect_key, cond.span) else {
                    return;
                };
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
                        def_name: callable_lean_name(
                            "wf",
                            &self.call_owner,
                            &format!("loop.{i}"),
                            self.fresh,
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

                // 2. Havoc the exact checker-linked mutation set (fresh
                // source-named binders).
                self.havoc(&loop_effects);

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
                let p = self.eval_prop(cond, scope);

                // Full clones — see the If arm.
                let snap_env = self.env.clone();
                let snap_hyps = self.hyps.clone();
                let snap_ctx = self.context.clone();
                let snap_var_tys = self.var_tys.clone();
                let snap_entry_states = self.entry_states.clone();

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
                    backedge,
                    invariants,
                    variant,
                    v0,
                };
                self.exec(&body_stmts, body_scope, &loop_tail);

                self.env = snap_env.clone();
                self.hyps = snap_hyps.clone();
                self.context = snap_ctx.clone();
                self.var_tys = snap_var_tys.clone();
                self.entry_states = snap_entry_states.clone();

                // 5. Continuation: invariants + ¬cond.
                self.hyps
                    .push((format!("h_path_not_{}", hslug(&p)), format!("¬{p}")));
                self.context.push((format!("path ¬{p}"), cond.span));
                self.exec(rest, scope, tail);
                self.env = snap_env;
                self.hyps = snap_hyps;
                self.context = snap_ctx;
                self.var_tys = snap_var_tys;
                self.entry_states = snap_entry_states;
            }
        }
    }

    /// A loop preserves one owner-slot container's length only when every
    /// mutation that can overlap that exact place is a checked take or put
    /// on that same place. Whole-owner writes can install a differently
    /// sized allocation and therefore deliberately receive no length fact.
    fn loop_preserves_slot_length(effects: &CheckedLoopEffects, container: &Place) -> bool {
        effects
            .mutations
            .iter()
            .filter(|mutation| mutation.place().overlaps(container))
            .all(|mutation| {
                matches!(
                    mutation,
                    CheckedMutation::Slot {
                        container: mutated,
                        operation:
                            CheckedSlotMutationKind::Take | CheckedSlotMutationKind::Put,
                        ..
                    } if mutated == container
                )
            })
    }

    /// Fresh source-named binders for everything the loop body assigns
    /// (plus locals whose symbolic value mentions a havocked variable,
    /// transitively). Hypotheses mentioning havocked names are dropped.
    fn havoc(&mut self, effects: &CheckedLoopEffects) {
        let mut havoc_set: HashSet<String> = effects
            .mutations
            .iter()
            .map(|mutation| mutation.place().root().to_string())
            .collect();
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
                    | Val::Slots(s)
                    | Val::Obj(s)
                    | Val::Record(s)
                    | Val::View(s)
                    | Val::Ptr(s) => s,
                    Val::Prop(s) => s,
                    Val::Unit => continue,
                };
                if havoc_set.iter().any(|h| mentions(s, h)) {
                    // A shared borrow maps to its own name and never
                    // changes, so a name that mentions a havocked one does
                    // not itself need a fresh binder.
                    if self.var_tys.get(name).map(Ty::binding_mode) != Some(BindingMode::Shared) {
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
            if name == "self" {
                match self.cctx {
                    // Mid-member self-mutation in a loop: fresh state
                    // binder, field facts only. The class invariant is NOT
                    // in force mid-method (design §7), and a destructor's
                    // entry invariant is likewise not re-established once
                    // its body has run (ADR 0029) — loop invariants carry
                    // whatever the continuation needs.
                    Cctx::Method(class, _) | Cctx::Deinit(class) => {
                        let b = self.hinted_sym("_self", Some("_self_loop".to_string()));
                        self.binders.push((b.clone(), lean_class_name(&class.name)));
                        self.push_class_state_facts(class, &b);
                        self.env.insert("self".to_string(), Val::Obj(b));
                        continue;
                    }
                    // Init loops mutate fields through `self.<field>` env
                    // entries (there is no whole-object state yet): version
                    // every tracked field — leaving ANY field's chain in
                    // place would let the pre-loop value survive the loop
                    // (same class of bug as must-fail/owned_loop_stale),
                    // and `fresh_state_for` is exhaustive over the field's
                    // type, so a field with no fresh-state story refuses
                    // rather than keeping its chain.
                    Cctx::Init(class) => {
                        for fld in &class.fields {
                            let key = format!("self.{}", fld.name);
                            let Some(prior_value) = self.env.get(&key).cloned() else {
                                continue;
                            };
                            self.fresh += 1;
                            let b = format!("_self{}_{}", self.fresh, fld.name);
                            // Array stores preserve length. Owner-slot
                            // take/put does too, but a whole-field write may
                            // replace the allocation and must drop the
                            // relation even when the old chain survives.
                            let len = match &prior_value {
                                Val::Arr(chain) => {
                                    let prior = substitute(chain, &stale_map, None);
                                    if havoc_set
                                        .iter()
                                        .any(|h| !stale_map.contains_key(h) && mentions(&prior, h))
                                    {
                                        LenFact::Skip
                                    } else {
                                        LenFact::Eq(prior)
                                    }
                                }
                                Val::Slots(chain) => {
                                    let container = Place::field("self", &fld.name);
                                    if !Self::loop_preserves_slot_length(effects, &container) {
                                        LenFact::Skip
                                    } else {
                                        let prior = substitute(chain, &stale_map, None);
                                        if havoc_set.iter().any(|h| {
                                            !stale_map.contains_key(h) && mentions(&prior, h)
                                        }) {
                                            LenFact::Skip
                                        } else {
                                            LenFact::Eq(prior)
                                        }
                                    }
                                }
                                Val::Int(_)
                                | Val::Prop(_)
                                | Val::Opt(_)
                                | Val::Obj(_)
                                | Val::Record(_)
                                | Val::View(_)
                                | Val::Ptr(_)
                                | Val::Unit => LenFact::Skip,
                            };
                            let ty = fld.ty.clone();
                            let base = format!("self_{}", fld.name);
                            let value = self.fresh_state_for(&ty, &b, &base, len);
                            self.env.insert(key, value);
                        }
                        continue;
                    }
                    Cctx::None => {}
                }
            }
            // A composite key (`self.<field>`) versions through its base's
            // branch above. One that reaches here alone was pulled in by
            // the cascade: its place was not assigned in the loop, but its
            // chain mentions a havocked name, so rewrite the chain to the
            // stale binders — the pre-loop value is intact and that is its
            // name now. A chain over a body-local (no stale binder) has no
            // pre-loop spelling at all: refuse rather than keep it.
            if name.contains('.') {
                let base = name.split('.').next().expect("split yields a first piece");
                if havoc_set.contains(base) {
                    continue;
                }
                let Some(value) = self.env.get(name).cloned() else {
                    continue;
                };
                let rewrite = |s: &String| substitute(s, &stale_map, None);
                let (chain, rebuilt) = match &value {
                    Val::Int(s) => (rewrite(s), Val::Int(rewrite(s))),
                    Val::Prop(s) => (rewrite(s), Val::Prop(rewrite(s))),
                    Val::Opt(s) => (rewrite(s), Val::Opt(rewrite(s))),
                    Val::Arr(s) => (rewrite(s), Val::Arr(rewrite(s))),
                    Val::Slots(s) => (rewrite(s), Val::Slots(rewrite(s))),
                    Val::Obj(s) => (rewrite(s), Val::Obj(rewrite(s))),
                    Val::Record(s) => (rewrite(s), Val::Record(rewrite(s))),
                    Val::View(s) => (rewrite(s), Val::View(rewrite(s))),
                    Val::Ptr(s) => (rewrite(s), Val::Ptr(rewrite(s))),
                    Val::Unit => continue,
                };
                if havoc_set
                    .iter()
                    .any(|h| !stale_map.contains_key(h) && mentions(&chain, h))
                {
                    refuse_vc_type(format!(
                        "internal.vcgen.havoc_stale_chain: `{name}` depends on a loop-body \
                         local with no pre-loop state"
                    ));
                    continue;
                }
                self.env.insert(name.clone(), rebuilt);
                continue;
            }
            let Some(ty) = self.var_tys.get(name).cloned() else {
                // A body-local declaration: it has no pre-loop state to go
                // stale, so there is nothing to version. A pre-loop env
                // entry under an untyped name would be a chain about to be
                // recaptured by the fresh binders — refuse, fail closed.
                if self.env.contains_key(name) {
                    refuse_vc_type(format!(
                        "internal.vcgen.havoc_untyped_name: `{name}` is havocked at a \
                         loop head but has no declared type"
                    ));
                }
                continue;
            };
            // A shared borrow names storage the loop cannot write, so it is
            // never havocked; every fresh state below is an owned local or
            // a unique borrow. This is a binding-mode filter — the dispatch
            // over what the type names is `fresh_state_for`'s, exhaustive
            // with no wildcard (ADR 0074).
            if ty.binding_mode() == BindingMode::Shared {
                continue;
            }
            // Array stores and unique-loan calls preserve length. Slot
            // take/put preserves length too, but a whole owner write does
            // not. What a surviving relation is equated to differs by
            // binding mode: a `&mut` parameter has an entry-state binder,
            // and an owned local has the pre-havoc `.set` chain instead
            // (rewritten to stale names and kept only when it does not
            // itself mention a havocked body-local).
            let len = if ty.is_unique_borrow() {
                // Only a parameter has an entry state, and only a
                // parameter can be a unique borrow here: a borrow is not a
                // local binding (ADR 0072). If some other name reaches this
                // point the length relation has nothing to be relative to,
                // so refuse rather than index.
                match self.entry_states.get(name.as_str()).cloned() {
                    Some(entry) => LenFact::Eq(entry),
                    None => {
                        refuse_vc_type(format!(
                            "internal.vcgen.borrow_without_entry_state: unique borrow \
                             `{name}` is live at a loop head with no entry state; a \
                             borrow is a parameter binding mode, not a local"
                        ));
                        LenFact::Skip
                    }
                }
            } else {
                match self.env.get(name) {
                    Some(Val::Arr(s)) => {
                        let prior = substitute(s, &stale_map, None);
                        if havoc_set
                            .iter()
                            .any(|h| !stale_map.contains_key(h) && mentions(&prior, h))
                        {
                            LenFact::Skip
                        } else {
                            LenFact::Eq(prior)
                        }
                    }
                    Some(Val::Slots(s)) => {
                        let container = Place::local(name);
                        if !Self::loop_preserves_slot_length(effects, &container) {
                            LenFact::Skip
                        } else {
                            let prior = substitute(s, &stale_map, None);
                            if havoc_set
                                .iter()
                                .any(|h| !stale_map.contains_key(h) && mentions(&prior, h))
                            {
                                LenFact::Skip
                            } else {
                                LenFact::Eq(prior)
                            }
                        }
                    }
                    Some(
                        Val::Int(_)
                        | Val::Prop(_)
                        | Val::Opt(_)
                        | Val::Obj(_)
                        | Val::Record(_)
                        | Val::View(_)
                        | Val::Ptr(_)
                        | Val::Unit,
                    )
                    | None => LenFact::Skip,
                }
            };
            let value = self.fresh_state_for(&ty, name, name, len);
            self.env.insert(name.clone(), value);
        }
    }

    /// Read one checker-admitted owner-slot place. The surface language
    /// currently permits only a mutable local root or a direct `self` field;
    /// keeping that boundary explicit prevents VCgen from inventing general
    /// object-field aliasing semantics.
    fn slot_place_str(&mut self, place: &Place) -> Option<String> {
        if place.is_root() {
            return match self.env.get(place.root()) {
                Some(Val::Slots(slots)) => Some(slots.clone()),
                Some(_) | None => {
                    refuse_vc_type(format!(
                        "internal.vcgen.slot_place_state: checked slot place `{}` has no owner-slot state",
                        place.render()
                    ));
                    None
                }
            };
        }
        if place.root() != "self" {
            refuse_vc_type(format!(
                "internal.vcgen.slot_place_shape: checked slot place `{}` is not a local root or direct `self` field",
                place.render()
            ));
            return None;
        }
        let Some(field) = place.direct_field() else {
            refuse_vc_type(format!(
                "internal.vcgen.slot_place_shape: checked slot place `{}` has an unsupported projection",
                place.render()
            ));
            return None;
        };
        match self.cctx {
            Cctx::Init(_) => match self.env.get(&format!("self.{field}")) {
                Some(Val::Slots(slots)) => Some(slots.clone()),
                Some(_) | None => {
                    refuse_vc_type(format!(
                        "internal.vcgen.slot_place_state: checked slot field `self.{field}` is not initialized as owner-slot state"
                    ));
                    None
                }
            },
            Cctx::Method(..) | Cctx::Deinit(_) => Some(project_field(&self.self_chain(), field)),
            Cctx::None => {
                refuse_vc_type(format!(
                    "internal.vcgen.slot_place_shape: `self.{field}` appears outside a class member"
                ));
                None
            }
        }
    }

    /// Consume the slot operation's explicit borrow expression while reading
    /// state from the exact checker-authored place. In an initializer,
    /// `self.field` lives in its own `self.field` environment entry until the
    /// final class literal exists; generic borrow projection through `self`
    /// would therefore observe a fictitious whole-object state.
    fn checked_slot_place_state(
        &mut self,
        expression: &Expr,
        place: &Place,
        scope: ScopeId,
    ) -> Option<String> {
        if !self.consume_expression_trap_sites(scope, expression) {
            return None;
        }
        let Some(borrowed) = BorrowedPlace::from_expr(expression) else {
            refuse_vc_type(format!(
                "internal.vcgen.slot_place_shape: `{}` is not retained as an explicit borrow",
                place.render()
            ));
            return None;
        };
        if borrowed.mutability() != Mutability::Mut || borrowed.place() != place {
            refuse_vc_type(format!(
                "internal.vcgen.slot_place_state_mismatch: explicit borrow disagrees with checked slot place `{}`",
                place.render()
            ));
            return None;
        }
        self.slot_place_str(place)
    }

    /// Atomically install a new owner-slot sequence at the exact checked
    /// place. Callers construct the complete `.set` term before invoking
    /// this helper, so no intermediate proof state can observe a taken value
    /// still present or a put value staged but not installed.
    fn write_slot_place(&mut self, place: &Place, slots: String) -> bool {
        if place.is_root() {
            self.env.insert(place.root().to_string(), Val::Slots(slots));
            return true;
        }
        if place.root() != "self" {
            refuse_vc_type(format!(
                "internal.vcgen.slot_place_shape: checked slot write `{}` is not a local root or direct `self` field",
                place.render()
            ));
            return false;
        }
        let Some(field) = place.direct_field() else {
            refuse_vc_type(format!(
                "internal.vcgen.slot_place_shape: checked slot write `{}` has an unsupported projection",
                place.render()
            ));
            return false;
        };
        match self.cctx {
            Cctx::Init(_) => {
                self.env.insert(format!("self.{field}"), Val::Slots(slots));
                true
            }
            Cctx::Method(..) | Cctx::Deinit(_) => {
                let base = self.self_chain();
                self.env.insert(
                    "self".to_string(),
                    Val::Obj(format!("{{ {base} with {field} := {slots} }}")),
                );
                true
            }
            Cctx::None => {
                refuse_vc_type(format!(
                    "internal.vcgen.slot_place_shape: `self.{field}` appears outside a class member"
                ));
                false
            }
        }
    }

    /// Give every symbolic visit to one immutable slot transition a distinct,
    /// typed theorem identity. Body-relative spans mirror call-havoc
    /// certificates while the explicit flavor component keeps the namespaces
    /// disjoint even when source names contain punctuation resembling one of
    /// the readable separators.
    fn slot_transition_certificate_names(
        &mut self,
        transition: &CheckedSlotTransition,
        operation: &str,
        place: &Place,
        symbolic_visit: usize,
    ) -> Option<(String, String)> {
        let Some(site_start) = transition.key.span.start.checked_sub(self.f.span.start) else {
            refuse_vc_type(format!(
                "internal.slot_transition_certificate_identity: `{operation}` span {}..{} precedes its {} body",
                transition.key.span.start,
                transition.key.span.end,
                self.call_owner.render()
            ));
            return None;
        };
        let Some(site_end) = transition.key.span.end.checked_sub(self.f.span.start) else {
            refuse_vc_type(format!(
                "internal.slot_transition_certificate_identity: `{operation}` span {}..{} precedes its {} body",
                transition.key.span.start,
                transition.key.span.end,
                self.call_owner.render()
            ));
            return None;
        };
        let owner = self.call_owner.certificate_component();
        let raw_place = place.render();
        let occurrence = format!("{site_start}:{site_end}");
        let visit = symbolic_visit.to_string();
        let name = format!(
            "transition.{owner}.{operation}.{raw_place}.site.{site_start}-{site_end}.visit.{symbolic_visit}"
        );
        let thm_name = injective_lean_components(
            "cert",
            &[
                "slot_transition",
                owner.as_str(),
                operation,
                raw_place.as_str(),
                occurrence.as_str(),
                visit.as_str(),
            ],
        );
        Some((name, thm_name))
    }

    fn slot_payload_term(&mut self, payload: &Ty, value: Val) -> Option<String> {
        match (payload, value) {
            (Ty::Bool, Val::Prop(prop)) => Some(lean_bool_value(&prop)),
            (Ty::Int(_) | Ty::Param(_), Val::Int(value)) => Some(value),
            (Ty::Record(_), Val::Record(value)) => Some(value),
            (Ty::Class(_), Val::Obj(value)) => Some(value),
            (
                Ty::Bool
                | Ty::Int(_)
                | Ty::Param(_)
                | Ty::Record(_)
                | Ty::Class(_)
                | Ty::Array(_)
                | Ty::Slots(_)
                | Ty::Option(_)
                | Ty::OptionRaw(_)
                | Ty::Res(_)
                | Ty::Raw(_)
                | Ty::RawRecord(_)
                | Ty::Borrow(..)
                | Ty::Unit,
                Val::Int(_)
                | Val::Prop(_)
                | Val::Opt(_)
                | Val::Arr(_)
                | Val::Slots(_)
                | Val::Obj(_)
                | Val::Record(_)
                | Val::View(_)
                | Val::Ptr(_)
                | Val::Unit,
            ) => {
                refuse_vc_type(format!(
                    "internal.vcgen.slot_payload_state: `{}` value has no matching symbolic slot payload",
                    payload.name()
                ));
                None
            }
        }
    }

    fn eval(&mut self, e: &Expr, scope: ScopeId) -> Val {
        if !self.consume_expression_trap_sites(scope, e) {
            return refused_expression_value(e);
        }
        self.eval_after_trap_lookup(e, scope)
    }

    /// Translate an expression whose direct source trap edge has already
    /// been consumed. Recursive calls go through [`Generator::eval`] (or
    /// [`Generator::eval_prop`]) so every child consumes its own direct site
    /// only when source evaluation reaches it.
    fn eval_after_trap_lookup(&mut self, e: &Expr, scope: ScopeId) -> Val {
        match &e.kind {
            ExprKind::SlotOp { op, args, .. } => {
                let Some((transition, action, symbolic_visit)) =
                    self.checked_slot_transition_action(scope, e)
                else {
                    return refused_expression_value(e);
                };
                let payload = transition.payload.clone();
                let payload_lean = lean_slot_payload_ty(&payload, self.classes, self.records);
                let site = slug(self.src(e.span));
                match op {
                    SlotOp::Alloc { .. } => {
                        let CheckedSlotTransitionKind::Alloc { .. } = transition.kind else {
                            unreachable!("slot allocation transition was exactly cross-validated")
                        };
                        let SlotActionKind::Alloc { .. } = action.kind() else {
                            unreachable!("slot allocation action was exactly cross-validated")
                        };
                        let hint = self.name_hint.take();
                        let Val::Int(length) = self.eval(&args[0], scope) else {
                            unreachable!("checked: owner-slot allocation length is u64")
                        };
                        let slots = self.hinted_sym("_slots", hint);
                        self.binders.push((
                            slots.clone(),
                            lean_slots_ty(&payload, self.classes, self.records),
                        ));
                        self.push_hyp_unique(
                            format!("h_{}_len", slots.trim_start_matches('_')),
                            format!("({slots}.len) = ({length})"),
                        );
                        self.push_hyp_unique(
                            format!("h_{}_all_none", slots.trim_start_matches('_')),
                            format!(
                                "∀ k, 0 ≤ k → k < ({slots}.len) → ({slots}.get k) = (none : Option {payload_lean})"
                            ),
                        );
                        self.push_slot_payload_facts(
                            &payload,
                            slots.trim_start_matches('_'),
                            &slots,
                        );
                        Val::Slots(slots)
                    }
                    SlotOp::Take => {
                        let CheckedSlotTransitionKind::Take { container, .. } = &transition.kind
                        else {
                            unreachable!("slot take transition was exactly cross-validated")
                        };
                        let container = container.clone();
                        let SlotActionKind::Take { .. } = action.kind() else {
                            unreachable!("slot take action was exactly cross-validated")
                        };
                        let hint = self.name_hint.take();
                        let Some(before) =
                            self.checked_slot_place_state(&args[0], &container, scope)
                        else {
                            return refused_expression_value(e);
                        };
                        let Val::Int(index) = self.eval(&args[1], scope) else {
                            unreachable!("checked: slot_take index is u64")
                        };
                        let bounds = format!("0 ≤ {index} ∧ {index} < ({before}.len)");
                        let ob = self.obligation(
                            &format!("{}.slot_take.bounds.{site}", self.fname),
                            format!(
                                "`slot_take` index must be in bounds for `{}`",
                                container.render()
                            ),
                            args[1].span,
                            bounds.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&bounds);
                        let occupied =
                            format!("({before}.get {index}) ≠ (none : Option {payload_lean})");
                        let ob = self.obligation(
                            &format!("{}.slot_take.occupied.{site}", self.fname),
                            format!(
                                "`slot_take` requires occupied storage in `{}`",
                                container.render()
                            ),
                            e.span,
                            occupied.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&occupied);

                        let taken = self.hinted_sym("_slot_take", hint);
                        let base = taken.trim_start_matches('_').to_string();
                        let value = self.fresh_state_for(&payload, &taken, &base, LenFact::Skip);
                        self.push_hyp_unique(
                            format!("h_{base}_taken"),
                            format!("({before}.get {index}) = some ({taken})"),
                        );
                        let updated =
                            format!("({before}.set {index} (none : Option {payload_lean}))");
                        if !self.write_slot_place(&container, updated.clone()) {
                            return refused_expression_value(e);
                        }
                        // Read the checked place back from the live environment.
                        // Reusing `updated` here would certify construction of a
                        // term, not that local/field write-back installed it.
                        let Some(observed) = self.slot_place_str(&container) else {
                            return refused_expression_value(e);
                        };
                        let Some((name, thm_name)) = self.slot_transition_certificate_names(
                            &transition,
                            "slot_take",
                            &container,
                            symbolic_visit,
                        ) else {
                            return refused_expression_value(e);
                        };
                        match TransitionCertificate::slot_take(
                            name,
                            thm_name,
                            transition,
                            action,
                            before,
                            observed,
                            index,
                            self.binders.clone(),
                        ) {
                            Ok(certificate) => self.out.transition_certificates.push(certificate),
                            Err(message) => {
                                refuse_vc_type(message);
                                return refused_expression_value(e);
                            }
                        }
                        self.push_slot_payload_facts(
                            &payload,
                            &format!("{}_take", container.binder_hint()),
                            &updated,
                        );
                        value
                    }
                    SlotOp::Put => {
                        let CheckedSlotTransitionKind::Put { container, .. } = &transition.kind
                        else {
                            unreachable!("slot put transition was exactly cross-validated")
                        };
                        let container = container.clone();
                        let SlotActionKind::Put {
                            value_transfer,
                            staging,
                            ..
                        } = action.kind().clone()
                        else {
                            unreachable!("slot put action was exactly cross-validated")
                        };
                        // Source order is container, index, then incoming
                        // value. The value is still staged before either
                        // guard, so a guard trap owns the staged payload via
                        // the retained terminal route, but an index expression
                        // may legally borrow that payload before the later
                        // move consumes it.
                        let Some(before) =
                            self.checked_slot_place_state(&args[0], &container, scope)
                        else {
                            return refused_expression_value(e);
                        };
                        let Val::Int(index) = self.eval(&args[1], scope) else {
                            unreachable!("checked: slot_put index is u64")
                        };
                        let evaluated = self.eval(&args[2], scope);
                        let _transfer = self.checked_value_transfer_key(&args[2], &value_transfer);
                        let Some(incoming) = self.slot_payload_term(&payload, evaluated) else {
                            return refused_expression_value(e);
                        };
                        let staging_name = self.hinted_sym(
                            "_slot_put_value",
                            Some(format!("_{}", sanitize(&staging.binder_hint()))),
                        );
                        self.binders
                            .push((staging_name.clone(), payload_lean.clone()));
                        self.push_hyp_unique(
                            format!("h_{}_staged", staging_name.trim_start_matches('_')),
                            format!("{staging_name} = ({incoming})"),
                        );

                        let bounds = format!("0 ≤ {index} ∧ {index} < ({before}.len)");
                        let ob = self.obligation(
                            &format!("{}.slot_put.bounds.{site}", self.fname),
                            format!(
                                "`slot_put` index must be in bounds for `{}`",
                                container.render()
                            ),
                            args[1].span,
                            bounds.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&bounds);
                        let empty =
                            format!("({before}.get {index}) = (none : Option {payload_lean})");
                        let ob = self.obligation(
                            &format!("{}.slot_put.empty.{site}", self.fname),
                            format!(
                                "`slot_put` requires empty storage in `{}`",
                                container.render()
                            ),
                            e.span,
                            empty.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&empty);

                        // Integer/record facts and, critically, every class
                        // invariant are proved for the exact staged value
                        // before its `some` state is made visible.
                        for (suffix, fact) in self.slot_payload_fact_props(&payload, &staging_name)
                        {
                            let ob = self.obligation(
                                &format!("{}.slot_put.payload.{suffix}.{site}", self.fname),
                                "staged slot payload must preserve its checked value facts".into(),
                                args[2].span,
                                fact.clone(),
                            );
                            self.push_obligation(ob);
                            self.assume_fact(&fact);
                        }
                        let updated = format!("({before}.set {index} (some ({staging_name})))");
                        if !self.write_slot_place(&container, updated.clone()) {
                            return refused_expression_value(e);
                        }
                        // The observed term comes from the environment after
                        // write-back, including direct `self` field projection.
                        let Some(observed) = self.slot_place_str(&container) else {
                            return refused_expression_value(e);
                        };
                        let Some((name, thm_name)) = self.slot_transition_certificate_names(
                            &transition,
                            "slot_put",
                            &container,
                            symbolic_visit,
                        ) else {
                            return refused_expression_value(e);
                        };
                        match TransitionCertificate::slot_put(
                            name,
                            thm_name,
                            transition,
                            action,
                            before,
                            observed,
                            index,
                            staging_name,
                            self.binders.clone(),
                        ) {
                            Ok(certificate) => self.out.transition_certificates.push(certificate),
                            Err(message) => {
                                refuse_vc_type(message);
                                return refused_expression_value(e);
                            }
                        }
                        self.push_slot_payload_facts(
                            &payload,
                            &format!("{}_put", container.binder_hint()),
                            &updated,
                        );
                        Val::Unit
                    }
                }
            }
            ExprKind::IntLit(n) => {
                let v = if *n < 0 {
                    format!("({n})")
                } else {
                    format!("{n}")
                };
                // A literal at type `T` cannot be range-checked
                // statically: emit a fits-VC against the model
                // (ADR 0009); dischargeable from `wf`/`requires`.
                if let Some(ty @ (Ty::Param(_) | Ty::Int(IntTy::TParam(_)))) = &e.ty {
                    let goal = self.r_prop(&v, adr0009_ty_int_model(ty.clone()));
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
                let container = match self.env.get(array) {
                    Some(Val::Arr(array)) | Some(Val::Slots(array)) => array.clone(),
                    Some(_) | None => unreachable!("checked: sequence container in scope"),
                };
                Val::Int(format!("({container}.len)"))
            }
            ExprKind::IsSome { operand } => {
                let Val::Opt(o) = self.eval(operand, scope) else {
                    unreachable!()
                };
                Val::Prop(format!("({o} ≠ none)"))
            }
            ExprKind::OptValue { operand } => {
                // Junk-on-none like `Seq.get` off-range; the someness VC
                // keeps verified code away from the junk (ADR 0008).
                let Val::Opt(o) = self.eval(operand, scope) else {
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
                match &e.ty {
                    Some(Ty::RawRecord(_)) => Val::Ptr(value),
                    Some(Ty::Bool) => Val::Prop(format!("({value} = true)")),
                    Some(Ty::Int(_) | Ty::Param(_)) => Val::Int(value),
                    // A nested payload's `.value` is itself an option chain.
                    Some(Ty::Option(_) | Ty::OptionRaw(_)) => Val::Opt(value),
                    // The affine `.value` is checked-refused (`.take` is the
                    // extraction), so a payload with no projection here is a
                    // named refusal, never a misbranded Int (ADR 0074).
                    Some(
                        Ty::Array(..)
                        | Ty::Slots(..)
                        | Ty::Class(_)
                        | Ty::Record(_)
                        | Ty::Res(_)
                        | Ty::Raw(_)
                        | Ty::Borrow(..)
                        | Ty::Unit,
                    )
                    | None => {
                        refuse_vc_type(format!(
                            "internal.vcgen.type_error: `.value` result has no symbolic \
                             projection for its type in {}",
                            self.fname
                        ));
                        Val::Unit
                    }
                }
            }
            ExprKind::OptTake {
                option,
                option_span,
            } => {
                let effect = self.checked_option_take(e, option, *option_span);
                if !effect.source.is_root() {
                    refuse_vc_type(format!(
                        "internal.vcgen.option_take_place: checked option take names unsupported projected place `{}`",
                        effect.source.render()
                    ));
                }
                let source = effect.source.root().to_string();
                // This is a single ownership transition in the symbolic
                // state: snapshot the old option, require presence, then
                // clear the source before handing the payload to the new
                // owned-array local. There is no intermediate environment
                // in which both names own the same sequence.
                let Val::Opt(old_option) = self
                    .env
                    .get(&source)
                    .cloned()
                    .expect("checked: affine-option take source is initialized")
                else {
                    unreachable!("checked: affine-option take source")
                };
                let goal = format!("({old_option}) ≠ none");
                let ob = self.obligation(
                    &format!("{}.option_take.{}", self.fname, slug(self.src(e.span))),
                    format!("`{}.take` must hold an owned value here", source),
                    effect.source_span.join(e.span),
                    goal.clone(),
                );
                self.push_obligation(ob);
                self.assume_fact(&goal);
                let payload = effect.payload;
                let reset = format!("(none : {})", lean_option_ty(&payload, self.classes));
                self.env.insert(source, Val::Opt(reset));
                match payload {
                    // The array payload has a spellable junk default, and
                    // the proven presence keeps every reader away from it.
                    Ty::Array(..) => Val::Arr(format!("(({old_option}).getD ⟨0, fun _ => false⟩)")),
                    // A class has no junk default to spell, so the taken
                    // value is a fresh binder pinned by the presence
                    // equation: it *is* the payload, and it carries the
                    // facts every checked class value carries — sound
                    // because every `some` was wrapped from a checked
                    // constructor or an invariant-carrying named local.
                    Ty::Class(ci) => {
                        self.fresh += 1;
                        let binder = format!("_taken{}", self.fresh);
                        let base = format!("taken{}", self.fresh);
                        let taken =
                            self.fresh_state_for(&Ty::Class(ci), &binder, &base, LenFact::Skip);
                        self.push_hyp_unique(
                            format!("h_{base}_eq"),
                            format!("({old_option}) = some ({binder})"),
                        );
                        taken
                    }
                    Ty::Int(_)
                    | Ty::Bool
                    | Ty::Param(_)
                    | Ty::Record(_)
                    | Ty::Slots(_)
                    | Ty::Option(_)
                    | Ty::OptionRaw(_)
                    | Ty::Res(_)
                    | Ty::Raw(_)
                    | Ty::RawRecord(_)
                    | Ty::Borrow(..)
                    | Ty::Unit => {
                        refuse_vc_type(format!(
                            "internal.vcgen.type_error: `.take` has no extraction model \
                             for this payload in {}",
                            self.fname
                        ));
                        Val::Unit
                    }
                }
            }
            ExprKind::Widen { arg, .. } => self.eval(arg, scope),
            ExprKind::Narrow { target, arg } => {
                let Val::Int(v) = self.eval(arg, scope) else {
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
                let evaluated = self.eval(inner, scope);
                if e.ty.as_ref().is_some_and(Ty::is_affine_option) {
                    let _transfer = self.checked_value_transfer(
                        inner,
                        crate::ownership::ValueTransferSink::OptionPayload,
                    );
                }
                let value = match evaluated {
                    Val::Int(v) | Val::Ptr(v) | Val::Arr(v) => v,
                    Val::Prop(p) => lean_bool_value(&p),
                    // A nested inner option is one chain; `some (...)`
                    // parenthesizes it below. A class payload's structure
                    // chain rides the same way.
                    Val::Opt(v) | Val::Obj(v) => v,
                    Val::Slots(_) | Val::View(_) | Val::Record(_) | Val::Unit => {
                        refuse_vc_type(format!(
                            "internal.vcgen.type_error: `some` payload has no symbolic \
                             value in {}",
                            self.fname
                        ));
                        "0".to_string()
                    }
                };
                Val::Opt(format!("some ({value})"))
            }
            ExprKind::NoneE => {
                let ty = match &e.ty {
                    Some(Ty::Option(element)) => lean_option_ty(element, self.classes),
                    Some(Ty::OptionRaw(_)) => "Option Sable.RawPtr".into(),
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
                    | None => unreachable!("checked: contextual none has an option type"),
                };
                Val::Opt(format!("(none : {ty})"))
            }
            // The raw operations. Every one carries a *pointer-names-byte*
            // premise instead of a global provenance predicate: same
            // allocation, offset lands inside the span. The resource
            // borrow beside it is what says the caller may touch it, and
            // that is a checker fact with no VC (ADR 0026).
            ExprKind::RawOp { op, args, .. } => {
                let hint = self.name_hint.take();
                let values: Vec<Val> = args
                    .iter()
                    .map(|argument| self.eval(argument, scope))
                    .collect();
                let checked = self.checked_sealed_operation(CheckedSealedTarget::Raw(*op), e, args);
                match op {
                    RawOp::Offset => {
                        let Val::Ptr(p) = values[0].clone() else {
                            unreachable!("checked: raw<u8>")
                        };
                        let Val::Int(d) = values[1].clone() else {
                            unreachable!("checked: u64")
                        };
                        Val::Ptr(format!("(Sable.RawPtr.add {p} {d})"))
                    }
                    RawOp::CastRecord(_) => {
                        let Val::Ptr(p) = values[0].clone() else {
                            unreachable!("checked: raw<u8>")
                        };
                        Val::Ptr(p)
                    }
                    RawOp::PointerOffsetRecord(_) => {
                        let Val::Ptr(p) = values[0].clone() else {
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
                        let Val::Ptr(p) = values[0].clone() else {
                            unreachable!("checked: raw<u8>")
                        };
                        let Val::View(m) = values[1].clone() else {
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
                        let Val::Ptr(p) = values[0].clone() else {
                            unreachable!("checked: raw<u8>")
                        };
                        let Val::Int(w) = values[1].clone() else {
                            unreachable!("checked: u8")
                        };
                        let Val::View(m) = values[2].clone() else {
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
                        let mname = sealed_borrow_root(&checked, 2);
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
                        let Val::Ptr(sp) = values[0].clone() else {
                            unreachable!("checked: raw<u8>")
                        };
                        let Val::Ptr(dp) = values[1].clone() else {
                            unreachable!("checked: raw<u8>")
                        };
                        let Val::Int(n) = values[2].clone() else {
                            unreachable!("checked: u64")
                        };
                        let Val::View(sm) = values[3].clone() else {
                            unreachable!("checked: span borrow")
                        };
                        let Val::View(dm) = values[4].clone() else {
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
                        let dname = sealed_borrow_root(&checked, 4);
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
                        let Val::Ptr(p) = values[0].clone() else {
                            unreachable!("checked: raw<u8>")
                        };
                        let Val::View(m) = values[1].clone() else {
                            unreachable!("checked: span value")
                        };
                        let leased =
                            matches!(sealed_resource_kind(&checked, 1), Some(ResKind::BlockLease));
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
                        let Val::Ptr(p) = values[0].clone() else {
                            unreachable!("checked: raw<u8>")
                        };
                        let Val::View(c) = values[1].clone() else {
                            unreachable!("checked: cell value")
                        };
                        let leased = matches!(
                            sealed_resource_kind(&checked, 1),
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
                        let Val::Ptr(p) = values[0].clone() else {
                            unreachable!("checked: raw<u8>")
                        };
                        let Val::Int(w) = values[1].clone() else {
                            unreachable!("checked: u64")
                        };
                        let Val::View(c) = values[2].clone() else {
                            unreachable!("checked: cell borrow")
                        };
                        let leased = matches!(
                            sealed_resource_kind(&checked, 2),
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
                        let name = sealed_borrow_root(&checked, 2);
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
                        let Val::Ptr(p) = values[0].clone() else {
                            unreachable!("checked: raw<u8>")
                        };
                        let Val::View(c) = values[1].clone() else {
                            unreachable!("checked: cell borrow")
                        };
                        let leased = matches!(
                            sealed_resource_kind(&checked, 1),
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
                            let name = sealed_borrow_root(&checked, 1);
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
                        let Val::Ptr(p) = values[0].clone() else {
                            unreachable!("checked: raw<u8>")
                        };
                        let Val::View(c) = values[1].clone() else {
                            unreachable!("checked: cell borrow")
                        };
                        let leased = matches!(
                            sealed_resource_kind(&checked, 1),
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
                        let name = sealed_borrow_root(&checked, 1);
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
                        let Val::Ptr(p) = values[0].clone() else {
                            unreachable!("checked: raw record pointer")
                        };
                        let Val::View(bytes) = values[1].clone() else {
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
                        let Val::Ptr(p) = values[0].clone() else {
                            unreachable!("checked: raw record pointer")
                        };
                        let Val::View(cell) = values[1].clone() else {
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
                        let Val::Ptr(p) = values[0].clone() else {
                            unreachable!("checked: raw record pointer")
                        };
                        let Val::Record(value) = values[1].clone() else {
                            unreachable!("checked: record value")
                        };
                        let Val::View(cell) = values[2].clone() else {
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
                        let name = sealed_borrow_root(&checked, 2);
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
                        let Val::Ptr(p) = values[0].clone() else {
                            unreachable!("checked: raw record pointer")
                        };
                        let Val::View(cell) = values[1].clone() else {
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
                            let name = sealed_borrow_root(&checked, 1);
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
                        let Val::Ptr(p) = values[0].clone() else {
                            unreachable!("checked: raw record pointer")
                        };
                        let Val::View(cell) = values[1].clone() else {
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
                        let name = sealed_borrow_root(&checked, 1);
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
                        let Val::Ptr(p) = values[0].clone() else {
                            unreachable!("checked: raw<u8>")
                        };
                        let Val::View(block) = values[1].clone() else {
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
                        let Val::Ptr(p) = values[0].clone() else {
                            unreachable!("checked: raw<u8>")
                        };
                        let Val::View(header) = values[1].clone() else {
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
                        let Val::Ptr(p) = values[0].clone() else {
                            unreachable!("checked: raw<u8>")
                        };
                        let Val::Int(size) = values[1].clone() else {
                            unreachable!("checked: u64 size")
                        };
                        let Val::Int(next) = values[2].clone() else {
                            unreachable!("checked: u64 next")
                        };
                        let Val::View(header) = values[3].clone() else {
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
                        let name = sealed_borrow_root(&checked, 3);
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
                        let Val::Ptr(p) = values[0].clone() else {
                            unreachable!("checked: raw<u8>")
                        };
                        let Val::View(header) = values[1].clone() else {
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
                        let Val::Ptr(p) = values[0].clone() else {
                            unreachable!("checked: raw<u8>")
                        };
                        let Val::View(header) = values[1].clone() else {
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
                        let name = sealed_borrow_root(&checked, 1);
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
                let values: Vec<Val> = args
                    .iter()
                    .map(|argument| self.eval(argument, scope))
                    .collect();
                let checked =
                    self.checked_sealed_operation(CheckedSealedTarget::Device(*op), e, args);
                match op {
                    DeviceOp::UartStatus => {
                        let Val::View(old) = values[0].clone() else {
                            unreachable!("checked: UART borrow")
                        };
                        let name = sealed_borrow_root(&checked, 0);
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
                        let Val::Int(byte) = values[0].clone() else {
                            unreachable!("checked: UART byte")
                        };
                        let Val::View(old) = values[1].clone() else {
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
                        let name = sealed_borrow_root(&checked, 1);
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
                let values: Vec<Val> = args
                    .iter()
                    .map(|argument| self.eval(argument, scope))
                    .collect();
                let checked =
                    self.checked_sealed_operation(CheckedSealedTarget::Resource(*op), e, args);
                match op {
                    // `split_off(&mut whole, n)`: the prefix stays, the
                    // suffix leaves. `whole` is rebound to the prefix
                    // view, exactly as any `&mut` argument is rebound.
                    ResOp::SplitOff => {
                        let Val::View(whole) = values[0].clone() else {
                            unreachable!("checked: span borrow")
                        };
                        let Val::Int(n) = values[1].clone() else {
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
                        let array = sealed_borrow_root(&checked, 0);
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
                        let Val::View(a) = values[0].clone() else {
                            unreachable!("checked: span value")
                        };
                        let Val::View(b) = values[1].clone() else {
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
                        let Val::View(w) = values[0].clone() else {
                            unreachable!("checked: world borrow")
                        };
                        let Val::Int(fd) = values[1].clone() else {
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
                        let array = sealed_borrow_root(&checked, 0);
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
                        let Val::Int(_script) = values[0].clone() else {
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
                        let Val::Int(_script) = values[0].clone() else {
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
                        let Ty::Res(
                            map_kind @ (ResKind::ResourceMapPointsToU64
                            | ResKind::ResourceMapPointsToRecord(_)),
                        ) = &checked.result_ty
                        else {
                            unreachable!("checked: resource-map result type")
                        };
                        let map_kind = *map_kind;
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
                        ) = sealed_resource_kind(&checked, 0)
                        else {
                            unreachable!("checked: resource-map borrow")
                        };
                        let cell_kind = match map_kind {
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
                        };
                        let Val::View(map) = values[0].clone() else {
                            unreachable!("checked: resource map borrow")
                        };
                        let Val::Int(key) = values[1].clone() else {
                            unreachable!("checked: u64 key")
                        };
                        let goal = match map_kind {
                            ResKind::ResourceMapPointsToU64 => {
                                format!("Sable.ResourceMapView.canTakeU64 ({map}) {key}")
                            }
                            ResKind::ResourceMapPointsToRecord(_) => {
                                format!("∃ cell, ({map}).entries {key} = some cell")
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
                            | ResKind::FreeHeader => unreachable!(),
                        };
                        let ob = self.obligation(
                            &format!("{}.resource_map_take.{}", self.fname, slug(&key)),
                            "`resource_map_take` needs a stored entry at this key".into(),
                            e.span,
                            goal.clone(),
                        );
                        self.push_obligation(ob);
                        self.assume_fact(&goal);
                        let array = sealed_borrow_root(&checked, 0);
                        let residual = self.hinted_sym("_resource_map", Some(array.clone()));
                        self.binders
                            .push((residual.clone(), lean_res_view_ty(map_kind, self.records)));
                        self.push_hyp_unique(
                            format!("h_{array}_take"),
                            format!("{residual} = Sable.ResourceMapView.erase ({map}) {key}"),
                        );
                        for (h, prop) in view_wf_hyps(map_kind, &array, &residual, self.records) {
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
                        ) = sealed_resource_kind(&checked, 0)
                        else {
                            unreachable!("checked: resource-map borrow")
                        };
                        let Val::View(map) = values[0].clone() else {
                            unreachable!("checked: resource map borrow")
                        };
                        let Val::Int(key) = values[1].clone() else {
                            unreachable!("checked: u64 key")
                        };
                        let Val::View(cell) = values[2].clone() else {
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
                        let array = sealed_borrow_root(&checked, 0);
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
                        for (h, prop) in view_wf_hyps(map_kind, &array, &restored, self.records) {
                            self.push_hyp_unique(h, prop);
                        }
                        self.env.insert(array.clone(), Val::View(restored));
                        Val::Unit
                    }
                    ResOp::AllocatorCreate => {
                        let Val::View(root) = values[0].clone() else {
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
                        let Val::View(state) = values[0].clone() else {
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
                        let Val::View(state) = values[0].clone() else {
                            unreachable!("checked: allocator state borrow")
                        };
                        let Val::Int(key) = values[1].clone() else {
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
                        let array = sealed_borrow_root(&checked, 0);
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
                        let Val::View(state) = values[0].clone() else {
                            unreachable!("checked: allocator state borrow")
                        };
                        let Val::View(lease) = values[1].clone() else {
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
                        let array = sealed_borrow_root(&checked, 0);
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
                        let Val::View(state) = values[0].clone() else {
                            unreachable!("checked: allocator state borrow")
                        };
                        let Val::Int(key) = values[1].clone() else {
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
                        let array = sealed_borrow_root(&checked, 0);
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
                        let Val::View(state) = values[0].clone() else {
                            unreachable!("checked: allocator state borrow")
                        };
                        let Val::View(block) = values[1].clone() else {
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
                        let array = sealed_borrow_root(&checked, 0);
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
                        let Val::View(state) = values[0].clone() else {
                            unreachable!("checked: allocator state borrow")
                        };
                        let Val::Int(key) = values[1].clone() else {
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
                        let array = sealed_borrow_root(&checked, 0);
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
                        let Val::View(state) = values[0].clone() else {
                            unreachable!("checked: allocator state borrow")
                        };
                        let Val::Int(limit) = values[1].clone() else {
                            unreachable!("checked: u64 limit")
                        };
                        let Val::Int(key) = values[2].clone() else {
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
                        let array = sealed_borrow_root(&checked, 0);
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
                        let Val::View(state) = values[0].clone() else {
                            unreachable!("checked: allocator state borrow")
                        };
                        let Val::View(header) = values[1].clone() else {
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
                        let array = sealed_borrow_root(&checked, 0);
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
                        let Val::View(block) = values[0].clone() else {
                            unreachable!("checked: free block borrow")
                        };
                        let Val::Int(n) = values[1].clone() else {
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
                        let array = sealed_borrow_root(&checked, 0);
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
                        let Val::View(left) = values[0].clone() else {
                            unreachable!("checked: free block value")
                        };
                        let Val::View(right) = values[1].clone() else {
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
                        let Val::View(block) = values[0].clone() else {
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
                        let Val::View(lease) = values[0].clone() else {
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
                    Some(
                        Val::Int(_)
                        | Val::Prop(_)
                        | Val::Opt(_)
                        | Val::Arr(_)
                        | Val::Slots(_)
                        | Val::Record(_)
                        | Val::View(_)
                        | Val::Ptr(_)
                        | Val::Unit,
                    )
                    | None => None,
                };
                // A field borrow names the field's own place; whether
                // that place is an object or an array is what the
                // checker recorded on the expression (ADR 0020).
                let place = |v: String| match &e.ty {
                    Some(ty) => {
                        if checked_array_payload(ty).is_some() {
                            Val::Arr(v)
                        } else if matches!(ty.referent(), Ty::Slots(_)) {
                            Val::Slots(v)
                        } else {
                            Val::Obj(v)
                        }
                    }
                    None => Val::Obj(v),
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
                            Some(
                                Val::Int(_)
                                | Val::Prop(_)
                                | Val::Opt(_)
                                | Val::Arr(_)
                                | Val::Slots(_)
                                | Val::Record(_)
                                | Val::View(_)
                                | Val::Ptr(_)
                                | Val::Unit,
                            )
                            | None => "self".to_string(),
                        };
                        place(project_field(&selfv, f))
                    }
                    (None, None)
                        if matches!(e.ty.as_ref().map(Ty::referent), Some(Ty::Slots(_))) =>
                    {
                        Val::Slots(self.slots_str(array))
                    }
                    (None, None) => Val::Arr(self.arr_str(array)),
                }
            }
            ExprKind::ArrayLit(elems) => {
                let hint = self.name_hint.take();
                let b = self.hinted_sym("_lit", hint);
                let Some(Ty::Array(ref element)) = e.ty else {
                    unreachable!("checked: array literal has an array type")
                };
                self.binders
                    .push((b.clone(), lean_array_ty(&(*element).clone(), self.records)));
                let h1 = self.fresh_hyp("h_lit");
                self.hyps.push((h1, format!("({b}.len) = {}", elems.len())));
                for (i, el) in elems.iter().enumerate() {
                    let v = checked_array_payload_value(element, self.eval(el, scope), |payload| {
                        format!(
                            "internal.vcgen.lean_type_unsupported: array literal element \
                                 `{}` has no proof value",
                            payload.name()
                        )
                    });
                    let h = self.fresh_hyp("h_lit");
                    self.hyps.push((h, format!("{b}.get {i} = {v}")));
                }
                Val::Arr(b)
            }
            ExprKind::Index { array, index, .. } => {
                let Val::Int(i) = self.eval(index, scope) else {
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
                match e.ty.clone().expect("checked: array index type") {
                    Ty::Bool => Val::Prop(format!("({value} = true)")),
                    ty @ (Ty::Int(_) | Ty::Param(_)) => {
                        // Element range follows from the array's element fact
                        // plus the just-proven bounds; assuming it here saves
                        // the automation a quantifier instantiation.
                        let range = self.r_prop(&value, adr0009_ty_int_model(ty));
                        self.assume_fact(&range);
                        Val::Int(value)
                    }
                    Ty::Record(ri) => {
                        // Element well-formedness follows the same way from
                        // the array's elementwise fact.
                        let wf = format!("{}.wf {value}", lean_record_name(&self.records[ri].name));
                        self.assume_fact(&wf);
                        Val::Record(value)
                    }
                    other @ (Ty::Class(_)
                    | Ty::Array(_)
                    | Ty::Slots(_)
                    | Ty::Option(_)
                    | Ty::OptionRaw(_)
                    | Ty::Res(_)
                    | Ty::Raw(_)
                    | Ty::RawRecord(_)
                    | Ty::Borrow(..)
                    | Ty::Unit) => {
                        refuse_vc_type(format!(
                            "internal.vcgen.lean_type_unsupported: array element `{}` has no \
                             proof value",
                            other.name()
                        ));
                        Val::Int(UNSUPPORTED_LEAN_VALUE.into())
                    }
                }
            }
            ExprKind::AllocArray { elem, len, init } => {
                let hint = self.name_hint.take();
                let Val::Int(n) = self.eval(len, scope) else {
                    unreachable!()
                };
                let v0 = checked_array_payload_value(elem, self.eval(init, scope), |payload| {
                    format!(
                        "internal.vcgen.lean_type_unsupported: array allocation initializer \
                             `{}` has no proof value",
                        payload.name()
                    )
                });
                // Allocation succeeds symbolically: failure is the named
                // OOM trap (design §10), not a proof obligation.
                let b = self.hinted_sym("_alloc", hint);
                self.binders
                    .push((b.clone(), lean_array_ty(elem, self.records)));
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
                let projected = project_field(&chain, field);
                match &e.ty {
                    Some(Ty::Bool) => Val::Prop(format!("({projected} = true)")),
                    Some(Ty::Int(_) | Ty::Param(_)) => Val::Int(projected),
                    // A field type with no symbolic projection is a named
                    // refusal, never a bare Int (ADR 0074).
                    Some(
                        Ty::Res(_)
                        | Ty::Class(_)
                        | Ty::Record(_)
                        | Ty::Array(..)
                        | Ty::Slots(..)
                        | Ty::Option(_)
                        | Ty::OptionRaw(_)
                        | Ty::Raw(_)
                        | Ty::RawRecord(_)
                        | Ty::Borrow(..)
                        | Ty::Unit,
                    )
                    | None => {
                        refuse_vc_type(format!(
                            "internal.vcgen.field_state_unsupported: `{obj}.{field}` has \
                             no symbolic field state for its type"
                        ));
                        Val::Unit
                    }
                }
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
                    Some(
                        Ty::Bool
                        | Ty::Param(_)
                        | Ty::Class(_)
                        | Ty::Record(_)
                        | Ty::Array(_)
                        | Ty::Slots(_)
                        | Ty::Option(_)
                        | Ty::Res(_)
                        | Ty::Raw(_)
                        | Ty::Borrow(..)
                        | Ty::Unit,
                    )
                    | None => unreachable!("checked: initial record field type"),
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
                let Val::Int(i) = self.eval(index, scope) else {
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
                let value = format!("({arr}.get {i})");
                match &e.ty {
                    Some(Ty::Bool) => Val::Prop(format!("({value} = true)")),
                    Some(Ty::Int(_) | Ty::Param(_)) => Val::Int(value),
                    Some(Ty::Record(ri)) => {
                        let wf =
                            format!("{}.wf {value}", lean_record_name(&self.records[*ri].name));
                        self.assume_fact(&wf);
                        Val::Record(value)
                    }
                    Some(
                        Ty::Class(_)
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
                        refuse_vc_type(format!(
                            "internal.vcgen.field_state_unsupported: `{obj}.{field}[..]` has \
                             no symbolic element value for its type"
                        ));
                        Val::Unit
                    }
                }
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
                    match e.ty.as_ref().map(Ty::referent) {
                        Some(Ty::Res(_)) => Val::View(projected),
                        Some(Ty::Class(_)) => Val::Obj(projected),
                        Some(Ty::Raw(_) | Ty::RawRecord(_)) => Val::Ptr(projected),
                        Some(Ty::Array(..)) => Val::Arr(projected),
                        Some(Ty::Slots(..)) => Val::Slots(projected),
                        Some(Ty::Bool) => Val::Prop(format!("({projected} = true)")),
                        Some(Ty::Int(_) | Ty::Param(_)) => Val::Int(projected),
                        // A copyable option field projects as its chain,
                        // with the accessor and match surface any option
                        // value has.
                        Some(Ty::Option(_)) => Val::Opt(projected),
                        // A field type with no symbolic projection is a
                        // named refusal, never a bare Int (ADR 0074).
                        Some(Ty::Record(_) | Ty::OptionRaw(_) | Ty::Borrow(..) | Ty::Unit)
                        | None => {
                            refuse_vc_type(format!(
                                "internal.vcgen.field_state_unsupported: `self.{field}` \
                                 has no symbolic field state for its type"
                            ));
                            Val::Unit
                        }
                    }
                }
                Cctx::None => unreachable!("checked: fields only in members"),
            },
            ExprKind::SelfFieldLen { field } => {
                let arr = self.self_field_str(field);
                Val::Int(format!("({arr}.len)"))
            }
            ExprKind::SelfFieldIndex { field, index } => {
                let Val::Int(i) = self.eval(index, scope) else {
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
                match e.ty.clone().expect("checked: field index type") {
                    Ty::Bool => Val::Prop(format!("({value} = true)")),
                    ty @ (Ty::Int(_) | Ty::Param(_)) => {
                        let range = self.r_prop(&value, adr0009_ty_int_model(ty));
                        self.assume_fact(&range);
                        Val::Int(value)
                    }
                    // Element well-formedness follows from the field's
                    // elementwise fact plus the just-proven bounds.
                    Ty::Record(ri) => {
                        let wf = format!("{}.wf {value}", lean_record_name(&self.records[ri].name));
                        self.assume_fact(&wf);
                        Val::Record(value)
                    }
                    Ty::Class(_)
                    | Ty::Array(_)
                    | Ty::Slots(_)
                    | Ty::Option(_)
                    | Ty::OptionRaw(_)
                    | Ty::Res(_)
                    | Ty::Raw(_)
                    | Ty::RawRecord(_)
                    | Ty::Borrow(..)
                    | Ty::Unit => {
                        refuse_vc_type(format!(
                            "internal.vcgen.field_state_unsupported: `self.{field}[..]` has \
                             no symbolic element value for its type"
                        ));
                        Val::Unit
                    }
                }
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
                    .map(|a| {
                        match self.eval(a, scope) {
                            // Class args (by value or borrowed) substitute
                            // as their symbolic structure value (ADR 0020).
                            Val::Int(v) | Val::Arr(v) | Val::Obj(v) | Val::View(v) => v,
                            // Parenthesized as at a function call: dot-notation
                            // in the init's clauses must bind the whole chain.
                            Val::Opt(v) => format!("({v})"),
                            Val::Prop(p) => lean_bool_value(&p),
                            Val::Slots(_) | Val::Record(_) | Val::Ptr(_) | Val::Unit => {
                                unreachable!("checked: ctor args")
                            }
                        }
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
                    // `old p` of a `&mut` argument is its pre-call state —
                    // one question, one pattern, for every referent a unique
                    // borrow can name (ADR 0074).
                    if p.ty.is_unique_borrow() {
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
                let (checked_call, symbolic_visit) = self.checked_call(
                    CallTarget::Constructor {
                        class: class.clone(),
                        init: init.clone(),
                    },
                    e.span,
                    &iparams,
                    args,
                    None,
                );
                for (pname, fresh) in self.havoc_mut_borrow_args(&checked_call, symbolic_visit) {
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
                    .map(|arg| match self.eval(arg, scope) {
                        Val::Int(v) | Val::Opt(v) | Val::Ptr(v) => format!("({v})"),
                        Val::Prop(_)
                        | Val::Arr(_)
                        | Val::Slots(_)
                        | Val::Obj(_)
                        | Val::Record(_)
                        | Val::View(_)
                        | Val::Unit => {
                            unreachable!("checked: raw-storable record field")
                        }
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
                        let Val::Int(v) = self.eval(a, scope) else {
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
                match &m.ret {
                    ty @ (Ty::Int(_) | Ty::Param(_)) => {
                        self.binders.push((ret_sym.clone(), "Int".into()));
                        let model = adr0009_ty_int_model(ty.clone());
                        let is_trait_self = matches!(ty, Ty::Int(IntTy::TParam(0)))
                            || matches!(ty, Ty::Param(parameter) if parameter.index() == 0);
                        let range = if is_trait_self {
                            format!("{param}.min ≤ {ret_sym} ∧ {ret_sym} ≤ {param}.max")
                        } else {
                            self.r_prop(&ret_sym, model)
                        };
                        self.hyps.push((
                            format!("h_{}_range", ret_sym.trim_start_matches('_')),
                            range,
                        ));
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
                    | Ty::Unit => unreachable!("trait methods return integers for now"),
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
                recv,
                recv_span,
                method,
                args,
                ..
            } => {
                let hint = self.name_hint.take();
                let arg_vals: Vec<String> = args
                    .iter()
                    .map(|a| {
                        match self.eval(a, scope) {
                            Val::Int(v)
                            | Val::Arr(v)
                            | Val::Obj(v)
                            | Val::View(v)
                            | Val::Ptr(v) => v,
                            // Parenthesized as at a function call: dot-notation
                            // in the callee's clauses must bind the whole chain.
                            Val::Opt(v) => format!("({v})"),
                            // Program booleans are propositions in symbolic
                            // execution, while source parameters bind Lean Bool;
                            // reify at the call boundary as at a function call.
                            Val::Prop(p) => lean_bool_value(&p),
                            Val::Slots(_) | Val::Record(_) | Val::Unit => unreachable!(
                                "checked: int/bool/option/array/class/resource/pointer args"
                            ),
                        }
                    })
                    .collect();
                let Some(ci) = self.var_tys.get(recv.as_str()).and_then(Ty::class_index) else {
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
                    Some(
                        Val::Int(_)
                        | Val::Prop(_)
                        | Val::Opt(_)
                        | Val::Arr(_)
                        | Val::Slots(_)
                        | Val::Record(_)
                        | Val::View(_)
                        | Val::Ptr(_)
                        | Val::Unit,
                    )
                    | None => unreachable!("checked: class value"),
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
                let (checked_call, symbolic_visit) = self.checked_call(
                    CallTarget::Method {
                        class: cd.name.clone(),
                        method: method.clone(),
                    },
                    e.span,
                    &mparams,
                    args,
                    Some((
                        cd.name.as_str(),
                        Place::local(recv),
                        if m.self_kind == SelfKind::Mut {
                            Mutability::Mut
                        } else {
                            Mutability::Shared
                        },
                        *recv_span,
                        Ty::Class(ci),
                    )),
                );
                let receiver_effect = checked_call.receiver.as_ref().map(|r| r.transition.effect);
                // The checker-authored receiver loan decides whether caller
                // state changes; the method signature above is only the exact
                // match that rejects a stale or forged handoff.
                let final_state = if receiver_effect == Some(CallEffect::HavocUniqueBorrow) {
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
                let ret_val = self.bind_call_result(&m.f.ret, &ret_sym, CallResultSite::Member);
                let fresh_args = self.havoc_mut_borrow_args(&checked_call, symbolic_visit);
                let cd = &self.classes[ci];
                let m = cd
                    .methods
                    .iter()
                    .find(|m| m.f.name == *method)
                    .expect("checked: method exists");
                let mut post_map = self.class_state_map(cd, &final_state);
                for (p, a) in m.f.params.iter().zip(arg_vals.iter()) {
                    post_map.insert(p.name.clone(), a.clone());
                    // `old p` of a `&mut` argument is its pre-call state —
                    // one question, one pattern, for every referent a unique
                    // borrow can name (ADR 0074).
                    if p.ty.is_unique_borrow() {
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
                // Same payload fact as `fresh_state_for`, emitted after the
                // posts for the same motive-capture reason as the free call.
                if let Ty::Option(element) = &m.f.ret.clone() {
                    let base = ret_sym.trim_start_matches('_').to_string();
                    self.push_option_value_facts(element, &base, &ret_sym);
                }
                ret_val
            }
            ExprKind::Unary { op, operand } => match op {
                UnOp::Neg => {
                    let Val::Int(v) = self.eval(operand, scope) else {
                        unreachable!()
                    };
                    let value = format!("(-{v})");
                    let it =
                        adr0009_ty_int_model(e.ty.clone().expect("checked: negation result type"));
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
                    let p = self.eval_prop(operand, scope);
                    Val::Prop(format!("¬{p}"))
                }
            },
            ExprKind::Binary { op, lhs, rhs, .. } => {
                if op.is_arith() {
                    let Val::Int(l) = self.eval(lhs, scope) else {
                        unreachable!()
                    };
                    let Val::Int(r) = self.eval(rhs, scope) else {
                        unreachable!()
                    };
                    let lean_op = match op {
                        BinOp::Add => "+",
                        BinOp::Sub => "-",
                        BinOp::Mul => "*",
                        BinOp::Div => "/",
                        BinOp::Rem => "%",
                        BinOp::Lt
                        | BinOp::Le
                        | BinOp::Gt
                        | BinOp::Ge
                        | BinOp::Eq
                        | BinOp::Ne
                        | BinOp::And
                        | BinOp::Or => unreachable!(),
                    };
                    let value = format!("({l} {lean_op} {r})");
                    let it = adr0009_ty_int_model(
                        e.ty.clone().expect("checked: arithmetic result type"),
                    );
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
                        BinOp::Lt
                        | BinOp::Le
                        | BinOp::Gt
                        | BinOp::Ge
                        | BinOp::Eq
                        | BinOp::Ne
                        | BinOp::And
                        | BinOp::Or => unreachable!(),
                    }
                    Val::Int(value)
                } else {
                    Val::Prop(self.eval_prop_after_trap_lookup(e, scope))
                }
            }
            ExprKind::Call { callee, args, .. } => {
                let hint = self.name_hint.take();
                let params = self.sigs[callee.as_str()].params.clone();
                let arg_vals: Vec<String> = args
                    .iter()
                    .zip(&params)
                    .map(|(a, parameter)| match self.eval(a, scope) {
                        Val::Int(v)
                        | Val::Arr(v)
                        | Val::Obj(v)
                        | Val::Record(v)
                        | Val::View(v)
                        | Val::Ptr(v) => v,
                        // An option argument substitutes as its whole chain,
                        // parenthesized so dot-notation in the callee's
                        // clauses binds to the chain: `(some (7)).is_some`,
                        // never `some ((7).is_some)`.
                        Val::Opt(v) => format!("({v})"),
                        // Program booleans are propositions in symbolic
                        // execution, while source parameters bind Lean Bool.
                        // Reify at the exact call boundary before substituting
                        // the callee's pre/post/variant clauses.
                        Val::Prop(p) if parameter.ty == Ty::Bool => lean_bool_value(&p),
                        Val::Prop(_) => {
                            unreachable!("checked: a proposition argument has a Bool parameter")
                        }
                        Val::Slots(_) => {
                            unreachable!(
                                "checked: owner-slot containers cannot cross call boundaries"
                            )
                        }
                        Val::Unit => unreachable!(
                            "checked: int/bool/option/array/class/record/resource/pointer args"
                        ),
                    })
                    .collect();
                let callee_fn = self.fn_map[callee.as_str()];
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
                    // One question, one pattern: a unique borrow is the only
                    // type through which a callee can change storage the
                    // caller still names, so it is the only one with an
                    // entry-state twin.
                    if p.ty.is_unique_borrow() {
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

                // Every `&mut` argument — array, class, or resource — comes
                // back in a FRESH state through the one call-site havoc
                // (ADR 0074): the callee may have mutated it arbitrarily
                // within its posts, and omitting the havoc asserts those
                // posts over the pre-call state.
                let (checked_call, symbolic_visit) = self.checked_call(
                    CallTarget::Function(callee.clone()),
                    e.span,
                    &params,
                    args,
                    None,
                );
                for (pname, fresh) in self.havoc_mut_borrow_args(&checked_call, symbolic_visit) {
                    subst_map.insert(pname, fresh);
                }
                let sig = &self.sigs[callee.as_str()];

                let ret_sym = self.hinted_sym("_r", hint);
                let ret_val = self.bind_call_result(&sig.ret, &ret_sym, CallResultSite::Function);
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
                // The payload fact every fresh option state carries
                // (`fresh_state_for`): an integer leaf's `.value` is in
                // range whether present or junk-on-none. Emitted after the
                // callee's posts, so a `match`-shaped post's motive does not
                // capture it and user scripts can case on the result.
                if let Ty::Option(element) = &sig.ret.clone() {
                    let base = ret_sym.trim_start_matches('_').to_string();
                    self.push_option_value_facts(element, &base, &ret_sym);
                }
                ret_val
            }
        }
    }

    fn eval_prop(&mut self, e: &Expr, scope: ScopeId) -> String {
        if !self.consume_expression_trap_sites(scope, e) {
            return "False".into();
        }
        self.eval_prop_after_trap_lookup(e, scope)
    }

    /// Proposition translation after the current expression's direct trap
    /// edge has been consumed. The fallback invokes the expression translator
    /// below that same seam so Boolean calls and projections do not consume
    /// one source site twice.
    fn eval_prop_after_trap_lookup(&mut self, e: &Expr, scope: ScopeId) -> String {
        match &e.kind {
            ExprKind::SlotOp { op, .. } => {
                refuse_vc_type(format!(
                    "internal.vcgen.slots_unsupported: `{}` has no proposition semantics",
                    op.name()
                ));
                "False".into()
            }
            ExprKind::BoolLit(b) => if *b { "True" } else { "False" }.to_string(),
            ExprKind::Var(_) => {
                let Val::Prop(p) = self.eval_after_trap_lookup(e, scope) else {
                    unreachable!()
                };
                p
            }
            ExprKind::Unary {
                op: UnOp::Not,
                operand,
            } => format!("¬{}", self.eval_prop(operand, scope)),
            ExprKind::Binary { op, lhs, rhs, .. } if op.is_comparison() => {
                let Val::Int(l) = self.eval(lhs, scope) else {
                    unreachable!()
                };
                let Val::Int(r) = self.eval(rhs, scope) else {
                    unreachable!()
                };
                let sym = match op {
                    BinOp::Lt => "<",
                    BinOp::Le => "≤",
                    BinOp::Gt => ">",
                    BinOp::Ge => "≥",
                    BinOp::Eq => "=",
                    BinOp::Ne => "≠",
                    BinOp::Add
                    | BinOp::Sub
                    | BinOp::Mul
                    | BinOp::Div
                    | BinOp::Rem
                    | BinOp::And
                    | BinOp::Or => unreachable!(),
                };
                format!("({l} {sym} {r})")
            }
            ExprKind::Binary {
                op: op @ (BinOp::And | BinOp::Or),
                lhs,
                rhs,
                ..
            } => {
                let pl = self.eval_prop(lhs, scope);
                let guard = if *op == BinOp::And {
                    pl.clone()
                } else {
                    format!("¬{pl}")
                };
                let snap = self.hyps.len();
                let hname = format!("h_guard_{}", hslug(&guard));
                self.hyps.push((hname, guard));
                let pr = self.eval_prop(rhs, scope);
                self.hyps.truncate(snap);
                let sym = if *op == BinOp::And { "∧" } else { "∨" };
                format!("({pl} {sym} {pr})")
            }
            // Bool-typed calls (and anything else the checker typed Bool).
            ExprKind::IntLit(_)
            | ExprKind::Unary { .. }
            | ExprKind::Binary { .. }
            | ExprKind::Call { .. }
            | ExprKind::Index { .. }
            | ExprKind::Len { .. }
            | ExprKind::RawOp { .. }
            | ExprKind::DeviceOp { .. }
            | ExprKind::ResOp { .. }
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
            | ExprKind::RecordLit { .. } => match self.eval_after_trap_lookup(e, scope) {
                Val::Prop(p) => p,
                Val::Int(_)
                | Val::Opt(_)
                | Val::Arr(_)
                | Val::Slots(_)
                | Val::Obj(_)
                | Val::Record(_)
                | Val::View(_)
                | Val::Ptr(_)
                | Val::Unit => unreachable!("checked: bool-typed expression"),
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
                | Val::Slots(s)
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
                Val::Prop(p) if p != name && p != &format!("({name} = true)") => {
                    Some((name.clone(), lean_bool_value(p)))
                }
                Val::Int(_)
                | Val::Prop(_)
                | Val::Opt(_)
                | Val::Arr(_)
                | Val::Slots(_)
                | Val::Obj(_)
                | Val::Record(_)
                | Val::View(_)
                | Val::Ptr(_)
                | Val::Unit => None,
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
            Some(
                Val::Int(_)
                | Val::Prop(_)
                | Val::Opt(_)
                | Val::Arr(_)
                | Val::Slots(_)
                | Val::Record(_)
                | Val::View(_)
                | Val::Ptr(_)
                | Val::Unit,
            )
            | None => unreachable!("checked: self in scope"),
        }
    }

    /// Current symbolic expression for an array or owner-slot field of self.
    fn self_field_str(&self, field: &str) -> String {
        match self.cctx {
            Cctx::Init(_) => match self.env.get(&format!("self.{field}")) {
                Some(Val::Arr(s)) | Some(Val::Slots(s)) => s.clone(),
                Some(
                    Val::Int(_)
                    | Val::Prop(_)
                    | Val::Opt(_)
                    | Val::Obj(_)
                    | Val::Record(_)
                    | Val::View(_)
                    | Val::Ptr(_)
                    | Val::Unit,
                )
                | None => unreachable!("checked: field initialized"),
            },
            Cctx::Method(..) | Cctx::Deinit(_) => project_field(&self.self_chain(), field),
            Cctx::None => unreachable!("checked: fields only in members"),
        }
    }

    /// Current symbolic array expression for an in-scope array name.
    fn arr_str(&self, name: &str) -> String {
        match self.env.get(name) {
            Some(Val::Arr(s)) => s.clone(),
            Some(
                Val::Int(_)
                | Val::Prop(_)
                | Val::Opt(_)
                | Val::Slots(_)
                | Val::Obj(_)
                | Val::Record(_)
                | Val::View(_)
                | Val::Ptr(_)
                | Val::Unit,
            )
            | None => unreachable!("checked: array in scope"),
        }
    }

    /// Current symbolic view of a resource in scope.
    fn slots_str(&self, name: &str) -> String {
        match self.env.get(name) {
            Some(Val::Slots(s)) => s.clone(),
            Some(
                Val::Int(_)
                | Val::Prop(_)
                | Val::Opt(_)
                | Val::Arr(_)
                | Val::Obj(_)
                | Val::Record(_)
                | Val::View(_)
                | Val::Ptr(_)
                | Val::Unit,
            )
            | None => unreachable!("checked: owner-slot container in scope"),
        }
    }

    /// Current symbolic view of a resource in scope.
    fn view_str(&self, name: &str) -> String {
        match self.env.get(name) {
            Some(Val::View(s)) => s.clone(),
            Some(
                Val::Int(_)
                | Val::Prop(_)
                | Val::Opt(_)
                | Val::Arr(_)
                | Val::Slots(_)
                | Val::Obj(_)
                | Val::Record(_)
                | Val::Ptr(_)
                | Val::Unit,
            )
            | None => unreachable!("checked: resource in scope"),
        }
    }

    /// Current symbolic state of a `&mut` param — an array chain or a
    /// class-state symbol.
    fn state_str(&self, name: &str) -> String {
        match self.env.get(name) {
            Some(Val::Arr(s)) | Some(Val::Slots(s)) | Some(Val::Obj(s)) | Some(Val::View(s)) => {
                s.clone()
            }
            Some(
                Val::Int(_) | Val::Prop(_) | Val::Opt(_) | Val::Record(_) | Val::Ptr(_) | Val::Unit,
            )
            | None => unreachable!("checked: &mut param in scope"),
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
            match p.ty.referent() {
                Ty::Int(_) | Ty::Param(_) => out.push((p.name.clone(), "Int".into())),
                Ty::Bool => out.push((p.name.clone(), "Bool".into())),
                Ty::Class(ci) => {
                    let lean = lean_class_name(&self.classes[*ci].name);
                    out.push((p.name.clone(), lean.clone()));
                    if let Some(entry) = self.entry_states.get(&p.name) {
                        out.push((entry.clone(), lean));
                    }
                }
                Ty::Record(ri) => {
                    out.push((p.name.clone(), lean_record_name(&self.records[*ri].name)))
                }
                Ty::Array(element) => {
                    let lean_ty = lean_array_ty(element, self.records);
                    out.push((p.name.clone(), lean_ty.clone()));
                    if let Some(entry) = self.entry_states.get(&p.name) {
                        out.push((entry.clone(), lean_ty));
                    }
                }
                Ty::Slots(_) => {
                    refuse_vc_type(format!(
                        "internal.vcgen.slots_unsupported: parameter `{}` has no clause binder",
                        p.name
                    ));
                }
                Ty::Raw(_) | Ty::RawRecord(_) => out.push((p.name.clone(), "Sable.RawPtr".into())),
                Ty::OptionRaw(_) => out.push((p.name.clone(), "Option Sable.RawPtr".into())),
                Ty::Res(k) => {
                    out.push((p.name.clone(), lean_res_view_ty(*k, self.records)));
                    if let Some(entry) = self.entry_states.get(&p.name) {
                        out.push((entry.clone(), lean_res_view_ty(*k, self.records)));
                    }
                }
                Ty::Option(element) => {
                    out.push((p.name.clone(), lean_option_ty(element, self.classes)));
                }
                Ty::Borrow(..) | Ty::Unit => {}
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
    fn t_min(&self, ty: &Ty) -> String {
        let it = adr0009_int_model(ty);
        if let IntTy::TParam(i) = it {
            return format!("{}.min", self.tparams[i as usize]);
        }
        it.lean_min()
    }
    fn t_max(&self, ty: &Ty) -> String {
        let it = adr0009_int_model(ty);
        if let IntTy::TParam(i) = it {
            return format!("{}.max", self.tparams[i as usize]);
        }
        it.lean_max()
    }

    /// Integer arrays carry explicit element-range hypotheses. A Boolean
    /// sequence needs no analogue: Lean's `Bool` type is already its complete
    /// value domain, so inventing numeric bounds would both be ill-typed and
    /// would conflate the two aggregate proof models.
    fn array_element_range_prop(&self, array: &str, ty: &Ty) -> Option<String> {
        match ty {
            Ty::Bool => None,
            Ty::Int(_) | Ty::Param(_) => Some(format!(
                "∀ k, 0 ≤ k → k < {array}.len → {} ≤ {array}.get k ∧ {array}.get k ≤ {}",
                self.t_min(&ty.clone()),
                self.t_max(ty)
            )),
            // Nominal well-formedness elementwise: every record value a
            // program can store was built through the checked constructor.
            Ty::Record(ri) => Some(format!(
                "∀ k, 0 ≤ k → k < {array}.len → {}.wf ({array}.get k)",
                lean_record_name(&self.records[*ri].name)
            )),
            other @ (Ty::Class(_)
            | Ty::Array(_)
            | Ty::Slots(_)
            | Ty::Option(_)
            | Ty::OptionRaw(_)
            | Ty::Res(_)
            | Ty::Raw(_)
            | Ty::RawRecord(_)
            | Ty::Borrow(..)
            | Ty::Unit) => {
                refuse_vc_type(format!(
                    "internal.vcgen.lean_type_unsupported: array payload `{}` has no \
                     element-range fact",
                    other.name()
                ));
                None
            }
        }
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

    /// Preserve established user-facing obligation names unless two legal
    /// member flavors share the same display spelling. Lean declaration
    /// identities always carry the typed owner independently.
    fn obligation_owner(&self) -> String {
        let collides = match self.cctx {
            Cctx::None => false,
            Cctx::Init(class) => class
                .methods
                .iter()
                .any(|method| method.f.name == self.f.name),
            Cctx::Method(class, _) => class.inits.iter().any(|init| init.name == self.f.name),
            Cctx::Deinit(class) => {
                class.inits.iter().any(|init| init.name == "deinit")
                    || class.methods.iter().any(|method| method.f.name == "deinit")
            }
        };
        if !collides {
            return self.fname.clone();
        }
        match &self.call_owner {
            CallOwner::Function(_) => self.fname.clone(),
            CallOwner::Constructor { class, init } => {
                format!("{class}::{init}::constructor")
            }
            CallOwner::Method { class, method } => format!("{class}::{method}::method"),
            CallOwner::Deinitializer { class } => format!("{class}::deinit::destructor"),
        }
    }

    fn obligation(
        &mut self,
        name: &str,
        kind_desc: String,
        span: Span,
        goal: String,
    ) -> Obligation {
        let owner = self.obligation_owner();
        let semantic_name = match name.strip_prefix(&self.fname) {
            Some(rest) if rest.is_empty() || rest.starts_with('.') => format!("{owner}{rest}"),
            Some(_) | None => format!("{owner}.{name}"),
        };
        let unique = self.unique_name(&semantic_name);
        let owner = self.call_owner.certificate_component();
        Obligation {
            thm_name: injective_lean_components("vc", &[owner.as_str(), unique.as_str()]),
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

/// The well-formedness a resource view carries at every binding site.
/// This is the shape of the *value*, not a claim about authority: a span
/// has a nonnegative length its byte sequence covers.
fn sealed_resource_kind(operation: &CheckedSealedOperation, index: usize) -> Option<ResKind> {
    let argument = operation.arguments.get(index)?;
    match &argument.effect {
        CallArgumentEffect::Loan(loan) => loan.referent.res_kind(),
        CallArgumentEffect::Value(value) => value.value_ty.res_kind(),
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
        // A unique borrow is the only parameter whose storage the callee
        // can change while the caller still names it, so it is the only one
        // whose `old p` needs an entry-state binder.
        if !p.ty.is_unique_borrow() {
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
                _other_byte => {}
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

/// Encode an arbitrary semantic identity as one injective Lean identifier.
///
/// Sanitizing punctuation is lossy (`a.b_c` and `a_b.c` collapse), which is
/// unsafe for declarations subtracted across module artifacts. The byte
/// length plus full UTF-8 hex payload makes distinct identities distinct;
/// the version tag leaves room to change the representation deliberately.
fn injective_lean_name(prefix: &str, identity: &str) -> String {
    let payload = identity
        .as_bytes()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    format!("{prefix}_v1_{}_{payload}", identity.len())
}

/// Compose semantic fields without delimiter ambiguity before encoding them.
fn injective_lean_components(prefix: &str, components: &[&str]) -> String {
    let identity = components
        .iter()
        .map(|component| format!("{}:{component}", component.len()))
        .collect::<String>();
    injective_lean_name(prefix, &identity)
}

fn callable_lean_name(prefix: &str, owner: &CallOwner, role: &str, occurrence: usize) -> String {
    let owner = owner.certificate_component();
    let occurrence = occurrence.to_string();
    injective_lean_components(prefix, &[owner.as_str(), role, occurrence.as_str()])
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

#[cfg(test)]
mod type_domain_tests {
    use super::*;
    use crate::span::LineMap;
    use crate::transition::CallTransition;

    #[test]
    fn owner_slots_have_a_distinct_local_vc_type_and_sealed_operation_gate() {
        let slots = Ty::slots(Ty::Int(IntTy::U64));
        validate_vc_ty(slots.clone(), false, "slot local")
            .expect("owner slots have a proof representation");
        validate_vc_type_position(slots.clone(), false, VcTypePosition::Local, "slot local")
            .expect("owner slots are admitted as local storage");
        let error = validate_vc_type_position(
            slots.clone(),
            false,
            VcTypePosition::Parameter,
            "slot parameter",
        )
        .expect_err("owner slots do not cross call boundaries");
        assert!(error.starts_with("vc.slots_position:"), "{error}");
        assert_eq!(
            lean_slots_ty(&Ty::Int(IntTy::U64), &[], &[]),
            "Sable.Seq (Option Int)"
        );

        let operation = Expr {
            kind: ExprKind::SlotOp {
                op: SlotOp::Take,
                op_span: Span::new(1, 2),
                args: Vec::new(),
            },
            span: Span::new(1, 2),
            ty: Some(Ty::Unit),
        };
        let error = validate_vc_expr(&operation, false, "forged slot operation", &HashMap::new())
            .expect_err("a sealed operation must retain its exact arity and types");
        assert!(
            error.starts_with("internal.vcgen.slot_transition_shape:"),
            "{error}"
        );
    }

    /// A shape the preflight should have refused reaches a helper that has no
    /// error channel. The answer is a latched, named internal error and a
    /// Lean name that does not exist in the prelude — never a panic, and
    /// never an invented type. `generate` fails on the latch, so the
    /// placeholder cannot be published.
    ///
    /// This refusal is unreachable from any `.sable` source by construction,
    /// which is why it is named in the `internal.` namespace and covered here
    /// rather than by a `corpus/must-fail/` subject (ADR 0064).
    #[test]
    fn an_unprovable_payload_latches_a_named_internal_error() {
        let _ = take_vc_type_refusal();

        assert_eq!(lean_array_ty(&Ty::Class(0), &[]), UNSUPPORTED_LEAN_TY);
        let latched = take_vc_type_refusal().expect("the refusal is latched");
        assert!(
            latched.starts_with("internal.vcgen.lean_type_unsupported:"),
            "{latched}"
        );
        assert!(take_vc_type_refusal().is_none(), "the latch is taken once");

        // The one admitted owning payload has a Lean type, parenthesized so
        // it stays one argument.
        assert_eq!(
            lean_option_ty(&Ty::array(Ty::Bool), &[]),
            "Option (Sable.Seq Bool)"
        );
        assert!(
            take_vc_type_refusal().is_none(),
            "an owned payload is not a refusal"
        );

        assert_eq!(
            lean_option_ty(&Ty::array(Ty::Int(IntTy::U64)), &[]),
            UNSUPPORTED_LEAN_TY
        );
        assert!(
            take_vc_type_refusal()
                .expect("the refusal is latched")
                .starts_with("internal.vcgen.lean_type_unsupported:")
        );

        assert_eq!(adr0009_ty_int_model(Ty::Bool), IntTy::I64);
        assert!(
            take_vc_type_refusal()
                .expect("the refusal is latched")
                .starts_with("internal.vcgen.int_model_unsupported:")
        );
    }

    /// The payload gate names its refusals in the `internal.` namespace for
    /// the same reason: the checker refuses each of these shapes first, so no
    /// `.sable` source reaches them. The exemption from the corpus convention
    /// is earned by asserting the names here, and each container reports
    /// itself so a refusal says which position asked (ADR 0064).
    #[test]
    fn a_payload_with_no_proof_semantics_is_refused_by_name() {
        // The recursive family splits by container: an option payload may
        // itself be an option, an array element may not.
        validate_vc_payload_ty(
            &Ty::option(Ty::Int(IntTy::U64)),
            false,
            VcAggregateKind::Option,
            "a probe",
        )
        .expect("option nesting has proof semantics per level");
        validate_vc_payload_ty(
            &Ty::option(Ty::Int(IntTy::U64)),
            false,
            VcAggregateKind::Array,
            "a probe",
        )
        .expect_err("an array element stays a flat value");
        validate_vc_payload_ty(&Ty::Record(0), false, VcAggregateKind::Array, "a probe")
            .expect("record elements have proof semantics");
        let record_option =
            validate_vc_payload_ty(&Ty::Record(0), false, VcAggregateKind::Option, "a probe")
                .expect_err("record option payloads keep the refusal");
        assert!(
            record_option.starts_with("internal.vcgen.type_error:"),
            "{record_option}"
        );
        for aggregate in [VcAggregateKind::Array, VcAggregateKind::Option] {
            let container = aggregate.container();
            for shape in [
                Ty::Class(0),
                Ty::array(Ty::Int(IntTy::U64)),
                Ty::Int(IntTy::TParam(0)),
                Ty::Param(TypeParamId::from_legacy(0)),
            ] {
                let refusal = validate_vc_payload_ty(&shape, false, aggregate, "a probe")
                    .expect_err("the gate refuses every payload without proof semantics");
                assert!(
                    refusal.starts_with("internal.vcgen.type_error:"),
                    "{refusal}"
                );
                assert!(refusal.contains(container), "{refusal}");
            }

            // A parameter is admitted only where a retained template licenses
            // one, so the same shape answers differently by position.
            assert!(
                validate_vc_payload_ty(
                    &Ty::Param(TypeParamId::from_legacy(0)),
                    true,
                    aggregate,
                    "a template probe",
                )
                .is_ok()
            );
        }
    }

    fn parsed_program(source: &str) -> Program {
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

    fn checked_program(source: &str) -> (Program, CheckResult) {
        let mut program = parsed_program(source);
        crate::mono::monomorphize(&mut program).expect("test source should monomorphize");
        let checked = crate::check::check(&mut program).expect("test source should typecheck");
        (program, checked)
    }

    fn tampered_generation_error(source: &str, tamper: impl FnOnce(&mut CheckResult)) -> String {
        let (program, mut checked) = checked_program(source);
        tamper(&mut checked);
        match generate(&program, &checked, source, Path::new(".")) {
            Err(error) => error,
            Ok(_) => panic!("tampered checker ownership facts must fail closed"),
        }
    }

    fn affine_bool_option() -> Ty {
        Ty::affine_array_option(Ty::Bool)
    }

    fn public_generate_error(program: &Program) -> String {
        if let Err(error) = validate_vc_type_domain(program) {
            return error;
        }
        let checked = CheckResult {
            sigs: HashMap::new(),
            control: crate::control::ControlProgram::build(program)
                .expect("the forged VC-domain fixture still has structural control"),
            ownership: CheckedOwnershipPlan::default(),
            unsafe_regions: 0,
        };
        match generate(program, &checked, "", Path::new(".")) {
            Err(error) => error,
            Ok(_) => panic!("synthetic invalid affine-option program reached VC generation"),
        }
    }

    #[test]
    fn owner_slot_roundtrip_emits_occupancy_vcs_and_atomic_state_updates() {
        let source = r#"
fn slot_roundtrip(u64 value) -> u64 {
    mut slots<u64> cells = alloc_slots<u64>(1);
    slot_put(&mut cells, 0, value);
    u64 taken = slot_take(&mut cells, 0);
    return taken;
}
"#;
        let (program, checked) = checked_program(source);
        let generated = generate(&program, &checked, source, Path::new("."))
            .expect("checked owner-slot operations must have VC semantics");

        assert!(
            generated
                .obligations
                .iter()
                .flat_map(|obligation| &obligation.binders)
                .any(|(_, ty)| ty == "Sable.Seq (Option Int)")
        );
        let put_bounds = generated
            .obligations
            .iter()
            .find(|obligation| {
                obligation
                    .name
                    .starts_with("slot_roundtrip.slot_put.bounds")
            })
            .expect("put emits its exact bounds obligation");
        assert!(put_bounds.goal.contains(".len"));
        assert!(put_bounds.hyps.iter().any(|(name, proposition)| {
            name.contains("all_none") && proposition.contains("none : Option Int")
        }));
        let put_empty = generated
            .obligations
            .iter()
            .find(|obligation| obligation.name.starts_with("slot_roundtrip.slot_put.empty"))
            .expect("put emits an empty-cell obligation");
        assert!(put_empty.goal.contains("= (none : Option Int)"));

        let take_occupied = generated
            .obligations
            .iter()
            .find(|obligation| {
                obligation
                    .name
                    .starts_with("slot_roundtrip.slot_take.occupied")
            })
            .expect("take emits an occupied-cell obligation");
        assert!(take_occupied.goal.contains("≠ (none : Option Int)"));
        assert!(take_occupied.hyps.iter().any(|(_, proposition)| {
            proposition.contains(".set") && proposition.contains("some")
        }));
        assert!(generated.obligations.iter().all(|obligation| {
            obligation
                .binders
                .iter()
                .all(|(_, ty)| ty != "Sable.Seq Int" || !obligation.name.contains("slot_"))
        }));

        assert_eq!(
            generated.transition_certificates.len(),
            2,
            "allocation has no certificate; put and take each have one"
        );
        for certificate in &generated.transition_certificates {
            assert!(
                certificate.hyps.is_empty(),
                "slot writeback certificates must not consume generator-authored semantic hypotheses"
            );
            match &certificate.kind {
                crate::transition::TransitionCertificateKind::SlotTake {
                    transition,
                    action,
                    ..
                }
                | crate::transition::TransitionCertificateKind::SlotPut {
                    transition,
                    action,
                    ..
                } => {
                    assert_eq!(action.effect_key(), &transition.key);
                    assert_eq!(action.span(), transition.key.span);
                    assert_eq!(action.payload(), &transition.payload);
                    assert_eq!(action.result_ty(), &transition.result_ty);
                }
                crate::transition::TransitionCertificateKind::CallHavoc { .. } => {
                    panic!("the local roundtrip has no call-havoc transition")
                }
            }
        }
        let put = generated
            .transition_certificates
            .iter()
            .find_map(|certificate| match &certificate.kind {
                crate::transition::TransitionCertificateKind::SlotPut {
                    before,
                    observed,
                    index,
                    staged,
                    ..
                } => Some((certificate, before, observed, index, staged)),
                crate::transition::TransitionCertificateKind::CallHavoc { .. }
                | crate::transition::TransitionCertificateKind::SlotTake { .. } => None,
            })
            .expect("the local put emits its writeback certificate");
        assert_eq!(
            put.2,
            &format!("({}.set {} (some ({})))", put.1, put.3, put.4),
            "the local post-state is read back exactly"
        );
        assert_eq!(
            put.0.lean_goal(),
            format!(
                "Sable.SlotPutWriteback ({}) ({}) ({}) ({})",
                put.1, put.2, put.3, put.4
            ),
            "the fixed certificate states only the structural put writeback"
        );
        let take = generated
            .transition_certificates
            .iter()
            .find_map(|certificate| match &certificate.kind {
                crate::transition::TransitionCertificateKind::SlotTake {
                    before,
                    observed,
                    index,
                    ..
                } => Some((certificate, before, observed, index)),
                crate::transition::TransitionCertificateKind::CallHavoc { .. }
                | crate::transition::TransitionCertificateKind::SlotPut { .. } => None,
            })
            .expect("the local take emits its writeback certificate");
        assert_eq!(
            take.2,
            &format!("({}.set {} (none : Option Int))", take.1, take.3),
            "the local post-state is read back exactly"
        );
        assert_eq!(
            take.0.lean_goal(),
            format!(
                "Sable.SlotTakeWriteback ({}) ({}) ({})",
                take.1, take.2, take.3
            ),
            "the fixed certificate states only the structural take writeback"
        );
        let returned = take
            .0
            .binders
            .iter()
            .map(|(name, _)| name)
            .find(|name| name.as_str() == "taken")
            .expect("the ordinary VC context retains the returned payload binder");
        assert!(
            !take.0.lean_goal().contains(returned),
            "trusted generator-authored payload provenance stays outside the fixed writeback predicate"
        );
        assert!(
            !put.0.lean_goal().contains("(incoming)"),
            "trusted generator-authored incoming-to-staged provenance stays outside the fixed predicate"
        );
        // Coordinated substitution that preserves these equalities is
        // deliberately a trusted-Rust provenance question, not a stronger
        // source-semantics claim smuggled into this structural certificate.

        let attempted_skip: HashSet<String> = generated
            .transition_certificates
            .iter()
            .map(|certificate| certificate.name.clone())
            .collect();
        let emitted = crate::lean::emit(
            &generated,
            &[],
            &attempted_skip,
            &[],
            &crate::lean::EmittedNames::default(),
        )
        .finish("SableGeneratedVcgenTest");
        assert!(emitted.lean_source.contains("Sable.SlotPutWriteback"));
        assert!(emitted.lean_source.contains("Sable.SlotTakeWriteback"));
        assert_eq!(generated.argument_schedule_certificates.len(), 3);
        assert!(emitted.lean_source.contains("Sable.ArgumentSchedule.safe"));
        assert_eq!(emitted.names.certificates.len(), 5);
    }

    #[test]
    fn slot_allocation_and_cleanup_emit_no_transition_certificate() {
        let source = r#"
class Payload {
    u64 value;

    init new() {
        self.value = 1;
    }
}

fn allocation_only() {
    mut slots<Payload> cells = alloc_slots<Payload>(2);
}
"#;
        let (program, checked) = checked_program(source);
        let generated = generate(&program, &checked, source, Path::new("."))
            .expect("slot allocation and lexical cleanup remain executable proof state");
        assert!(
            generated.transition_certificates.is_empty(),
            "allocation and cleanup remain outside the writeback-certificate slice"
        );
    }

    #[test]
    fn slot_writeback_certificates_use_injective_symbolic_visit_identities() {
        let source = r#"
fn branch_slot(bool choose, u64 incoming) -> u64 {
    mut slots<u64> cells = alloc_slots<u64>(1);
    if (choose) {
    } else {
    }
    slot_put(&mut cells, 0, incoming);
    return slot_take(&mut cells, 0);
}
"#;
        let (program, checked) = checked_program(source);
        assert_eq!(
            checked
                .ownership
                .slot_transitions_for_owner(&CallOwner::Function("branch_slot".into()))
                .count(),
            3,
            "the checker retains one alloc, one put, and one take source transition"
        );
        let generated = generate(&program, &checked, source, Path::new("."))
            .expect("branch revisits reuse immutable slot authorities");
        let puts: Vec<&TransitionCertificate> = generated
            .transition_certificates
            .iter()
            .filter(|certificate| {
                matches!(
                    &certificate.kind,
                    crate::transition::TransitionCertificateKind::SlotPut { .. }
                )
            })
            .collect();
        let takes: Vec<&TransitionCertificate> = generated
            .transition_certificates
            .iter()
            .filter(|certificate| {
                matches!(
                    &certificate.kind,
                    crate::transition::TransitionCertificateKind::SlotTake { .. }
                )
            })
            .collect();
        assert_eq!(puts.len(), 2);
        assert_eq!(takes.len(), 2);
        for certificates in [puts, takes] {
            assert!(certificates[0].name.contains(".visit.1"));
            assert!(certificates[1].name.contains(".visit.2"));
            assert_ne!(certificates[0].thm_name, certificates[1].thm_name);
        }
    }

    #[test]
    fn direct_self_slot_fields_are_read_back_after_initializer_and_method_writes() {
        let source = r#"
class SlotHolder {
    slots<u64> cells;

    init full(u64 incoming) {
        self.cells = alloc_slots<u64>(1);
        slot_put(&mut self.cells, 0, incoming);
    }

    fn drain(&mut self) -> u64 {
        self.cells = alloc_slots<u64>(1);
        slot_put(&mut self.cells, 0, 7);
        return slot_take(&mut self.cells, 0);
    }
}
"#;
        let (program, checked) = checked_program(source);
        let generated = generate(&program, &checked, source, Path::new("."))
            .expect("direct self slot fields have bounded writeback semantics");
        let initializer = generated
            .transition_certificates
            .iter()
            .find(|certificate| {
                matches!(
                    &certificate.kind,
                    crate::transition::TransitionCertificateKind::SlotPut { .. }
                ) && certificate
                    .name
                    .contains("constructor.SlotHolder.full.slot_put")
            })
            .expect("initializer put emits a certificate");
        assert_eq!(initializer.place().render(), "self.cells");
        let method = generated
            .transition_certificates
            .iter()
            .find(|certificate| {
                matches!(
                    &certificate.kind,
                    crate::transition::TransitionCertificateKind::SlotTake { .. }
                ) && certificate
                    .name
                    .contains("method.SlotHolder.drain.slot_take")
            })
            .expect("method take emits a certificate");
        let crate::transition::TransitionCertificateKind::SlotTake {
            before, observed, ..
        } = &method.kind
        else {
            unreachable!()
        };
        assert_eq!(method.place().render(), "self.cells");
        assert_eq!(
            observed,
            &format!("({before}.set 0 (none : Option Int))"),
            "the direct-field environment readback resolves to the exact installed update"
        );

        let emitted = crate::lean::emit(
            &generated,
            &[],
            &HashSet::new(),
            &[],
            &crate::lean::EmittedNames::default(),
        )
        .finish("SableGeneratedVcgenTest");
        assert!(emitted.lean_source.contains(&method.thm_name));

        let repo_root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("compiler crate has a repository parent");
        let environment = crate::lean::ProofEnvironment::capture(repo_root)
            .expect("the repository proof environment must be capturable");
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("test clock follows the Unix epoch")
            .as_nanos();
        let lean_file = std::env::temp_dir().join(format!(
            "sable_direct_self_slot_certificate_{}_{}.lean",
            std::process::id(),
            nonce
        ));
        std::fs::write(&lean_file, &emitted.lean_source)
            .expect("the direct-field generated document must be writable");
        let messages = crate::lean::run_lean(
            repo_root,
            &environment,
            &lean_file,
            None,
            &emitted.lean_source,
        )
        .expect("Lean must check the direct-field slot certificates");
        let _ = std::fs::remove_file(&lean_file);
        let modules = crate::modules::ModuleSet::single(
            "direct_self_slot_certificate.sable".into(),
            source.into(),
        );
        let diagnostics = crate::lean::diagnose(&emitted, &generated, &messages, &modules);
        assert!(
            diagnostics.is_empty(),
            "direct-field certificates must pass the kernel: {diagnostics:#?}"
        );
    }

    fn assert_tampered_slot_certificate_rejected_by_lean(
        source: &str,
        label: &str,
        tamper: impl FnOnce(&mut [TransitionCertificate]),
    ) {
        let (program, checked) = checked_program(source);
        let mut generated = generate(&program, &checked, source, Path::new("."))
            .expect("the untampered slot subject generates certificates");
        tamper(&mut generated.transition_certificates);
        let emitted = crate::lean::emit(
            &generated,
            &[],
            &HashSet::new(),
            &[],
            &crate::lean::EmittedNames::default(),
        )
        .finish("SableGeneratedVcgenTest");

        let repo_root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("compiler crate has a repository parent");
        let environment = crate::lean::ProofEnvironment::capture(repo_root)
            .expect("the repository proof environment must be capturable");
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("test clock follows the Unix epoch")
            .as_nanos();
        let lean_file = std::env::temp_dir().join(format!(
            "sable_tampered_slot_{}_{}_{}.lean",
            sanitize(label),
            std::process::id(),
            nonce
        ));
        std::fs::write(&lean_file, &emitted.lean_source)
            .expect("the tampered generated document must be writable");
        let messages = crate::lean::run_lean(
            repo_root,
            &environment,
            &lean_file,
            None,
            &emitted.lean_source,
        )
        .expect("Lean must run and reject the tampered slot theorem");
        let _ = std::fs::remove_file(&lean_file);
        let modules = crate::modules::ModuleSet::single(
            "slot_transition_certificate.sable".into(),
            source.into(),
        );
        let diagnostics = crate::lean::diagnose(&emitted, &generated, &messages, &modules);
        assert!(!diagnostics.is_empty(), "{label}: Lean accepted the tamper");
        assert!(
            diagnostics.iter().all(|diagnostic| {
                diagnostic.name == "internal.slot_transition_certificate_rejected"
                    && diagnostic.title.contains("slot-")
                    && diagnostic
                        .label
                        .contains("owner-slot write-back was not certified")
            }),
            "{label}: {diagnostics:#?}"
        );
    }

    #[test]
    fn lean_rejects_tampered_owner_slot_prestate_observation_index_and_staged_term() {
        let source = r#"
fn certified_roundtrip(u64 incoming) -> u64 {
    mut slots<u64> cells = alloc_slots<u64>(1);
    slot_put(&mut cells, 0, incoming);
    return slot_take(&mut cells, 0);
}
"#;
        assert_tampered_slot_certificate_rejected_by_lean(
            source,
            "take_observed",
            |certificates| {
                let certificate = certificates
                    .iter_mut()
                    .find(|certificate| {
                        matches!(
                            &certificate.kind,
                            crate::transition::TransitionCertificateKind::SlotTake { .. }
                        )
                    })
                    .expect("take certificate exists");
                let crate::transition::TransitionCertificateKind::SlotTake {
                    before, observed, ..
                } = &mut certificate.kind
                else {
                    unreachable!()
                };
                *observed = before.clone();
            },
        );
        assert_tampered_slot_certificate_rejected_by_lean(source, "take_before", |certificates| {
            let certificate = certificates
                .iter_mut()
                .find(|certificate| {
                    matches!(
                        &certificate.kind,
                        crate::transition::TransitionCertificateKind::SlotTake { .. }
                    )
                })
                .expect("take certificate exists");
            let crate::transition::TransitionCertificateKind::SlotTake {
                before, observed, ..
            } = &mut certificate.kind
            else {
                unreachable!()
            };
            *before = observed.clone();
        });
        assert_tampered_slot_certificate_rejected_by_lean(source, "take_index", |certificates| {
            let certificate = certificates
                .iter_mut()
                .find(|certificate| {
                    matches!(
                        &certificate.kind,
                        crate::transition::TransitionCertificateKind::SlotTake { .. }
                    )
                })
                .expect("take certificate exists");
            let crate::transition::TransitionCertificateKind::SlotTake { index, .. } =
                &mut certificate.kind
            else {
                unreachable!()
            };
            *index = "1".into();
        });
        assert_tampered_slot_certificate_rejected_by_lean(source, "put_staged", |certificates| {
            let certificate = certificates
                .iter_mut()
                .find(|certificate| {
                    matches!(
                        &certificate.kind,
                        crate::transition::TransitionCertificateKind::SlotPut { .. }
                    )
                })
                .expect("put certificate exists");
            let crate::transition::TransitionCertificateKind::SlotPut { staged, .. } =
                &mut certificate.kind
            else {
                unreachable!()
            };
            *staged = "0".into();
        });
    }

    #[test]
    fn class_slot_put_proves_the_staged_invariant_before_installation() {
        let source = r#"
class Item {
    u64 value;

    /// invariant value ≤ 10

    /// pre value ≤ 10
    init new(u64 value) {
        self.value = value;
    }
}

fn class_slot() {
    mut slots<Item> cells = alloc_slots<Item>(1);
    var item = Item::new(7);
    slot_put(&mut cells, 0, item);
    var restored = slot_take(&mut cells, 0);
}
"#;
        let (program, checked) = checked_program(source);
        let generated = generate(&program, &checked, source, Path::new("."))
            .expect("class payload slots preserve the concrete invariant fact");
        let invariant = generated
            .obligations
            .iter()
            .find(|obligation| obligation.name.contains("slot_put.payload.inv_"))
            .expect("put proves the staged concrete class invariant");
        assert!(invariant.goal.contains("≤ 10"));
        assert!(
            invariant.binders.iter().any(|(name, ty)| {
                name.contains("slot_put_value") && ty.contains("SableC_Item")
            })
        );
        let take = generated
            .obligations
            .iter()
            .find(|obligation| obligation.name.contains("slot_take.occupied"))
            .expect("class take proves occupancy");
        assert!(take.hyps.iter().any(|(name, proposition)| {
            name.contains("present_inv") && proposition.contains("≤ 10")
        }));
    }

    #[test]
    fn slot_put_evaluates_a_borrowing_index_before_staging_and_moving_its_value() {
        let source = r#"
class Item {
    u64 value;

    /// invariant value = 7

    init new() {
        self.value = 7;
    }
}

/// post result = 0
fn index_of(&Item item) -> u64 {
    return 0;
}

fn slot_put_order() {
    mut slots<Item> cells = alloc_slots<Item>(1);
    var item = Item::new();
    slot_put(&mut cells, index_of(&item), item);
    var restored = slot_take(&mut cells, 0);
}
"#;
        let (program, checked) = checked_program(source);
        let generated = generate(&program, &checked, source, Path::new("."))
            .expect("the put index may borrow its payload before the later move");

        let borrow_invariant = generated
            .obligations
            .iter()
            .find(|obligation| obligation.name.contains("slot_put_order.borrow_inv.item"))
            .expect("the index helper checks its shared class borrow");
        assert!(
            borrow_invariant
                .binders
                .iter()
                .all(|(name, _)| { !name.contains("slot_put_value") })
        );
        assert!(borrow_invariant.hyps.iter().all(|(name, proposition)| {
            !name.contains("staged") && !proposition.contains("slot_put_value")
        }));

        let bounds = generated
            .obligations
            .iter()
            .find(|obligation| obligation.name.contains("slot_put_order.slot_put.bounds"))
            .expect("the put emits bounds after staging");
        let post_position = bounds
            .hyps
            .iter()
            .position(|(name, _)| name.starts_with("h_index_of_post_"))
            .expect("the index call postcondition is in scope");
        let staged_position = bounds
            .hyps
            .iter()
            .position(|(name, _)| name.contains("staged"))
            .expect("the moved value is staged before the guard");
        assert!(post_position < staged_position);
        let result_position = bounds
            .binders
            .iter()
            .position(|(name, ty)| name.starts_with("_r") && ty == "Int")
            .expect("the index result is bound");
        let staging_position = bounds
            .binders
            .iter()
            .position(|(name, ty)| name.contains("slot_put_value") && ty.contains("SableC_Item"))
            .expect("the payload staging binder is present");
        assert!(result_position < staging_position);

        let tampered = tampered_generation_error(source, |checked| {
            let owner = CallOwner::Function("slot_put_order".into());
            let key = checked
                .ownership
                .slot_transitions_for_owner(&owner)
                .find(|(_, transition)| {
                    matches!(transition.kind, CheckedSlotTransitionKind::Put { .. })
                })
                .expect("put transition")
                .0
                .clone();
            let transition = checked
                .ownership
                .slot_transition_mut(&key)
                .expect("mutable put transition");
            let CheckedSlotTransitionKind::Put {
                index_span,
                value_transfer,
                ..
            } = &mut transition.kind
            else {
                unreachable!()
            };
            value_transfer.span = *index_span;
        });
        assert!(
            tampered.starts_with("internal.vcgen.slot_transition_mismatch:"),
            "{tampered}"
        );
    }

    #[test]
    fn initializer_slot_operations_read_the_exact_initialized_field_state() {
        let source = r#"
class InitializedPool {
    slots<u64> cells;
    u64 restored;

    init new() {
        self.cells = alloc_slots<u64>(1);
        slot_put(&mut self.cells, 0, 7);
        self.restored = slot_take(&mut self.cells, 0);
    }
}
"#;
        let (program, checked) = checked_program(source);
        let generated = generate(&program, &checked, source, Path::new("."))
            .expect("initializer slot operations use the initialized field entry directly");
        assert_eq!(generated.classes[0].fields[0].1, "Sable.Seq (Option Int)");

        let put_bounds = generated
            .obligations
            .iter()
            .find(|obligation| obligation.name.contains("slot_put.bounds"))
            .expect("the initializer put emits its bounds obligation");
        assert!(put_bounds.goal.contains(".len"));
        let take_occupied = generated
            .obligations
            .iter()
            .find(|obligation| obligation.name.contains("slot_take.occupied"))
            .expect("the initializer take emits its occupancy obligation");
        assert!(take_occupied.goal.contains(".set"));
        assert!(take_occupied.goal.contains("some"));
    }

    #[test]
    fn direct_self_slot_fields_use_the_enclosing_class_state_chain() {
        let source = r#"
class Pool {
    slots<u64> cells;

    init new() {
        self.cells = alloc_slots<u64>(1);
    }

    fn roundtrip(&mut self, u64 value) -> u64 {
        slot_put(&mut self.cells, 0, value);
        return slot_take(&mut self.cells, 0);
    }

    fn replace(&mut self) -> u64 {
        var previous = self.cells;
        mut slots<u64> next = alloc_slots<u64>(2);
        self.cells = next;
        return self.cells.len;
    }
}
"#;
        let (program, checked) = checked_program(source);
        let generated = generate(&program, &checked, source, Path::new("."))
            .expect("direct self slot fields have symbolic read/write semantics");
        assert_eq!(generated.classes[0].fields[0].1, "Sable.Seq (Option Int)");
        let occupied = generated
            .obligations
            .iter()
            .find(|obligation| obligation.name.contains("slot_take.occupied"))
            .expect("the field take emits occupancy");
        assert!(occupied.goal.contains(".cells"));
        assert!(occupied.goal.contains(".set"));
        assert!(occupied.goal.contains("some"));
    }

    #[test]
    fn slot_loop_effects_validate_the_transition_and_havoc_the_whole_container() {
        let source = r#"
fn slot_loop() {
    mut slots<u64> cells = alloc_slots<u64>(1);
    slot_put(&mut cells, 0, 7);
    mut u64 i = 0;
    /// invariant i ≤ 1
    /// invariant cells.len = 1
    /// variant 1 - i
    while (i < 1) {
        u64 value = slot_take(&mut cells, i);
        slot_put(&mut cells, i, value);
        i = i + 1;
    }
    u64 final_value = slot_take(&mut cells, 0);
}
"#;
        let (program, checked) = checked_program(source);
        let generated = generate(&program, &checked, source, Path::new("."))
            .expect("slot loop mutations have exact checker-linked havoc semantics");
        let loop_take = generated
            .obligations
            .iter()
            .find(|obligation| {
                obligation.name.contains("slot_take.occupied")
                    && obligation
                        .binders
                        .iter()
                        .any(|(name, ty)| name == "cells" && ty == "Sable.Seq (Option Int)")
            })
            .expect("the loop body take sees a fresh whole-container binder");
        assert!(loop_take.hyps.iter().any(|(name, proposition)| {
            name.starts_with("h_inv_") && proposition.contains("cells.len")
        }));
        assert!(loop_take.hyps.iter().any(|(name, proposition)| {
            name.starts_with("h_cells_len")
                && proposition.contains("cells.len")
                && proposition.contains("_old")
        }));

        let error = tampered_generation_error(source, |checked| {
            let owner = CallOwner::Function("slot_loop".into());
            let key = checked
                .ownership
                .loops_for_owner(&owner)
                .next()
                .expect("loop effect")
                .0
                .clone();
            let effect = checked
                .ownership
                .loop_effects_mut(&key)
                .expect("mutable loop fixture");
            let mutation = effect
                .mutations
                .iter_mut()
                .find(|mutation| matches!(mutation, CheckedMutation::Slot { .. }))
                .expect("slot mutation");
            let CheckedMutation::Slot { payload, .. } = mutation else {
                unreachable!()
            };
            *payload = Ty::Bool;
        });
        assert!(
            error.starts_with("internal.vcgen.loop_slot_transition_mismatch:"),
            "{error}"
        );
    }

    #[test]
    fn slot_loop_whole_owner_writes_drop_local_and_init_field_length_facts() {
        let source = r#"
fn local_replacement() {
    mut slots<u64> cells = alloc_slots<u64>(1);
    mut u64 i = 0;
    /// invariant i ≤ 1
    /// variant 1 - i
    while (i < 1) {
        slots<u64> replacement = alloc_slots<u64>(2);
        cells = replacement;
        i = i + 1;
    }
    /// assert #[label(local_length_is_not_stable)] cells.len = 1
}

class FieldReplacement {
    slots<u64> cells;

    init new() {
        self.cells = alloc_slots<u64>(1);
        mut u64 i = 0;
        /// invariant i ≤ 1
        /// variant 1 - i
        while (i < 1) {
            slots<u64> replacement = alloc_slots<u64>(2);
            self.cells = replacement;
            i = i + 1;
        }
        /// assert #[label(field_length_is_not_stable)] self.cells.len = 1
    }
}
"#;
        let (program, checked) = checked_program(source);
        let generated = generate(&program, &checked, source, Path::new("."))
            .expect("whole owner writes havoc slots without a stale length equality");

        let local_assertion = generated
            .obligations
            .iter()
            .find(|obligation| obligation.name.contains("local_length_is_not_stable"))
            .expect("the local false assertion remains an obligation");
        assert!(
            local_assertion
                .hyps
                .iter()
                .all(|(name, _)| !name.starts_with("h_cells_len")),
            "a whole-local write must not retain a fresh-to-stale slot length equality: {local_assertion:#?}"
        );

        let field_assertion = generated
            .obligations
            .iter()
            .find(|obligation| obligation.name.contains("field_length_is_not_stable"))
            .expect("the init-field false assertion remains an obligation");
        assert!(
            field_assertion
                .hyps
                .iter()
                .all(|(name, _)| !name.starts_with("h_self_cells_len")),
            "a whole-field write must not retain a fresh-to-stale slot length equality: {field_assertion:#?}"
        );

        let emitted = crate::lean::emit(
            &generated,
            &[],
            &HashSet::new(),
            &[],
            &crate::lean::EmittedNames::default(),
        )
        .finish("SableGeneratedVcgenTest");
        let repo_root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("compiler crate has a repository parent");
        let environment = crate::lean::ProofEnvironment::capture(repo_root)
            .expect("the repository proof environment must be capturable");
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("test clock follows the Unix epoch")
            .as_nanos();
        let lean_file = std::env::temp_dir().join(format!(
            "sable_slot_length_havoc_{}_{}.lean",
            std::process::id(),
            nonce
        ));
        std::fs::write(&lean_file, &emitted.lean_source)
            .expect("the owner-slot havoc document must be writable");
        let messages = crate::lean::run_lean(
            repo_root,
            &environment,
            &lean_file,
            None,
            &emitted.lean_source,
        )
        .expect("Lean must run and reject the two false length assertions");
        let _ = std::fs::remove_file(&lean_file);
        let modules =
            crate::modules::ModuleSet::single("slot_length_havoc.sable".into(), source.into());
        let diagnostics = crate::lean::diagnose(&emitted, &generated, &messages, &modules);
        assert_eq!(diagnostics.len(), 2, "{diagnostics:#?}");
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.name.contains("local_length_is_not_stable")),
            "{diagnostics:#?}"
        );
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.name.contains("field_length_is_not_stable")),
            "{diagnostics:#?}"
        );
    }

    #[test]
    fn slot_transition_deletion_substitution_and_unvisited_insertion_fail_closed() {
        let source = r#"
fn slot_boundary(u64 value) {
    mut slots<u64> cells = alloc_slots<u64>(1);
    slot_put(&mut cells, 0, value);
    u64 restored = slot_take(&mut cells, 0);
}
"#;
        let deleted = tampered_generation_error(source, |checked| {
            let owner = CallOwner::Function("slot_boundary".into());
            let key = checked
                .ownership
                .slot_transitions_for_owner(&owner)
                .find(|(_, transition)| {
                    matches!(transition.kind, CheckedSlotTransitionKind::Put { .. })
                })
                .expect("put transition")
                .0
                .clone();
            checked
                .ownership
                .remove_slot_transition(&key)
                .expect("remove retained transition");
        });
        assert!(
            deleted.starts_with("internal.vcgen.slot_transition_missing:"),
            "{deleted}"
        );

        let substituted = tampered_generation_error(source, |checked| {
            let owner = CallOwner::Function("slot_boundary".into());
            let key = checked
                .ownership
                .slot_transitions_for_owner(&owner)
                .find(|(_, transition)| {
                    matches!(transition.kind, CheckedSlotTransitionKind::Take { .. })
                })
                .expect("take transition")
                .0
                .clone();
            checked
                .ownership
                .slot_transition_mut(&key)
                .expect("mutable retained transition")
                .payload = Ty::Bool;
        });
        assert!(
            substituted.starts_with("internal.vcgen.slot_transition_mismatch:"),
            "{substituted}"
        );

        let unvisited = tampered_generation_error(source, |checked| {
            let owner = CallOwner::Function("slot_boundary".into());
            let mut transition = checked
                .ownership
                .slot_transitions_for_owner(&owner)
                .next()
                .expect("slot transition")
                .1
                .clone();
            transition.key.span = Span::new(0, 0);
            checked
                .ownership
                .insert_slot_transition(transition)
                .expect("insert distinct forged transition");
        });
        assert!(
            unvisited.starts_with("internal.vcgen.slot_transition_unvisited:"),
            "{unvisited}"
        );
    }

    #[test]
    fn affine_options_stay_local_only_at_the_public_vc_boundary() {
        let mut return_program = parsed_program("fn subject() {}");
        return_program.fns[0].ret = affine_bool_option();
        assert!(public_generate_error(&return_program).starts_with("vc.affine_option_position:"));

        let mut local_program = parsed_program("fn subject() {}");
        local_program.fns[0].body.push(Stmt::Decl {
            ty: affine_bool_option(),
            name: "maybe_flags".into(),
            name_span: Span::new(0, 0),
            init: None,
            mutable: false,
        });
        assert!(public_generate_error(&local_program).starts_with("vc.affine_option_initializer:"));

        let mut expression_program = parsed_program("fn subject() {}");
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
        assert!(
            public_generate_error(&expression_program).starts_with("vc.affine_option_temporary:")
        );
    }

    #[test]
    fn affine_option_take_is_one_symbolic_transition_with_a_typed_default() {
        let source = r#"
fn affine_take(u64 n) {
    mut option<[bool]> pending = some(alloc_array<bool>(n, false));
    if (pending.is_some) {
        [bool] flags = pending.take;
        /// assert #[label(absent)] ¬pending.is_some
        /// assert #[label(length)] flags.len = n
    }
}
"#;
        let (program, checked) = checked_program(source);
        let generated = generate(&program, &checked, source, Path::new("."))
            .expect("checked affine-option locals must have VC semantics");

        let take = generated
            .obligations
            .iter()
            .find(|obligation| obligation.name.starts_with("affine_take.option_take"))
            .expect("take must emit a presence obligation");
        assert!(take.goal.contains("≠ none"));
        assert!(take.hyps.iter().any(|(name, proposition)| {
            name.starts_with("h_path_") && proposition.contains("≠ none")
        }));
        assert!(take.binders.iter().any(|(_, ty)| ty == "Sable.Seq Bool"));

        let absent = generated
            .obligations
            .iter()
            .find(|obligation| obligation.name.contains("assert.absent"))
            .expect("post-take absence assertion must be generated");
        assert!(absent.goal.contains("none : Option (Sable.Seq Bool)"));

        let length = generated
            .obligations
            .iter()
            .find(|obligation| obligation.name.contains("assert.length"))
            .expect("taken payload assertion must be generated");
        assert!(length.goal.contains("getD ⟨0, fun _ => false⟩"));
        assert!(generated.obligations.iter().all(|obligation| {
            !obligation.goal.contains("Inhabited")
                && obligation
                    .binders
                    .iter()
                    .all(|(_, ty)| !ty.contains("Inhabited"))
                && obligation
                    .hyps
                    .iter()
                    .all(|(_, proposition)| !proposition.contains("Inhabited"))
        }));
    }

    #[test]
    fn affine_option_take_is_a_loop_havoc_effect() {
        let source = r#"
fn affine_loop(u64 n) {
    mut option<[bool]> pending = some(alloc_array<bool>(n, false));
    mut u64 remaining = 1;
    /// invariant remaining ≤ 1
    /// invariant remaining = 1 → pending.is_some
    /// invariant remaining = 0 → ¬pending.is_some
    /// variant remaining
    while (remaining > 0) {
        [bool] flags = pending.take;
        remaining = 0;
    }
}
"#;
        let (program, checked) = checked_program(source);
        let generated = generate(&program, &checked, source, Path::new("."))
            .expect("affine-option take must survive loop havoc");
        let take = generated
            .obligations
            .iter()
            .find(|obligation| obligation.name.starts_with("affine_loop.option_take"))
            .expect("loop body must retain the take obligation");
        assert!(
            take.binders
                .iter()
                .any(|(name, ty)| { name == "pending" && ty == "Option (Sable.Seq Bool)" })
        );
        assert!(take.hyps.iter().any(|(name, proposition)| {
            name.starts_with("h_inv_") && proposition.contains("pending.is_some")
        }));

        let Stmt::While { kw_span, .. } = &program.fns[0].body[2] else {
            panic!("fixture keeps the loop as its third statement")
        };
        let key = EffectSiteKey {
            owner: CallOwner::Function("affine_loop".into()),
            span: *kw_span,
        };
        let effects = checked
            .ownership
            .loop_effects(&key)
            .expect("checker authors one exact loop mutation set");
        assert!(effects.mutations.iter().any(|mutation| matches!(
            mutation,
            CheckedMutation::OptionTake { source, payload }
                if source == &Place::local("pending")
                    && payload == &Ty::array(Ty::Bool)
        )));
    }

    #[test]
    fn affine_option_vc_preflight_rejects_immutable_and_nonbool_locals() {
        let span = Span::new(0, 0);
        let mut immutable = parsed_program("fn subject() {}");
        immutable.fns[0].body.push(Stmt::Decl {
            ty: affine_bool_option(),
            name: "pending".into(),
            name_span: span,
            init: Some(Expr {
                kind: ExprKind::NoneE,
                span,
                ty: Some(affine_bool_option()),
            }),
            mutable: false,
        });
        assert!(public_generate_error(&immutable).starts_with("vc.affine_option_immutable:"));

        let mut nonbool = parsed_program("fn subject() {}");
        let nonbool_ty = Ty::affine_array_option(Ty::Int(IntTy::U8));
        nonbool.fns[0].body.push(Stmt::Decl {
            ty: nonbool_ty.clone(),
            name: "pending".into(),
            name_span: span,
            init: Some(Expr {
                kind: ExprKind::NoneE,
                span,
                ty: Some(nonbool_ty),
            }),
            mutable: true,
        });
        assert!(public_generate_error(&nonbool).starts_with("vc.affine_option_payload:"));
    }

    #[test]
    fn affine_option_take_cannot_replace_its_source_place_in_forged_ast() {
        let span = Span::new(0, 0);
        let mut program = parsed_program("fn subject() {}");
        program.fns[0].body.extend([
            Stmt::Decl {
                ty: affine_bool_option(),
                name: "pending".into(),
                name_span: span,
                init: Some(Expr {
                    kind: ExprKind::NoneE,
                    span,
                    ty: Some(affine_bool_option()),
                }),
                mutable: true,
            },
            Stmt::Decl {
                ty: Ty::array(Ty::Bool),
                name: "pending".into(),
                name_span: span,
                init: Some(Expr {
                    kind: ExprKind::OptTake {
                        option: "pending".into(),
                        option_span: span,
                    },
                    span,
                    ty: Some(Ty::array(Ty::Bool)),
                }),
                mutable: false,
            },
        ]);
        assert!(public_generate_error(&program).starts_with("vc.duplicate_local:"));
    }

    #[test]
    fn exposure_return_rejection_comes_from_control_sealing_not_vc_resummary() {
        let span = Span::new(0, 0);
        let mut program = parsed_program("fn subject(&[u8] bytes) {}");
        program.fns[0].body.push(Stmt::Expose {
            kw_span: span,
            array: "bytes".into(),
            array_span: span,
            mutable: false,
            ptr: "ptr".into(),
            ptr_span: span,
            res: "mem".into(),
            res_span: span,
            body: vec![Stmt::If {
                cond: Expr {
                    kind: ExprKind::BoolLit(true),
                    span,
                    ty: Some(Ty::Bool),
                },
                then_block: vec![Stmt::Return { value: None, span }],
                else_block: None,
            }],
        });

        validate_vc_type_domain(&program)
            .expect("VC type preflight no longer reconstructs exposure flow");
        let error = crate::control::ControlProgram::build(&program)
            .expect_err("control sealing rejects a return that bypasses reconstruction");
        assert!(
            error.message.contains("return inside an exposure"),
            "{}",
            error.message
        );
    }

    #[test]
    fn deleting_an_exposure_normal_path_after_checking_fails_closed() {
        let source = r#"
fn subject(u64 n) {
    mut [u8] bytes = alloc_array<u8>(n, 0);
    unsafe expose &mut bytes as (ptr, resource mem) {
    }
}
"#;
        let (mut program, checked) = checked_program(source);
        let Stmt::Expose { body, .. } = &mut program.fns[0].body[1] else {
            panic!("fixture has an exposure")
        };
        body.push(Stmt::Return {
            value: None,
            span: Span::new(0, 0),
        });
        let error = match generate(&program, &checked, source, Path::new(".")) {
            Err(error) => error,
            Ok(_) => panic!("a forged exposure path cannot erase its checked normal phase"),
        };
        assert!(
            error.starts_with("internal.vcgen.control_plan_shape_mismatch:"),
            "{error}"
        );
    }

    #[test]
    fn checked_control_routes_remove_dead_names_from_later_clause_scopes() {
        let source = r#"
fn route_scope(&[u8] bytes, bool choose) {
    u64 outer = 7;
    if (choose) {
        u64 then_local = 1;
        mut [bool] flags = [true, false];
    } else {
        u64 else_local = 2;
    }
    /// assert outer = 7
    unsafe expose &bytes as (ptr, resource mem) {
        u64 exposure_local = 3;
        unsafe {
            u64 unsafe_local = 4;
        }
    }
    /// assert outer = 7
}
"#;
        let (program, checked) = checked_program(source);
        let generated = generate(&program, &checked, source, Path::new("."))
            .expect("every lexical continuation consumes its checked route");
        let assertions: Vec<&ClauseWf> = generated
            .clause_wfs
            .iter()
            .filter(|wf| wf.desc == "`assert` in `route_scope`")
            .collect();
        // Each source assertion is visited once per symbolic branch. Keep
        // both visits visible, and group by source site rather than DFS order.
        assert_eq!(assertions.len(), 4);
        let mut by_site: HashMap<(usize, usize), Vec<&ClauseWf>> = HashMap::new();
        for wf in &assertions {
            by_site
                .entry((wf.span.start, wf.span.end))
                .or_default()
                .push(*wf);
        }
        assert_eq!(by_site.len(), 2);
        assert!(by_site.values().all(|visits| visits.len() == 2));

        let names = |wf: &ClauseWf| {
            wf.binders
                .iter()
                .map(|(name, _)| name.clone())
                .collect::<HashSet<_>>()
        };
        for wf in &assertions {
            let visible = names(wf);
            for live in ["bytes", "choose", "outer"] {
                assert!(visible.contains(live), "missing live binder `{live}`");
            }
            for dead in ["then_local", "else_local", "flags"] {
                assert!(
                    !visible.contains(dead),
                    "dead branch binder `{dead}` escaped its route"
                );
            }
        }

        let post_exposure = by_site
            .iter()
            .max_by_key(|((start, _), _)| *start)
            .expect("the later assertion follows the exposure")
            .1;
        for wf in post_exposure {
            let visible = names(wf);
            for dead in ["ptr", "mem", "exposure_local", "unsafe_local"] {
                assert!(
                    !visible.contains(dead),
                    "dead exposure binder `{dead}` escaped its route"
                );
            }
        }
    }

    #[test]
    fn returning_symbolic_paths_restore_parent_types_and_old_state_for_siblings() {
        let source = r#"
fn route_return(&mut [bool] bits, bool stop) {
    u64 outer = 7;
    if (stop) {
        return;
    }
    /// assert outer = 7
}

fn route_loop_return(&mut [bool] bits, bool stop) {
    u64 outer = 7;
    /// invariant true
    /// variant 0
    while (stop) {
        u64 loop_local = 1;
        return;
    }
    /// assert outer = 7
}
"#;
        let (program, checked) = checked_program(source);
        let generated = generate(&program, &checked, source, Path::new("."))
            .expect("a returning path must not clear its sibling's symbolic maps");
        for function in ["route_return", "route_loop_return"] {
            let wf = generated
                .clause_wfs
                .iter()
                .find(|wf| wf.desc == format!("`assert` in `{function}`"))
                .expect("the post-control assertion has a WF declaration");
            let names: HashSet<&str> = wf.binders.iter().map(|(name, _)| name.as_str()).collect();
            for live in ["bits", "_old_bits", "outer", "stop"] {
                assert!(names.contains(live), "{function} lost `{live}`");
            }
            assert!(!names.contains("loop_local"));
        }
    }

    #[test]
    fn retained_branch_loop_and_exposure_normal_edges_drive_generation() {
        let source = r#"
fn structural_edges(u64 limit, bool choose) {
    mut [u8] bytes = alloc_array<u8>(limit, 0);
    if (choose) {
        u64 then_local = 1;
        /// assert then_local = 1
    } else {
        u64 else_local = 2;
        /// assert else_local = 2
    }
    mut u64 index = 0;
    /// invariant index ≤ limit
    /// variant limit - index
    while (index < limit) {
        index = index + 1;
    }
    unsafe expose &mut bytes as (pointer, resource memory) {
        u64 exposure_local = 3;
        /// assert exposure_local = 3
    }
    /// assert index = limit
}
"#;
        let (program, checked) = checked_program(source);
        let generated = generate(&program, &checked, source, Path::new("."))
            .expect("all retained normal structural edges should generate");
        assert!(generated.obligations.iter().any(|obligation| {
            obligation
                .name
                .starts_with("structural_edges.inv_preserved")
        }));
        assert!(
            generated
                .obligations
                .iter()
                .any(|obligation| obligation.name == "structural_edges.expose.bytes.extent")
        );
        assert!(
            generated
                .obligations
                .iter()
                .any(|obligation| obligation.name == "structural_edges.expose.bytes.bytes")
        );
        let assertion_count = generated
            .obligations
            .iter()
            .filter(|obligation| obligation.name.starts_with("structural_edges.assert."))
            .count();
        assert_eq!(assertion_count, 6);
    }

    #[test]
    fn checked_control_shape_refuses_deleted_else_and_moved_or_reshaped_returns() {
        let else_source = r#"
fn erased_else(bool flag) {
    if (flag) {
    } else {
        /// assert false
    }
}
"#;
        let (mut else_program, else_checked) = checked_program(else_source);
        let Stmt::If { else_block, .. } = &mut else_program.fns[0].body[0] else {
            panic!("fixture has an if statement")
        };
        *else_block = None;
        let deleted = match generate(&else_program, &else_checked, else_source, Path::new(".")) {
            Err(error) => error,
            Ok(_) => panic!("deleting a checked else arm must fail closed"),
        };
        assert!(
            deleted.starts_with("internal.vcgen.control_plan_shape_mismatch:"),
            "{deleted}"
        );

        let return_source = "fn moved_return(bool flag) { if (flag) {} return; }";
        let (mut return_program, return_checked) = checked_program(return_source);
        let return_statement = return_program.fns[0].body.pop().expect("checked return");
        let Stmt::If { then_block, .. } = &mut return_program.fns[0].body[0] else {
            panic!("fixture has an if statement")
        };
        then_block.push(return_statement);
        let moved = match generate(
            &return_program,
            &return_checked,
            return_source,
            Path::new("."),
        ) {
            Err(error) => error,
            Ok(_) => panic!("moving a checked return into another scope must fail closed"),
        };
        assert!(
            moved.starts_with("internal.vcgen.control_plan_shape_mismatch:"),
            "{moved}"
        );

        let shape_source = "fn reshaped_return() { return; }";
        let (mut shape_program, shape_checked) = checked_program(shape_source);
        let Stmt::Return { value, span } = &mut shape_program.fns[0].body[0] else {
            panic!("fixture has a return statement")
        };
        *value = Some(Expr {
            kind: ExprKind::IntLit(1),
            span: *span,
            ty: Some(Ty::Int(IntTy::U64)),
        });
        let reshaped = match generate(&shape_program, &shape_checked, shape_source, Path::new("."))
        {
            Err(error) => error,
            Ok(_) => {
                panic!("changing a checked unit return into a valued return must fail closed")
            }
        };
        assert!(
            reshaped.starts_with("internal.vcgen.control_plan_shape_mismatch:"),
            "{reshaped}"
        );

        let nested_source = "fn moved_if(bool first, bool second) { if (first) {} if (second) {} }";
        let (mut nested_program, nested_checked) = checked_program(nested_source);
        let moved_if = nested_program.fns[0].body.pop().expect("second checked if");
        let Stmt::If { then_block, .. } = &mut nested_program.fns[0].body[0] else {
            panic!("fixture starts with an if statement")
        };
        then_block.push(moved_if);
        let nested = match generate(
            &nested_program,
            &nested_checked,
            nested_source,
            Path::new("."),
        ) {
            Err(error) => error,
            Ok(_) => panic!("moving a checked control subtree must fail closed"),
        };
        assert!(
            nested.starts_with("internal.vcgen.control_plan_shape_mismatch:"),
            "{nested}"
        );

        let fallthrough_source = "fn erased_return() -> u64 { return 1; }";
        let (mut fallthrough_program, fallthrough_checked) = checked_program(fallthrough_source);
        fallthrough_program.fns[0].body.clear();
        let fallthrough = match generate(
            &fallthrough_program,
            &fallthrough_checked,
            fallthrough_source,
            Path::new("."),
        ) {
            Err(error) => error,
            Ok(_) => panic!("a non-unit checked return may not be erased"),
        };
        assert!(
            fallthrough.starts_with("internal.vcgen.control_plan_shape_mismatch:"),
            "{fallthrough}"
        );
    }

    #[test]
    fn checked_trap_sites_cover_nested_normal_source_translation() {
        let source = r#"
fn trap_callee(u64 x) -> u64 {
    return x;
}

/// pre i < values.len
/// pre x < u64.max
fn trap_source(&mut [u64] values, u64 i, u64 x) {
    /// assert i < values.len
    values[i] = trap_callee(x + 1);
    [u64] scratch = alloc_array<u64>(1, x);
    /// assert scratch.len = 1
}
"#;
        let (program, checked) = checked_program(source);
        let generated = generate(&program, &checked, source, Path::new("."))
            .expect("nested statement/expression traps must consume the retained no-unwind plan");

        assert!(
            generated
                .obligations
                .iter()
                .any(|obligation| obligation.name.starts_with("trap_source.assert."))
        );
        assert!(
            generated
                .obligations
                .iter()
                .any(|obligation| obligation.name.starts_with("trap_source.bounds."))
        );
        assert!(
            generated
                .obligations
                .iter()
                .any(|obligation| obligation.name.starts_with("trap_source.overflow."))
        );
        // Allocation failure and a callee trapping are operational-only
        // edges. Their exact source sites are consumed by expression entry,
        // while VC generation continues to reason about normal return only.
    }

    #[test]
    fn checked_trap_shape_refuses_deleted_and_semantically_replaced_sites() {
        let source = "fn trap_forge(u64 x) -> u64 { return x + 1; }";

        let (mut deleted_program, deleted_checked) = checked_program(source);
        let Stmt::Return {
            value: Some(deleted),
            ..
        } = &mut deleted_program.fns[0].body[0]
        else {
            panic!("fixture returns the trapping expression")
        };
        let ExprKind::Binary { lhs, .. } = &deleted.kind else {
            panic!("fixture return is an addition")
        };
        *deleted = (**lhs).clone();
        let deleted_error =
            match generate(&deleted_program, &deleted_checked, source, Path::new(".")) {
                Err(error) => error,
                Ok(_) => {
                    panic!("deleting a checked trap site must fail before symbolic execution")
                }
            };
        assert!(
            deleted_error.starts_with("internal.vcgen.control_plan_shape_mismatch:"),
            "{deleted_error}"
        );
        assert!(deleted_error.contains("trap"), "{deleted_error}");

        let (mut replaced_program, replaced_checked) = checked_program(source);
        let Stmt::Return {
            value: Some(replaced),
            ..
        } = &mut replaced_program.fns[0].body[0]
        else {
            panic!("fixture returns the trapping expression")
        };
        let ExprKind::Binary { op, .. } = &mut replaced.kind else {
            panic!("fixture return is an addition")
        };
        *op = BinOp::Sub;
        let replaced_error =
            match generate(&replaced_program, &replaced_checked, source, Path::new(".")) {
                Err(error) => error,
                Ok(_) => {
                    panic!("replacing one checked trap semantic with another must fail closed")
                }
            };
        assert!(
            replaced_error.starts_with("internal.vcgen.control_plan_shape_mismatch:"),
            "{replaced_error}"
        );
        assert!(replaced_error.contains("trap"), "{replaced_error}");
    }

    #[test]
    fn affine_option_cannot_launder_through_named_receivers_or_generated_bindings() {
        let span = Span::new(0, 0);
        let scalar = || Expr {
            kind: ExprKind::IntLit(0),
            span,
            ty: Some(Ty::Int(IntTy::U64)),
        };
        let expressions = vec![
            ExprKind::MethodCall {
                recv: "pending".into(),
                recv_span: span,
                method: "m".into(),
                method_span: span,
                args: Vec::new(),
            },
            ExprKind::ClassField {
                obj: "pending".into(),
                obj_span: span,
                field: "f".into(),
            },
            ExprKind::RecordField {
                obj: "pending".into(),
                obj_span: span,
                field: "f".into(),
            },
            ExprKind::ClassFieldLen {
                obj: "pending".into(),
                field: "f".into(),
            },
            ExprKind::ClassFieldIndex {
                obj: "pending".into(),
                obj_span: span,
                field: "f".into(),
                index: Box::new(scalar()),
            },
            ExprKind::Borrow {
                array: "pending".into(),
                field: None,
                mutable: false,
            },
            ExprKind::Len {
                array: "pending".into(),
            },
        ];
        for kind in expressions {
            let expression = Expr {
                kind,
                span,
                ty: Some(Ty::Int(IntTy::U64)),
            };
            let mut locals = HashMap::from([("pending".into(), affine_bool_option())]);
            let error = validate_vc_block(
                &[Stmt::ExprStmt(expression)],
                false,
                "forged affine receiver",
                &mut locals,
            )
            .expect_err("affine named receiver must fail closed");
            assert!(
                error.starts_with("vc.affine_option_boundary:")
                    || error.contains("is not an active array"),
                "{error}"
            );
        }

        let mut locals = HashMap::from([("pending".into(), affine_bool_option())]);
        let expose = Stmt::Expose {
            kw_span: span,
            array: "pending".into(),
            array_span: span,
            mutable: false,
            ptr: "p".into(),
            ptr_span: span,
            res: "r".into(),
            res_span: span,
            body: Vec::new(),
        };
        assert!(
            validate_vc_block(&[expose], false, "forged expose", &mut locals)
                .unwrap_err()
                .starts_with("vc.affine_option_boundary:")
        );

        let mut locals = HashMap::from([("pending".into(), affine_bool_option())]);
        let allocation = Stmt::StaticAlloc {
            kw_span: span,
            size: scalar(),
            ptr: "pending".into(),
            ptr_span: span,
            res: "pending".into(),
            res_span: span,
        };
        assert!(
            validate_vc_block(&[allocation], false, "forged allocation", &mut locals)
                .unwrap_err()
                .starts_with("vc.duplicate_local:")
        );
    }

    #[test]
    fn retained_templates_require_canonical_scalar_parameters() {
        let parameter = TypeParamId::from_legacy(3);
        assert!(validate_vc_ty(Ty::Param(parameter), true, "test template").is_ok());
        let error = validate_vc_ty(Ty::Int(IntTy::TParam(3)), true, "test template")
            .expect_err("legacy declaration-position parameter must fail closed");
        assert!(error.contains("non-canonical legacy scalar parameter"));
    }

    #[test]
    fn semantic_type_lookup_preserves_unannotated_resource_places() {
        let ty = Ty::Res(ResKind::RawSpan);
        let locals = HashMap::from([("whole".to_string(), ty.clone())]);
        let place = Expr {
            kind: ExprKind::Var("whole".into()),
            span: Span::new(0, 0),
            ty: None,
        };
        assert_eq!(
            vc_semantic_expr_ty(&place, &locals, "sealed resource operand").unwrap(),
            ty
        );
    }

    #[test]
    fn bool_options_have_a_distinct_proof_model() {
        assert_eq!(lean_option_ty(&Ty::Bool, &[]), "Option Bool");
        assert!(validate_vc_ty(Ty::option(Ty::Bool), false, "unused ordinary function").is_ok());
        assert_eq!(lean_array_ty(&Ty::Bool, &[]), "Sable.Seq Bool");
    }

    #[test]
    fn pod_record_payloads_split_by_container() {
        let record_error =
            validate_vc_ty(Ty::option(Ty::Record(0)), false, "unused ordinary function")
                .expect_err("POD-record options are represented but have no proof semantics");
        assert!(record_error.contains("POD-record option payload"));
        validate_vc_ty(Ty::array(Ty::Record(0)), false, "unused ordinary function")
            .expect("record elements have proof semantics (Sable.Seq over the structure)");
    }

    #[test]
    fn unsupported_option_positions_fail_in_vc_preflight() {
        // A concrete value payload binds as a parameter; every other
        // position keeps its refusal, and so does the type-parameter
        // payload, which check refuses first (`type.option_param`).
        validate_vc_type_position(
            Ty::option(Ty::Bool),
            false,
            VcTypePosition::Parameter,
            "synthetic declaration",
        )
        .expect("a value-payload option parameter binds Option Bool");
        let error = validate_vc_type_position(
            Ty::option(Ty::Param(TypeParamId::from_legacy(0))),
            true,
            VcTypePosition::Parameter,
            "synthetic declaration",
        )
        .expect_err("a type-parameter option payload has no parameter transport");
        assert!(
            error.contains("non-value-payload option parameters"),
            "{error}"
        );
        for (position, expected) in [
            (VcTypePosition::TraitParameter, "trait option parameters"),
            (VcTypePosition::TraitReturn, "trait option returns"),
        ] {
            let error = validate_vc_type_position(
                Ty::option(Ty::Bool),
                false,
                position,
                "synthetic declaration",
            )
            .expect_err("unsupported option position must fail before VC generation");
            assert!(error.contains(expected));
        }
        validate_vc_type_position(
            Ty::option(Ty::Bool),
            false,
            VcTypePosition::ClassField,
            "synthetic declaration",
        )
        .expect("a concrete value-payload option class field has VC field state");
        let error = validate_vc_type_position(
            Ty::option(Ty::Param(TypeParamId::from_legacy(0))),
            true,
            VcTypePosition::ClassField,
            "synthetic declaration",
        )
        .expect_err("a type-parameter option payload has no stored-field state");
        assert!(
            error.contains("non-value-payload option class fields"),
            "{error}"
        );
    }

    /// An owned Boolean array is a local value; a borrowed one names a
    /// sequence its caller owns and goes wherever a borrowed array goes.
    /// Which positions a borrow may be *written* in is the parser's row and
    /// `check::borrow_referent_ty`'s to state, not this gate's.
    #[test]
    fn an_owned_bool_array_is_a_local_value_in_vc_preflight() {
        for position in [VcTypePosition::Expression, VcTypePosition::Local] {
            validate_vc_type_position(Ty::array(Ty::Bool), false, position, "synthetic local")
                .expect("an owned Boolean array is a local value");
        }

        for mutability in [Mutability::Shared, Mutability::Mut] {
            for position in [
                VcTypePosition::Expression,
                VcTypePosition::Parameter,
                VcTypePosition::TraitParameter,
                VcTypePosition::Borrow,
            ] {
                validate_vc_type_position(
                    Ty::array_ref(Ty::Bool, mutability),
                    false,
                    position,
                    "synthetic declaration",
                )
                .unwrap_or_else(|error| {
                    panic!("a borrowed Boolean array carries a proof model here: {error}")
                });
            }
            // ...but not as a *local*. The symbolic environment is keyed by
            // source name and each key is assumed to be the only name for its
            // storage; a borrow local would be a second one (ADR 0072).
            let error = validate_vc_type_position(
                Ty::array_ref(Ty::Bool, mutability),
                false,
                VcTypePosition::Local,
                "synthetic declaration",
            )
            .expect_err("a borrow is not a local binding");
            assert!(error.contains("not a local binding"));
        }

        validate_vc_type_position(
            Ty::array(Ty::Bool),
            false,
            VcTypePosition::ClassField,
            "synthetic declaration",
        )
        .expect("a Boolean array is class-field state");
        // A return hands the owner over (ADR 0085), so it joins the
        // positions an owned Boolean array occupies.
        validate_vc_type_position(
            Ty::array(Ty::Bool),
            false,
            VcTypePosition::Return,
            "synthetic return",
        )
        .expect("a returned Boolean array is a value the callee hands over");
        // A parameter joins the return: both halves of a call transfer an
        // owner (ADR 0085).
        validate_vc_type_position(
            Ty::array(Ty::Bool),
            false,
            VcTypePosition::Parameter,
            "synthetic parameter",
        )
        .expect("an owned Boolean array is handed over at a call");
        for position in [
            VcTypePosition::TraitParameter,
            VcTypePosition::RecordField,
            VcTypePosition::Borrow,
        ] {
            let error = validate_vc_type_position(
                Ty::array(Ty::Bool),
                false,
                position,
                "synthetic declaration",
            )
            .expect_err("an owned Boolean array boundary must fail before symbolic evaluation");
            assert!(error.contains("an owned Boolean array is a local value"));
        }

        validate_vc_type_position(
            Ty::array(Ty::Record(0)),
            false,
            VcTypePosition::Local,
            "synthetic local",
        )
        .expect("a record-array local has VC state");
        for payload in [Ty::Param(TypeParamId::from_legacy(0))] {
            let error = validate_vc_type_position(
                Ty::array(payload.clone()),
                false,
                VcTypePosition::Local,
                "synthetic local",
            )
            .expect_err("non-Boolean future payloads stay independently closed");
            assert!(error.contains("escaped monomorphization"));
        }
    }

    #[test]
    fn bool_array_preflight_rejects_a_forged_owner_crossing_a_boundary() {
        let span = Span::new(0, 1);
        let array_ty = Ty::array(Ty::Bool);
        let mut locals = HashMap::from([("bits".to_string(), array_ty.clone())]);
        // Lending the owner is ordinary: the borrow produces no new owner.
        let borrowed = Expr {
            kind: ExprKind::Borrow {
                array: "bits".into(),
                field: None,
                mutable: false,
            },
            span,
            ty: Some(Ty::array_ref(Ty::Bool, Mutability::Shared)),
        };
        validate_vc_expr(&borrowed, false, "array borrow", &locals)
            .expect("a Boolean array borrow is an ordinary value");

        // An ordinary call is where an owner is handed over (ADR 0085). The
        // member boundary is not, and forging one still fails closed.
        let owned_argument = || Expr {
            kind: ExprKind::Var("bits".into()),
            span,
            ty: Some(array_ty.clone()),
        };
        let call = Expr {
            kind: ExprKind::Call {
                callee: "sink".into(),
                callee_span: span,
                type_args: Vec::new(),
                args: vec![owned_argument()],
            },
            span,
            ty: Some(Ty::Unit),
        };
        validate_vc_expr(&call, false, "handing an owner over", &locals)
            .expect("an owned Boolean array is handed over at an ordinary call");

        let ctor = Expr {
            kind: ExprKind::CtorCall {
                class: "Holder".into(),
                class_span: span,
                init: "with".into(),
                type_args: Vec::new(),
                args: vec![owned_argument()],
            },
            span,
            ty: Some(Ty::Unit),
        };
        let error = validate_vc_expr(&ctor, false, "forged constructor", &locals)
            .expect_err("forged Boolean array constructor argument must fail closed");
        assert!(error.contains("call boundary"), "{error}");

        let expose = Stmt::Expose {
            kw_span: span,
            array: "bits".into(),
            array_span: span,
            mutable: true,
            ptr: "p".into(),
            ptr_span: span,
            res: "mem".into(),
            res_span: span,
            body: Vec::new(),
        };
        let error = validate_vc_block(&[expose], false, "forged exposure", &mut locals)
            .expect_err("forged Boolean array exposure must fail closed");
        assert!(error.contains("exposure"));
    }

    #[test]
    fn bool_array_preflight_rejects_initializer_free_owned_local() {
        let source = r#"
fn subject() {
    [bool] bits = alloc_array<bool>(1, false);
}
"#;
        let (mut program, _) = checked_program(source);
        let Stmt::Decl { init, .. } = &mut program.fns[0].body[0] else {
            panic!("expected explicit Boolean array declaration")
        };
        *init = None;

        let error = validate_vc_type_domain(&program)
            .expect_err("initializer-free Boolean array must fail before generation");
        assert!(error.contains("must be initialized"));

        let parameter = TypeParamId::from_legacy(0);
        assert!(
            validate_vc_type_position(
                Ty::array(Ty::Param(parameter)),
                true,
                VcTypePosition::Local,
                "retained template",
            )
            .is_ok()
        );
    }

    #[test]
    fn bool_array_preflight_rejects_alias_initialization_and_rebinding() {
        let source = r#"
fn subject() {
    [bool] first = alloc_array<bool>(1, false);
    [bool] second = alloc_array<bool>(1, true);
}
"#;
        let (program, _) = checked_program(source);
        let Stmt::Decl {
            init: Some(first), ..
        } = &program.fns[0].body[0]
        else {
            panic!("expected first Boolean array declaration")
        };
        let first_span = first.span;
        let mut aliased = program.clone();
        let Stmt::Decl {
            init: Some(second), ..
        } = &mut aliased.fns[0].body[1]
        else {
            panic!("expected second Boolean array declaration")
        };
        *second = Expr {
            kind: ExprKind::Var("first".into()),
            span: first_span,
            ty: Some(Ty::array(Ty::Bool)),
        };
        let error = validate_vc_type_domain(&aliased)
            .expect_err("Boolean array alias initialization must fail closed");
        assert!(error.contains("literal, allocation, or affine-option take"));

        let mut rebound = program;
        rebound.fns[0].body.push(Stmt::Assign {
            name: "first".into(),
            name_span: first_span,
            value: Expr {
                kind: ExprKind::Var("second".into()),
                span: first_span,
                ty: Some(Ty::array(Ty::Bool)),
            },
        });
        let error = validate_vc_type_domain(&rebound)
            .expect_err("Boolean array rebinding must fail closed");
        assert!(error.contains("cannot be rebound"));
    }

    #[test]
    fn bool_array_preflight_rejects_option_operator_laundering() {
        let span = Span::new(0, 1);
        let array_ty = Ty::array(Ty::Bool);
        let locals = HashMap::from([("bits".to_string(), array_ty.clone())]);
        let bits = || Expr {
            kind: ExprKind::Var("bits".into()),
            span,
            ty: Some(array_ty.clone()),
        };

        let forged = [
            (
                Expr {
                    kind: ExprKind::SomeE(Box::new(bits())),
                    span,
                    ty: Some(Ty::option(Ty::Bool)),
                },
                "some",
            ),
            (
                Expr {
                    kind: ExprKind::IsSome {
                        operand: Box::new(bits()),
                    },
                    span,
                    ty: Some(Ty::Bool),
                },
                "is_some",
            ),
            (
                Expr {
                    kind: ExprKind::OptValue {
                        operand: Box::new(bits()),
                    },
                    span,
                    ty: Some(Ty::Bool),
                },
                "value",
            ),
        ];

        for (expr, operator) in forged {
            let error = validate_vc_expr(&expr, false, "forged option operator", &locals)
                .expect_err("Boolean array must not enter an option operator");
            assert!(error.contains(operator), "unexpected error: {error}");
        }
    }

    #[test]
    fn bool_array_preflight_rejects_scalar_operator_laundering() {
        let span = Span::new(0, 1);
        let array_ty = Ty::array(Ty::Bool);
        let locals = HashMap::from([("bits".to_string(), array_ty.clone())]);
        let bits = || Expr {
            kind: ExprKind::Var("bits".into()),
            span,
            ty: Some(array_ty.clone()),
        };
        let int = || Expr {
            kind: ExprKind::IntLit(1),
            span,
            ty: Some(Ty::Int(IntTy::U64)),
        };
        let boolean = || Expr {
            kind: ExprKind::BoolLit(true),
            span,
            ty: Some(Ty::Bool),
        };

        let forged = [
            Expr {
                kind: ExprKind::Widen {
                    target: IntTy::U64,
                    arg: Box::new(bits()),
                },
                span,
                ty: Some(Ty::Int(IntTy::U64)),
            },
            Expr {
                kind: ExprKind::Narrow {
                    target: IntTy::U64,
                    arg: Box::new(bits()),
                },
                span,
                ty: Some(Ty::Int(IntTy::U64)),
            },
            Expr {
                kind: ExprKind::Unary {
                    op: UnOp::Neg,
                    operand: Box::new(bits()),
                },
                span,
                ty: Some(Ty::Int(IntTy::I64)),
            },
            Expr {
                kind: ExprKind::Unary {
                    op: UnOp::Not,
                    operand: Box::new(bits()),
                },
                span,
                ty: Some(Ty::Bool),
            },
            Expr {
                kind: ExprKind::Binary {
                    op: BinOp::Add,
                    op_span: span,
                    lhs: Box::new(bits()),
                    rhs: Box::new(int()),
                },
                span,
                ty: Some(Ty::Int(IntTy::U64)),
            },
            Expr {
                kind: ExprKind::Binary {
                    op: BinOp::Eq,
                    op_span: span,
                    lhs: Box::new(bits()),
                    rhs: Box::new(int()),
                },
                span,
                ty: Some(Ty::Bool),
            },
            Expr {
                kind: ExprKind::Binary {
                    op: BinOp::And,
                    op_span: span,
                    lhs: Box::new(bits()),
                    rhs: Box::new(boolean()),
                },
                span,
                ty: Some(Ty::Bool),
            },
        ];

        for expr in forged {
            let error = validate_vc_expr(&expr, false, "forged scalar operator", &locals)
                .expect_err("Boolean array must not enter a scalar operator");
            assert!(
                error.contains("operand/result") || error.contains("integer operands"),
                "unexpected error: {error}"
            );
        }
    }

    #[test]
    fn bool_array_preflight_rejects_scalar_statement_operands() {
        let span = Span::new(0, 1);
        let bool_array = Ty::array(Ty::Bool);
        let int_array = Ty::array(Ty::Int(IntTy::U64));
        let mut locals = HashMap::from([
            ("bits".to_string(), bool_array.clone()),
            ("numbers".to_string(), int_array),
        ]);
        let bits = || Expr {
            kind: ExprKind::Var("bits".into()),
            span,
            ty: Some(bool_array.clone()),
        };
        let integer = || Expr {
            kind: ExprKind::IntLit(0),
            span,
            ty: Some(Ty::Int(IntTy::U64)),
        };

        let forged_store = Stmt::Store {
            array: "numbers".into(),
            array_span: span,
            index: bits(),
            value: integer(),
        };
        let error = validate_vc_block(
            &[forged_store],
            false,
            "forged integer-array store",
            &mut locals,
        )
        .expect_err("Boolean array must not be an integer-array store index");
        assert!(error.contains("array-store index"));

        let forged_if = Stmt::If {
            cond: bits(),
            then_block: Vec::new(),
            else_block: None,
        };
        let error = validate_vc_block(&[forged_if], false, "forged condition", &mut locals)
            .expect_err("Boolean array must not be an `if` condition");
        assert!(error.contains("`if` condition"));
    }

    #[test]
    fn bool_array_symbolics_use_bool_values_without_numeric_element_ranges() {
        let source = r#"
/// post result
fn bool_array_local(bool seed) -> bool {
    mut [bool] bits = alloc_array<bool>(2, seed);
    bits[1] = !seed;
    return bits[1];
}
"#;
        let (program, checked) = checked_program(source);
        let generated = generate(&program, &checked, source, std::path::Path::new("."))
            .expect("owned Boolean locals should stay inside the VC type domain");

        assert!(generated.obligations.iter().any(|obligation| {
            obligation
                .binders
                .iter()
                .any(|(name, ty)| name == "bits" && ty == "Sable.Seq Bool")
        }));
        assert!(generated.obligations.iter().all(|obligation| {
            obligation.hyps.iter().all(|(_, proposition)| {
                !proposition.contains("≤ bits.get") && !proposition.contains("bits.get k ≤")
            })
        }));
        assert!(generated.obligations.iter().any(|obligation| {
            obligation.hyps.iter().any(|(name, proposition)| {
                name == "h_result"
                    && proposition.contains(".get 1")
                    && proposition.contains("= true")
            })
        }));
        assert!(generated.obligations.iter().any(|obligation| {
            obligation.hyps.iter().any(|(_, proposition)| {
                proposition.contains("∀ k") && proposition.contains(".get k = (@decide")
            })
        }));
    }

    #[test]
    fn bool_array_loop_havoc_keeps_the_seq_bool_type() {
        let source = r#"
fn bool_array_loop(u64 n, bool seed) {
    mut [bool] bits = alloc_array<bool>(n, seed);
    mut u64 i = 0;
    /// invariant bits.len = n
    /// variant n - i
    while (i < n) {
        u64 loop_local = i;
        bits[i] = !bits[i];
        i = i + 1;
    }
}
"#;
        let (program, checked) = checked_program(source);
        let generated = generate(&program, &checked, source, std::path::Path::new("."))
            .expect("Boolean array loop havoc should remain in the concrete Bool model");
        let preservation = generated
            .obligations
            .iter()
            .find(|obligation| obligation.name.starts_with("bool_array_loop.inv_preserved"))
            .expect("loop should emit an invariant-preservation obligation");

        assert!(
            preservation
                .binders
                .iter()
                .any(|(name, ty)| name == "bits" && ty == "Sable.Seq Bool")
        );
        assert!(preservation.binders.iter().any(|(name, ty)| {
            name.starts_with("_old") && name.ends_with("_bits") && ty == "Sable.Seq Bool"
        }));
        assert!(
            preservation
                .binders
                .iter()
                .all(|(name, _)| name != "loop_local"),
            "loop-body locals must be cleared by the checked backedge route before preservation"
        );
        assert!(preservation.hyps.iter().all(|(name, proposition)| {
            name != "h_bits_elems"
                && !proposition.contains("≤ bits.get")
                && !proposition.contains("bits.get k ≤")
        }));
    }

    fn minimal_fn() -> Fn {
        Fn {
            is_pub: false,
            extern_info: None,
            name: "probe".to_string(),
            name_span: Span::new(0, 0),
            type_params: Vec::new(),
            type_bounds: Vec::new(),
            requires: Vec::new(),
            proof_reuse: ProofReuse::None,
            params: Vec::new(),
            ret: Ty::Unit,
            pres: Vec::new(),
            posts: Vec::new(),
            variant: None,
            body: Vec::new(),
            span: Span::new(0, 0),
        }
    }

    fn empty_result() -> VcResult {
        VcResult {
            ghosts: Vec::new(),
            classes: Vec::new(),
            records: Vec::new(),
            clause_wfs: Vec::new(),
            obligations: Vec::new(),
            transition_certificates: Vec::new(),
            argument_schedule_certificates: Vec::new(),
            trust: TrustManifest::default(),
            machine: MachineManifest::default(),
        }
    }

    /// Drive a bare generator (no program around it) so the havoc helpers
    /// can be probed on shapes no checked source program can spell.
    fn with_generator<R>(probe: impl FnOnce(&mut Generator) -> R) -> R {
        let f = minimal_fn();
        let classes: Vec<ClassDecl> = Vec::new();
        let records: Vec<RecordDecl> = Vec::new();
        let sigs: HashMap<String, FnSig> = HashMap::new();
        let ownership = CheckedOwnershipPlan::default();
        let fn_map: HashMap<&str, &Fn> = HashMap::new();
        let class_map: HashMap<&str, &ClassDecl> = HashMap::new();
        let mut out = empty_result();
        let mut generator = Generator {
            f: &f,
            fname: "probe".to_string(),
            call_owner: CallOwner::Function("probe".to_string()),
            cctx: Cctx::None,
            control: None,
            classes: &classes,
            records: &records,
            sigs: &sigs,
            ownership: &ownership,
            visited_checked_calls: HashSet::new(),
            checked_call_visits: HashMap::new(),
            checked_slot_visits: HashMap::new(),
            visited_option_takes: HashSet::new(),
            visited_slot_transitions: HashSet::new(),
            visited_slot_actions: HashSet::new(),
            visited_exposures: HashSet::new(),
            visited_sealed_operations: HashSet::new(),
            visited_loops: HashSet::new(),
            visited_value_transfers: HashSet::new(),
            visited_assignments: HashSet::new(),
            visited_field_assignments: HashSet::new(),
            visited_temporary_drops: HashSet::new(),
            fn_map: &fn_map,
            class_map: &class_map,
            source: "",
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
            out: &mut out,
        };
        probe(&mut generator)
    }

    fn checked_havoc_call(parameter: &str, referent: Ty, place: Place) -> CheckedCallTransition {
        let parameter_ty = Ty::borrow(Mutability::Mut, referent.clone());
        CheckedCallTransition {
            key: CallSiteKey {
                owner: CallOwner::Function("probe".to_string()),
                span: Span::new(0, 0),
                target: CallTarget::Function("callee".to_string()),
            },
            receiver: None,
            arguments: vec![crate::transition::CallArgumentTransition {
                parameter_index: 0,
                parameter: parameter.to_string(),
                parameter_ty,
                argument_span: Span::new(0, 0),
                effect: CallArgumentEffect::Loan(
                    crate::transition::CallTransition::unique_borrow(
                        place,
                        referent,
                        Span::new(0, 0),
                    )
                    .expect("test call-havoc shape is admitted"),
                ),
            }],
        }
    }

    #[test]
    fn sealed_ops_refuse_field_borrows_fail_closed() {
        let _ = take_vc_type_refusal();

        let operation = |place: Option<Place>| CheckedSealedOperation {
            key: EffectSiteKey {
                owner: CallOwner::Function("probe".into()),
                span: Span::new(0, 0),
            },
            target: CheckedSealedTarget::Resource(ResOp::SplitOff),
            arguments: vec![CheckedSealedArgument {
                index: 0,
                argument_ty: Ty::borrow(Mutability::Mut, Ty::Res(ResKind::RawSpan)),
                argument_span: Span::new(0, 0),
                effect: match place {
                    Some(place) => CallArgumentEffect::Loan(
                        CallTransition::unique_borrow(
                            place,
                            Ty::Res(ResKind::RawSpan),
                            Span::new(0, 0),
                        )
                        .expect("test sealed-loan shape is admitted"),
                    ),
                    None => CallArgumentEffect::Value(ValueTransfer {
                        source: None,
                        value_ty: Ty::Int(IntTy::U64),
                        kind: ValueTransferKind::Copy,
                        carried_obligation: false,
                        branded: false,
                        span: Span::new(0, 0),
                    }),
                },
            }],
            result_ty: Ty::Unit,
        };

        // A whole-place borrow answers with its root name and no refusal.
        let root = sealed_borrow_root(&operation(Some(Place::local("mem"))), 0);
        assert_eq!(root, "mem");
        assert!(take_vc_type_refusal().is_none());

        // A field borrow latches: the arm's write-back key would be the
        // whole object. The checker's `resource.field_borrow_op` refuses
        // the shape first; this is the arm's own fail-closed layer.
        let refused = sealed_borrow_root(&operation(Some(Place::field("self", "mem"))), 0);
        assert_eq!(refused, "_refused_split_off");
        let latched = take_vc_type_refusal().expect("the field borrow is latched");
        assert!(
            latched.starts_with("internal.vcgen.sealed_field_borrow:"),
            "{latched}"
        );

        // A non-borrow argument latches under its own name.
        let refused = sealed_borrow_root(&operation(None), 0);
        assert_eq!(refused, "_refused_split_off");
        let latched = take_vc_type_refusal().expect("the shape is latched");
        assert!(
            latched.starts_with("internal.vcgen.sealed_borrow_shape:"),
            "{latched}"
        );
    }

    #[test]
    fn fresh_state_refuses_shapes_with_no_story() {
        let _ = take_vc_type_refusal();
        with_generator(|generator| {
            let value = generator.fresh_state_for(&Ty::Unit, "u", "u", LenFact::Skip);
            assert!(matches!(value, Val::Unit));
            let latched = take_vc_type_refusal().expect("unit has no fresh state");
            assert!(
                latched.starts_with("internal.vcgen.fresh_state_unsupported:"),
                "{latched}"
            );

            let nested = Ty::borrow(
                Mutability::Mut,
                Ty::borrow(Mutability::Shared, Ty::Int(IntTy::U64)),
            );
            let value = generator.fresh_state_for(&nested, "b", "b", LenFact::Skip);
            assert!(matches!(value, Val::Unit));
            let latched = take_vc_type_refusal().expect("a borrow of a borrow has no state");
            assert!(
                latched.starts_with("internal.vcgen.fresh_state_unsupported:"),
                "{latched}"
            );
        });
    }

    #[test]
    fn call_site_havoc_gives_a_unique_array_borrow_a_fresh_state() {
        // The one call-site havoc covers `&mut [T]` for every caller —
        // ordinary calls, method calls, and constructor calls all go
        // through `havoc_mut_borrow_args` — so admitting a `&mut [T]`
        // member parameter later cannot silently skip the havoc. The
        // `type.member_param` corpus fences pin the gate itself.
        let _ = take_vc_type_refusal();
        with_generator(|generator| {
            generator
                .env
                .insert("xs".to_string(), Val::Arr("xs".to_string()));
            generator
                .var_tys
                .insert("xs".to_string(), Ty::array(Ty::Int(IntTy::U32)));
            let checked =
                checked_havoc_call("m", Ty::array(Ty::Int(IntTy::U32)), Place::local("xs"));
            let fresh = generator.havoc_mut_borrow_args(&checked, 1);
            assert_eq!(fresh, vec![("m".to_string(), "_arr1".to_string())]);
            assert!(matches!(
                generator.env.get("xs"),
                Some(Val::Arr(state)) if state == "_arr1"
            ));
            assert!(
                generator
                    .binders
                    .iter()
                    .any(|(b, ty)| b == "_arr1" && ty == "Sable.Seq Int")
            );
            assert!(
                generator
                    .hyps
                    .iter()
                    .any(|(h, prop)| h == "h_xs_len" && prop == "(_arr1.len) = (xs.len)")
            );
            assert!(generator.hyps.iter().any(|(h, _)| h == "h_xs_elems"));
            let certificate = generator
                .out
                .transition_certificates
                .last()
                .expect("a real array call havoc emits a certificate");
            assert_eq!(certificate.place().render(), "xs");
            assert!(matches!(
                &certificate.kind,
                crate::transition::TransitionCertificateKind::CallHavoc {
                    kind: crate::transition::CallHavocCertificateKind::Array { .. },
                    ..
                }
            ));
        });
        assert!(take_vc_type_refusal().is_none());

        // A borrowed array place with no pre-call sequence state is
        // latched too: a length relation with nothing to be relative to is
        // not a fact.
        with_generator(|generator| {
            let checked =
                checked_havoc_call("m", Ty::array(Ty::Int(IntTy::U32)), Place::local("xs"));
            let _ = generator.havoc_mut_borrow_args(&checked, 1);
        });
        let latched = take_vc_type_refusal().expect("the missing state is latched");
        assert!(
            latched.starts_with("internal.vcgen.mut_borrow_arg_state:"),
            "{latched}"
        );
    }

    #[test]
    fn call_site_havoc_writes_back_the_shared_projected_place() {
        // The checker and VCgen both decode this as `self.mem`. VCgen keeps
        // the existing conservative object update, but it may not forget the
        // projection and replace `self` with the returned resource view.
        let _ = take_vc_type_refusal();
        with_generator(|generator| {
            generator
                .env
                .insert("self".to_string(), Val::Obj("before".to_string()));
            let checked = checked_havoc_call(
                "mem",
                Ty::Res(ResKind::RawSpan),
                Place::field("self", "mem"),
            );

            let fresh = generator.havoc_mut_borrow_args(&checked, 1);
            assert_eq!(fresh.len(), 1);
            assert_eq!(fresh[0].0, "mem");
            assert!(matches!(
                generator.env.get("self"),
                Some(Val::Obj(state))
                    if state.starts_with("{ before with mem := ") && state.ends_with(" }")
            ));
            let certificate = generator
                .out
                .transition_certificates
                .last()
                .expect("a projected resource call havoc emits a certificate");
            assert_eq!(certificate.place().render(), "self.mem");
            assert!(matches!(
                &certificate.kind,
                crate::transition::TransitionCertificateKind::CallHavoc {
                    fresh,
                    observed,
                    kind: crate::transition::CallHavocCertificateKind::Writeback,
                    ..
                } if fresh == observed
            ));
        });
        assert!(take_vc_type_refusal().is_none());
    }

    #[test]
    fn call_site_havoc_performs_only_checker_supplied_effects() {
        let _ = take_vc_type_refusal();
        with_generator(|generator| {
            let checked = CheckedCallTransition {
                key: CallSiteKey {
                    owner: CallOwner::Function("probe".to_string()),
                    span: Span::new(0, 0),
                    target: CallTarget::Function("callee".to_string()),
                },
                receiver: None,
                arguments: Vec::new(),
            };
            assert!(generator.havoc_mut_borrow_args(&checked, 1).is_empty());
        });
        assert!(take_vc_type_refusal().is_none());
    }

    fn checked_call_havoc_certificate(source: &str) -> (Program, CheckResult, VcResult) {
        let (program, checked) = checked_program(source);
        let repo_root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("compiler crate has a repository parent");
        let result = generate(&program, &checked, source, repo_root)
            .expect("the checked call must produce symbolic state");
        (program, checked, result)
    }

    const CALL_HAVOC_CERT_SOURCE: &str = r#"
fn mutate(&mut [u64] values) {
}

pub fn certificate_subject(u64 n) {
    mut [u64] values = alloc_array<u64>(n, 0);
    mutate(&mut values);
}
"#;

    const OPTION_HANDOFF_SOURCE: &str = r#"
pub fn option_handoff(u64 n) {
    mut option<[bool]> pending = some(alloc_array<bool>(n, false));
    [bool] flags = pending.take;
}
"#;

    const EXPOSURE_HANDOFF_SOURCE: &str = r#"
pub fn exposure_handoff(u64 n) {
    mut [u8] bytes = alloc_array<u8>(n, 0);
    unsafe expose &mut bytes as (pointer, resource memory) {
    }
}
"#;

    const SEALED_HANDOFF_SOURCE: &str = r#"
pub fn sealed_handoff(resource &mut RawSpan memory, u64 keep) -> resource RawSpan {
    resource RawSpan tail = split_off(&mut memory, keep);
    return tail;
}
"#;

    const LOOP_HANDOFF_SOURCE: &str = r#"
pub fn loop_handoff(u64 limit) {
    mut u64 index = 0;
    /// invariant index ≤ limit
    /// variant limit - index
    while (index < limit) {
        index = index + 1;
    }
}
"#;

    const VALUE_TRANSFER_HANDOFF_SOURCE: &str = r#"
pub fn value_transfer_handoff(u64 value) -> u64 {
    u64 copy = value;
    return copy;
}
"#;

    const CLEANUP_ACTION_HANDOFF_SOURCE: &str = r#"
class CleanupChild {
    u64 value;

    init new(u64 value) {
        self.value = value;
    }
}

fn make_cleanup_child(u64 value) -> CleanupChild {
    return CleanupChild::new(value);
}

class CleanupHolder {
    CleanupChild child;
    CleanupChild spare;

    init new() {
        self.child = CleanupChild::new(0);
        self.spare = CleanupChild::new(0);
    }

    fn exercise(&mut self, bool choose) {
        var mut local = make_cleanup_child(1);
        if (choose) {
        } else {
        }
        local = make_cleanup_child(2);
        self.child = make_cleanup_child(3);
        make_cleanup_child(4);
    }
}
"#;

    #[test]
    fn cleanup_actions_and_linked_transfers_survive_symbolic_revisits() {
        let (program, checked) = checked_program(CLEANUP_ACTION_HANDOFF_SOURCE);
        let owner = CallOwner::Method {
            class: "CleanupHolder".into(),
            method: "exercise".into(),
        };
        let body = checked
            .control
            .body(&owner, Span::new(0, 0))
            .expect("the method has one retained control body")
            .plan();
        assert_eq!(body.assignments().len(), 1);
        assert_eq!(body.field_assignments().len(), 1);
        assert_eq!(body.temporary_drops().len(), 1);
        let action_keys = [
            body.assignments()
                .next()
                .expect("local replacement action")
                .transfer_key(),
            body.field_assignments()
                .next()
                .expect("field replacement action")
                .transfer_key(),
            body.temporary_drops()
                .next()
                .expect("discarded class action")
                .transfer_key(),
        ];
        for key in action_keys {
            let transfer = checked
                .ownership
                .value_transfer(key)
                .expect("every cleanup action links an exact checker transfer");
            assert_eq!(transfer.kind, ValueTransferKind::Fresh);
            assert_eq!(transfer.source, None);
            assert_eq!(transfer.value_ty, Ty::Class(0));
        }
        generate(
            &program,
            &checked,
            CLEANUP_ACTION_HANDOFF_SOURCE,
            Path::new("."),
        )
        .expect("cleanup actions after a symbolic branch may be revisited without being consumed destructively");
    }

    #[test]
    fn cleanup_action_finish_ledger_refuses_each_unvisited_action_kind() {
        let (program, checked) = checked_program(CLEANUP_ACTION_HANDOFF_SOURCE);
        let class = &program.classes[1];
        let method = &class.methods[0];
        let owner = CallOwner::Method {
            class: class.name.clone(),
            method: method.f.name.clone(),
        };
        let control = checked
            .control
            .body(&owner, method.f.span)
            .expect("the method has one retained control body");
        let fn_map: HashMap<&str, &Fn> = program
            .fns
            .iter()
            .map(|function| (function.name.as_str(), function))
            .collect();
        let class_map: HashMap<&str, &ClassDecl> = program
            .classes
            .iter()
            .map(|declaration| (declaration.name.as_str(), declaration))
            .collect();
        let mut out = empty_result();
        let mut generator = Generator {
            f: &method.f,
            fname: format!("{}::{}", class.name, method.f.name),
            call_owner: owner.clone(),
            cctx: Cctx::Method(class, method.self_kind),
            control: Some(control),
            classes: &program.classes,
            records: &program.records,
            sigs: &checked.sigs,
            ownership: &checked.ownership,
            visited_checked_calls: checked
                .ownership
                .calls
                .for_owner(&owner)
                .map(|(key, _)| key.clone())
                .collect(),
            checked_call_visits: HashMap::new(),
            checked_slot_visits: HashMap::new(),
            visited_option_takes: HashSet::new(),
            visited_slot_transitions: HashSet::new(),
            visited_slot_actions: HashSet::new(),
            visited_exposures: HashSet::new(),
            visited_sealed_operations: HashSet::new(),
            visited_loops: HashSet::new(),
            visited_value_transfers: checked
                .ownership
                .value_transfers_for_owner(&owner)
                .map(|(key, _)| key.clone())
                .collect(),
            visited_assignments: HashSet::new(),
            visited_field_assignments: HashSet::new(),
            visited_temporary_drops: HashSet::new(),
            fn_map: &fn_map,
            class_map: &class_map,
            source: CLEANUP_ACTION_HANDOFF_SOURCE,
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
            out: &mut out,
        };

        generator.finish_checked_ownership();
        let assignment = take_vc_type_refusal().expect("the local action is unvisited");
        assert!(
            assignment.starts_with("internal.vcgen.assignment_action_unvisited:"),
            "{assignment}"
        );
        generator.visited_assignments.extend(
            control
                .plan()
                .assignments()
                .map(|action| (action.scope(), action.span())),
        );

        generator.finish_checked_ownership();
        let field = take_vc_type_refusal().expect("the field action is unvisited");
        assert!(
            field.starts_with("internal.vcgen.field_assignment_action_unvisited:"),
            "{field}"
        );
        generator.visited_field_assignments.extend(
            control
                .plan()
                .field_assignments()
                .map(|action| (action.scope(), action.span())),
        );

        generator.finish_checked_ownership();
        let temporary = take_vc_type_refusal().expect("the temporary drop is unvisited");
        assert!(
            temporary.starts_with("internal.vcgen.temporary_drop_action_unvisited:"),
            "{temporary}"
        );
        generator.visited_temporary_drops.extend(
            control
                .plan()
                .temporary_drops()
                .map(|action| (action.scope(), action.span())),
        );

        generator.finish_checked_ownership();
        assert!(take_vc_type_refusal().is_none());
    }

    #[test]
    fn cleanup_action_handoff_refuses_missing_and_mismatched_transfers() {
        let owner = CallOwner::Method {
            class: "CleanupHolder".into(),
            method: "exercise".into(),
        };
        let missing = tampered_generation_error(CLEANUP_ACTION_HANDOFF_SOURCE, |checked| {
            let key = checked
                .ownership
                .value_transfers_for_owner(&owner)
                .find(|(key, _)| key.sink == ValueTransferSink::DiscardTemporary)
                .map(|(key, _)| key.clone())
                .expect("the checker records the discarded temporary transfer");
            checked
                .ownership
                .remove_value_transfer(&key)
                .expect("the adversarial test removes the exact linked transfer");
        });
        assert!(
            missing.starts_with("internal.vcgen.value_transfer_missing:"),
            "{missing}"
        );

        let local_missing = tampered_generation_error(CLEANUP_ACTION_HANDOFF_SOURCE, |checked| {
            let key = checked
                .ownership
                .value_transfers_for_owner(&owner)
                .find(|(key, _)| {
                    matches!(
                        &key.sink,
                        ValueTransferSink::Assignment(place)
                            if place == &Place::local("local")
                    )
                })
                .map(|(key, _)| key.clone())
                .expect("the checker records the local replacement transfer");
            checked
                .ownership
                .remove_value_transfer(&key)
                .expect("the adversarial test removes the local action's exact transfer");
        });
        assert!(
            local_missing.starts_with("internal.vcgen.value_transfer_missing:"),
            "{local_missing}"
        );

        let mismatch = tampered_generation_error(CLEANUP_ACTION_HANDOFF_SOURCE, |checked| {
            let key = checked
                .ownership
                .value_transfers_for_owner(&owner)
                .find(|(key, _)| matches!(key.sink, ValueTransferSink::FieldAssignment(_)))
                .map(|(key, _)| key.clone())
                .expect("the checker records the field replacement transfer");
            checked
                .ownership
                .value_transfer_mut(&key)
                .expect("the adversarial test mutates the linked transfer")
                .value_ty = Ty::Bool;
        });
        assert!(
            mismatch.starts_with("internal.vcgen.value_transfer_mismatch:"),
            "{mismatch}"
        );
    }

    #[test]
    fn cleanup_action_shape_refuses_deletion_destination_type_and_span_forgery() {
        let checked_error = |program: &Program, checked: &CheckResult| match generate(
            program,
            checked,
            CLEANUP_ACTION_HANDOFF_SOURCE,
            Path::new("."),
        ) {
            Err(error) => error,
            Ok(_) => panic!("a forged cleanup action site must fail closed"),
        };

        let (mut deleted_program, deleted_checked) = checked_program(CLEANUP_ACTION_HANDOFF_SOURCE);
        deleted_program.classes[1].methods[0].f.body.pop();
        let deleted = checked_error(&deleted_program, &deleted_checked);
        assert!(
            deleted.starts_with("internal.vcgen.control_plan_shape_mismatch:"),
            "{deleted}"
        );

        let (mut destination_program, destination_checked) =
            checked_program(CLEANUP_ACTION_HANDOFF_SOURCE);
        let Stmt::FieldAssign { field, .. } =
            &mut destination_program.classes[1].methods[0].f.body[3]
        else {
            panic!("fixture has one field replacement")
        };
        *field = "spare".into();
        let destination = checked_error(&destination_program, &destination_checked);
        assert!(
            destination.starts_with("internal.vcgen.control_plan_shape_mismatch:"),
            "{destination}"
        );

        let (mut type_program, type_checked) = checked_program(CLEANUP_ACTION_HANDOFF_SOURCE);
        let Stmt::FieldAssign { value, .. } = &mut type_program.classes[1].methods[0].f.body[3]
        else {
            panic!("fixture has one field replacement")
        };
        value.ty = Some(Ty::Class(1));
        let forged_type = checked_error(&type_program, &type_checked);
        assert!(
            forged_type.starts_with("internal.vcgen.control_plan_shape_mismatch:"),
            "{forged_type}"
        );

        let (mut span_program, span_checked) = checked_program(CLEANUP_ACTION_HANDOFF_SOURCE);
        let Stmt::FieldAssign { field_span, .. } =
            &mut span_program.classes[1].methods[0].f.body[3]
        else {
            panic!("fixture has one field replacement")
        };
        field_span.start += 1;
        let forged_span = checked_error(&span_program, &span_checked);
        assert!(
            forged_span.starts_with("internal.vcgen.control_plan_shape_mismatch:"),
            "{forged_span}"
        );
    }

    #[test]
    fn option_take_handoff_refuses_missing_mismatched_and_unvisited_records() {
        let owner = CallOwner::Function("option_handoff".into());
        let missing = tampered_generation_error(OPTION_HANDOFF_SOURCE, |checked| {
            let (key, take) = checked
                .ownership
                .option_takes_for_owner(&owner)
                .next()
                .map(|(key, take)| (key.clone(), take.clone()))
                .expect("the checker records the affine extraction");
            assert_eq!(take.source, Place::local("pending"));
            assert_eq!(take.payload, Ty::array(Ty::Bool));
            checked
                .ownership
                .remove_option_take(&key)
                .expect("the checked extraction is removable in this adversarial test");
        });
        assert!(
            missing.starts_with("internal.vcgen.option_take_missing:"),
            "{missing}"
        );

        let mismatch = tampered_generation_error(OPTION_HANDOFF_SOURCE, |checked| {
            let key = checked
                .ownership
                .option_takes_for_owner(&owner)
                .next()
                .map(|(key, _)| key.clone())
                .expect("the checker records the affine extraction");
            checked
                .ownership
                .option_take_mut(&key)
                .expect("the checked extraction remains present")
                .source = Place::local("forged");
        });
        assert!(
            mismatch.starts_with("internal.vcgen.option_take_mismatch:"),
            "{mismatch}"
        );

        let unvisited = tampered_generation_error(OPTION_HANDOFF_SOURCE, |checked| {
            checked
                .ownership
                .insert_option_take(CheckedOptionTake {
                    key: EffectSiteKey {
                        owner,
                        span: Span::new(0, 0),
                    },
                    source: Place::local("pending"),
                    source_span: Span::new(0, 0),
                    payload: Ty::array(Ty::Bool),
                })
                .expect("the forged record has a distinct identity");
        });
        assert!(
            unvisited.starts_with("internal.vcgen.option_take_unvisited:"),
            "{unvisited}"
        );
    }

    #[test]
    fn exposure_handoff_refuses_missing_mismatched_and_unvisited_records() {
        let owner = CallOwner::Function("exposure_handoff".into());
        let missing = tampered_generation_error(EXPOSURE_HANDOFF_SOURCE, |checked| {
            let (key, exposure) = checked
                .ownership
                .exposures_for_owner(&owner)
                .next()
                .map(|(key, exposure)| (key.clone(), exposure.clone()))
                .expect("the checker records the exposure");
            assert_eq!(exposure.owner_place, Place::local("bytes"));
            assert_eq!(exposure.mutability, Mutability::Mut);
            assert_eq!(exposure.pointer, "pointer");
            assert_eq!(exposure.resource, "memory");
            checked
                .ownership
                .remove_exposure(&key)
                .expect("the checked exposure is removable in this adversarial test");
        });
        assert!(
            missing.starts_with("internal.vcgen.exposure_missing:"),
            "{missing}"
        );

        let mismatch = tampered_generation_error(EXPOSURE_HANDOFF_SOURCE, |checked| {
            let key = checked
                .ownership
                .exposures_for_owner(&owner)
                .next()
                .map(|(key, _)| key.clone())
                .expect("the checker records the exposure");
            checked
                .ownership
                .exposure_mut(&key)
                .expect("the checked exposure remains present")
                .pointer = "forged".into();
        });
        assert!(
            mismatch.starts_with("internal.vcgen.exposure_mismatch:"),
            "{mismatch}"
        );

        let key_mismatch = tampered_generation_error(EXPOSURE_HANDOFF_SOURCE, |checked| {
            let key = checked
                .ownership
                .exposures_for_owner(&owner)
                .next()
                .map(|(key, _)| key.clone())
                .expect("the checker records the exposure");
            checked
                .ownership
                .exposure_mut(&key)
                .expect("the checked exposure remains present")
                .key
                .owner = CallOwner::Function("forged_owner".into());
        });
        assert!(
            key_mismatch.starts_with("internal.vcgen.exposure_mismatch:"),
            "{key_mismatch}"
        );

        let unvisited = tampered_generation_error(EXPOSURE_HANDOFF_SOURCE, |checked| {
            checked
                .ownership
                .insert_exposure(CheckedExposure {
                    key: EffectSiteKey {
                        owner,
                        span: Span::new(0, 0),
                    },
                    owner_place: Place::local("bytes"),
                    owner_span: Span::new(0, 0),
                    owner_ty: Ty::array(Ty::Int(IntTy::U8)),
                    mutability: Mutability::Mut,
                    pointer: "pointer".into(),
                    pointer_span: Span::new(0, 0),
                    resource: "memory".into(),
                    resource_span: Span::new(0, 0),
                })
                .expect("the forged record has a distinct identity");
        });
        assert!(
            unvisited.starts_with("internal.vcgen.exposure_unvisited:"),
            "{unvisited}"
        );
    }

    #[test]
    fn sealed_handoff_refuses_missing_mismatched_and_unvisited_records() {
        let owner = CallOwner::Function("sealed_handoff".into());
        let missing = tampered_generation_error(SEALED_HANDOFF_SOURCE, |checked| {
            let (key, operation) = checked
                .ownership
                .sealed_operations_for_owner(&owner)
                .next()
                .map(|(key, operation)| (key.clone(), operation.clone()))
                .expect("the checker records the sealed operation");
            assert_eq!(
                operation.target,
                CheckedSealedTarget::Resource(ResOp::SplitOff)
            );
            assert!(matches!(
                &operation.arguments[0].effect,
                CallArgumentEffect::Loan(loan)
                    if loan.place == Place::local("memory")
                        && loan.effect == CallEffect::HavocUniqueBorrow
            ));
            assert_eq!(operation.result_ty, Ty::Res(ResKind::RawSpan));
            checked
                .ownership
                .remove_sealed_operation(&key)
                .expect("the checked operation is removable in this adversarial test");
        });
        assert!(
            missing.starts_with("internal.vcgen.sealed_transition_missing:"),
            "{missing}"
        );

        let mismatch = tampered_generation_error(SEALED_HANDOFF_SOURCE, |checked| {
            let key = checked
                .ownership
                .sealed_operations_for_owner(&owner)
                .next()
                .map(|(key, _)| key.clone())
                .expect("the checker records the sealed operation");
            checked
                .ownership
                .sealed_operation_mut(&key)
                .expect("the checked operation remains present")
                .target = CheckedSealedTarget::Resource(ResOp::Join);
        });
        assert!(
            mismatch.starts_with("internal.vcgen.sealed_transition_mismatch:"),
            "{mismatch}"
        );

        let unvisited = tampered_generation_error(SEALED_HANDOFF_SOURCE, |checked| {
            checked
                .ownership
                .insert_sealed_operation(CheckedSealedOperation {
                    key: EffectSiteKey {
                        owner,
                        span: Span::new(0, 0),
                    },
                    target: CheckedSealedTarget::Resource(ResOp::SplitOff),
                    arguments: Vec::new(),
                    result_ty: Ty::Unit,
                })
                .expect("the forged record has a distinct identity");
        });
        assert!(
            unvisited.starts_with("internal.vcgen.sealed_transition_unvisited:"),
            "{unvisited}"
        );
    }

    #[test]
    fn loop_handoff_refuses_missing_mismatched_and_unvisited_records() {
        let owner = CallOwner::Function("loop_handoff".into());
        let missing = tampered_generation_error(LOOP_HANDOFF_SOURCE, |checked| {
            let (key, effects) = checked
                .ownership
                .loops_for_owner(&owner)
                .next()
                .map(|(key, effects)| (key.clone(), effects.clone()))
                .expect("the checker records the loop effect");
            assert!(effects.mutations.iter().any(|mutation| matches!(
                mutation,
                CheckedMutation::DirectWrite { place }
                    if place == &Place::local("index")
            )));
            checked
                .ownership
                .remove_loop_effects(&key)
                .expect("the checked loop is removable in this adversarial test");
        });
        assert!(
            missing.starts_with("internal.vcgen.loop_effect_missing:"),
            "{missing}"
        );

        let mismatch = tampered_generation_error(LOOP_HANDOFF_SOURCE, |checked| {
            let key = checked
                .ownership
                .loops_for_owner(&owner)
                .next()
                .map(|(key, _)| key.clone())
                .expect("the checker records the loop effect");
            checked
                .ownership
                .loop_effects_mut(&key)
                .expect("the checked loop remains present")
                .condition_span = Span::new(0, 0);
        });
        assert!(
            mismatch.starts_with("internal.vcgen.loop_effect_mismatch:"),
            "{mismatch}"
        );

        let key_mismatch = tampered_generation_error(LOOP_HANDOFF_SOURCE, |checked| {
            let key = checked
                .ownership
                .loops_for_owner(&owner)
                .next()
                .map(|(key, _)| key.clone())
                .expect("the checker records the loop effect");
            checked
                .ownership
                .loop_effects_mut(&key)
                .expect("the checked loop remains present")
                .key
                .owner = CallOwner::Function("forged_owner".into());
        });
        assert!(
            key_mismatch.starts_with("internal.vcgen.loop_effect_mismatch:"),
            "{key_mismatch}"
        );

        let unvisited = tampered_generation_error(LOOP_HANDOFF_SOURCE, |checked| {
            checked
                .ownership
                .insert_loop(CheckedLoopEffects {
                    key: EffectSiteKey {
                        owner,
                        span: Span::new(0, 0),
                    },
                    condition_span: Span::new(0, 0),
                    mutations: Vec::new(),
                })
                .expect("the forged record has a distinct identity");
        });
        assert!(
            unvisited.starts_with("internal.vcgen.loop_effect_unvisited:"),
            "{unvisited}"
        );
    }

    #[test]
    fn value_transfer_handoff_refuses_missing_mismatched_and_unvisited_records() {
        let owner = CallOwner::Function("value_transfer_handoff".into());
        let missing = tampered_generation_error(VALUE_TRANSFER_HANDOFF_SOURCE, |checked| {
            let (key, transfer) = checked
                .ownership
                .value_transfers_for_owner(&owner)
                .min_by_key(|(key, _)| (key.span.start, key.span.end))
                .map(|(key, transfer)| (key.clone(), transfer.clone()))
                .expect("the checker records the first value transfer");
            assert_eq!(transfer.source, Some(Place::local("value")));
            assert_eq!(transfer.kind, ValueTransferKind::Copy);
            assert!(!transfer.carried_obligation);
            assert!(!transfer.branded);
            checked
                .ownership
                .remove_value_transfer(&key)
                .expect("the checked transfer is removable in this adversarial test");
        });
        assert!(
            missing.starts_with("internal.vcgen.value_transfer_missing:"),
            "{missing}"
        );

        let mismatch = tampered_generation_error(VALUE_TRANSFER_HANDOFF_SOURCE, |checked| {
            let key = checked
                .ownership
                .value_transfers_for_owner(&owner)
                .min_by_key(|(key, _)| (key.span.start, key.span.end))
                .map(|(key, _)| key.clone())
                .expect("the checker records the first value transfer");
            checked
                .ownership
                .value_transfer_mut(&key)
                .expect("the checked transfer remains present")
                .value_ty = Ty::Bool;
        });
        assert!(
            mismatch.starts_with("internal.vcgen.value_transfer_mismatch:"),
            "{mismatch}"
        );

        let unvisited = tampered_generation_error(VALUE_TRANSFER_HANDOFF_SOURCE, |checked| {
            checked
                .ownership
                .insert_value_transfer(
                    owner,
                    crate::ownership::ValueTransferSink::Binding("forged".into()),
                    ValueTransfer {
                        source: None,
                        value_ty: Ty::Unit,
                        kind: ValueTransferKind::Copy,
                        carried_obligation: false,
                        branded: false,
                        span: Span::new(0, 0),
                    },
                )
                .expect("the forged record has a distinct identity");
        });
        assert!(
            unvisited.starts_with("internal.vcgen.value_transfer_unvisited:"),
            "{unvisited}"
        );
    }

    #[test]
    fn for_desugaring_uses_distinct_transfer_sinks_at_one_source_anchor() {
        let source = r#"
pub fn desugared_transfers(u64 limit) {
    for (u64 index : range(limit)) {
    }
}
"#;
        let owner = CallOwner::Function("desugared_transfers".into());
        let (program, checked) = checked_program(source);
        let mut keys: Vec<_> = checked
            .ownership
            .value_transfers_for_owner(&owner)
            .map(|(key, _)| key.clone())
            .collect();
        keys.sort_by_key(|key| (key.span.start, key.span.end, key.sink.render()));
        assert_eq!(keys.len(), 2);
        assert_eq!(keys[0].span, keys[1].span);
        assert_ne!(keys[0].sink, keys[1].sink);
        assert!(matches!(
            (&keys[0].sink, &keys[1].sink),
            (
                crate::ownership::ValueTransferSink::Assignment(place),
                crate::ownership::ValueTransferSink::Binding(binding)
            ) if place == &Place::local("index") && binding == "index"
        ));
        generate(&program, &checked, source, Path::new("."))
            .expect("both desugared transfer records have exact VC consumers");
    }

    #[test]
    fn nested_calls_visit_checker_effects_in_evaluation_order() {
        let source = r#"
fn inner(&mut [u64] left) -> u64 {
    return 0;
}

fn outer(u64 marker, &mut [u64] right) {
}

pub fn nested_subject(u64 n) {
    mut [u64] left = alloc_array<u64>(n, 0);
    mut [u64] right = alloc_array<u64>(n, 0);
    outer(inner(&mut left), &mut right);
}
"#;
        let (_, _, result) = checked_call_havoc_certificate(source);
        let places: Vec<String> = result
            .transition_certificates
            .iter()
            .map(|certificate| certificate.place().render())
            .collect();
        assert_eq!(places, vec!["left".to_string(), "right".to_string()]);
    }

    #[test]
    fn a_call_after_a_branch_reuses_checked_facts_and_emits_one_certificate_per_path() {
        let source = r#"
fn mutate(&mut [u64] values) {
}

pub fn branch_join(u64 n, bool choose) {
    mut [u64] values = alloc_array<u64>(n, 0);
    if (choose) {
    } else {
    }
    mutate(&mut values);
}
"#;
        let (_, checked, result) = checked_call_havoc_certificate(source);
        assert_eq!(
            checked
                .ownership
                .calls
                .for_owner(&CallOwner::Function("branch_join".to_string()))
                .count(),
            1,
            "the checker records one immutable fact for the one source call"
        );

        let certificates: Vec<&TransitionCertificate> = result
            .transition_certificates
            .iter()
            .filter(|certificate| certificate.place().render() == "values")
            .collect();
        assert_eq!(certificates.len(), 2);
        assert!(certificates[0].name.contains(".visit.1."));
        assert!(certificates[1].name.contains(".visit.2."));
        assert_ne!(certificates[0].thm_name, certificates[1].thm_name);

        let emitted = crate::lean::emit(
            &result,
            &[],
            &HashSet::new(),
            &[],
            &crate::lean::EmittedNames::default(),
        )
        .finish("SableGeneratedVcgenTest");
        assert_eq!(result.argument_schedule_certificates.len(), 1);
        assert_eq!(emitted.names.certificates.len(), 3);
        assert!(
            certificates
                .iter()
                .all(|certificate| emitted.lean_source.contains(&certificate.thm_name))
        );
    }

    #[test]
    fn checker_handoff_preserves_a_destructor_field_place() {
        let source = r#"
fn touch(resource &mut RawSpan mem) {
}

pub class Holder {
    resource RawSpan mem;

    init hold(resource RawSpan initial) {
        self.mem = initial;
    }

    deinit {
        touch(&mut self.mem);
    }
}
"#;
        let (_, _, result) = checked_call_havoc_certificate(source);
        let certificate = result
            .transition_certificates
            .iter()
            .find(|certificate| certificate.place().render() == "self.mem")
            .expect("the checker-authored field place reaches the certificate");
        assert!(matches!(
            &certificate.kind,
            crate::transition::TransitionCertificateKind::CallHavoc {
                kind: crate::transition::CallHavocCertificateKind::Writeback,
                ..
            }
        ));
    }

    #[test]
    fn retained_template_deinit_visits_checked_calls_and_emits_obligations() {
        let source = r#"
fn touch(resource &mut RawSpan mem) {
}

pub class GenericHolder<T> {
    T value;
    resource RawSpan mem;

    init hold(T initial, resource RawSpan memory) {
        self.value = initial;
        self.mem = memory;
    }

    deinit {
        touch(&mut self.mem);
        /// assert #[label(nonnegative)] self.mem.len >= 0
    }
}
"#;
        let (program, checked) = checked_program(source);
        assert_eq!(
            checked
                .ownership
                .calls
                .for_owner(&CallOwner::Deinitializer {
                    class: "GenericHolder".to_string(),
                })
                .count(),
            1,
            "the checker records the retained template destructor call"
        );

        let repo_root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("compiler crate has a repository parent");
        let result = generate(&program, &checked, source, repo_root)
            .expect("the retained template destructor must be symbolically generated");

        assert!(
            result
                .obligations
                .iter()
                .any(|obligation| obligation.name == "GenericHolder::deinit.assert.nonnegative")
        );
        let certificate = result
            .transition_certificates
            .iter()
            .find(|certificate| {
                certificate.name.contains("deinitializer.GenericHolder")
                    && certificate.place().render() == "self.mem"
            })
            .expect("the template destructor visits its checker-authored field havoc");
        assert!(matches!(
            &certificate.kind,
            crate::transition::TransitionCertificateKind::CallHavoc {
                kind: crate::transition::CallHavocCertificateKind::Writeback,
                ..
            }
        ));
    }

    #[test]
    fn constructor_and_method_calls_visit_checker_unique_borrow_effects() {
        let source = r#"
class Cell {
    u64 value;

    init zero() {
        self.value = 0;
    }

    fn bump(&mut self) {
        self.value = self.value + 1;
    }
}

class Driver {
    u64 runs;

    init borrow(&mut Cell cell) {
        cell.bump();
        self.runs = 0;
    }

    fn touch(&self, &mut Cell cell) {
        cell.bump();
    }
}

pub fn member_call_subject() {
    var mut cell = Cell::zero();
    var driver = Driver::borrow(&mut cell);
    driver.touch(&mut cell);
}
"#;
        let (_, _, result) = checked_call_havoc_certificate(source);
        let places: Vec<String> = result
            .transition_certificates
            .iter()
            .map(|certificate| certificate.place().render())
            .collect();
        assert_eq!(places, vec!["cell".to_string(), "cell".to_string()]);
    }

    #[test]
    fn constructor_and_method_with_one_spelling_keep_distinct_typed_owners() {
        let source = r#"
fn noop() {
}

class Same {
    u64 value;

    init same() {
        noop();
        /// assert #[label(owner)] true
        self.value = 0;
    }

    fn same(&self) {
        noop();
        /// assert #[label(owner)] true
    }
}

pub fn same_member_subject() {
    var value = Same::same();
    value.same();
}
"#;
        let (program, checked) = checked_program(source);
        assert_eq!(
            checked
                .ownership
                .calls
                .for_owner(&CallOwner::Constructor {
                    class: "Same".to_string(),
                    init: "same".to_string(),
                })
                .count(),
            1
        );
        assert_eq!(
            checked
                .ownership
                .calls
                .for_owner(&CallOwner::Method {
                    class: "Same".to_string(),
                    method: "same".to_string(),
                })
                .count(),
            1
        );

        let repo_root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("compiler crate has a repository parent");
        let result = generate(&program, &checked, source, repo_root)
            .expect("typed member owners must partition calls and proof declarations");
        let constructor = result
            .obligations
            .iter()
            .find(|obligation| obligation.name == "Same::same::constructor.assert.owner")
            .expect("the constructor assertion has a typed identity");
        let method = result
            .obligations
            .iter()
            .find(|obligation| obligation.name == "Same::same::method.assert.owner")
            .expect("the method assertion has a typed identity");
        assert_ne!(constructor.thm_name, method.thm_name);
        assert_eq!(
            result
                .clause_wfs
                .iter()
                .map(|wf| wf.def_name.as_str())
                .collect::<HashSet<_>>()
                .len(),
            result.clause_wfs.len(),
            "typed owner components keep every generated clause helper distinct"
        );
    }

    #[test]
    fn generated_theorem_identity_is_injective_over_raw_semantic_components() {
        let projected = injective_lean_components(
            "cert",
            &["function.foo", "function.touch", "self.mem", "7:12", "0"],
        );
        let underscored = injective_lean_components(
            "cert",
            &["function.foo", "function.touch", "self_mem", "7:12", "0"],
        );
        assert_ne!(projected, underscored);

        let dependency = injective_lean_components(
            "cert",
            &[
                "function.foo",
                "function.touch_dep",
                "bar_call_havoc_baz",
                "7:12",
                "0",
            ],
        );
        let root = injective_lean_components(
            "cert",
            &[
                "function.foo_call_havoc_bar",
                "function.touch_root",
                "baz",
                "7:12",
                "0",
            ],
        );
        assert_ne!(dependency, root);
    }

    #[test]
    fn vcgen_refuses_a_missing_checked_call_record() {
        let (program, mut checked) = checked_program(CALL_HAVOC_CERT_SOURCE);
        checked.ownership.calls = crate::transition::CheckedCallTransitions::default();
        let error = match generate(&program, &checked, CALL_HAVOC_CERT_SOURCE, Path::new(".")) {
            Err(error) => error,
            Ok(_) => panic!("a unique-borrow call without its checker record must fail closed"),
        };
        assert!(
            error.starts_with("internal.vcgen.call_transition_missing:"),
            "{error}"
        );
    }

    #[test]
    fn vcgen_refuses_a_mismatched_checked_call_record() {
        let (program, mut checked) = checked_program(CALL_HAVOC_CERT_SOURCE);
        let key = checked
            .ownership
            .calls
            .for_owner(&CallOwner::Function("certificate_subject".to_string()))
            .next()
            .map(|(key, _)| key.clone())
            .expect("the subject has one checked call");
        checked
            .ownership
            .calls
            .get_mut(&key)
            .expect("the checked call remains present")
            .arguments[0]
            .parameter = "forged".into();
        let error = match generate(&program, &checked, CALL_HAVOC_CERT_SOURCE, Path::new(".")) {
            Err(error) => error,
            Ok(_) => panic!("a parameter-mismatched checker record must fail closed"),
        };
        assert!(
            error.starts_with("internal.vcgen.call_transition_mismatch:"),
            "{error}"
        );
    }

    #[test]
    fn vcgen_refuses_a_checked_call_record_for_a_different_place() {
        let (program, mut checked) = checked_program(CALL_HAVOC_CERT_SOURCE);
        let key = checked
            .ownership
            .calls
            .for_owner(&CallOwner::Function("certificate_subject".to_string()))
            .next()
            .map(|(key, _)| key.clone())
            .expect("the subject has one checked call");
        let CallArgumentEffect::Loan(loan) = &mut checked
            .ownership
            .calls
            .get_mut(&key)
            .expect("the checked call remains present")
            .arguments[0]
            .effect
        else {
            panic!("the source passes one unique borrow")
        };
        loan.place = Place::local("forged");
        let error = match generate(&program, &checked, CALL_HAVOC_CERT_SOURCE, Path::new(".")) {
            Err(error) => error,
            Ok(_) => panic!("a place-mismatched checker record must fail closed"),
        };
        assert!(
            error.starts_with("internal.vcgen.call_transition_mismatch:"),
            "{error}"
        );
    }

    #[test]
    fn vcgen_refuses_an_unvisited_checked_call_record() {
        let (program, mut checked) = checked_program(CALL_HAVOC_CERT_SOURCE);
        checked
            .ownership
            .calls
            .insert(CheckedCallTransition {
                key: CallSiteKey {
                    owner: CallOwner::Function("certificate_subject".into()),
                    span: Span::new(0, 0),
                    target: CallTarget::Function("not_in_the_ast".into()),
                },
                receiver: None,
                arguments: Vec::new(),
            })
            .expect("the forged extra key is distinct");
        let error = match generate(&program, &checked, CALL_HAVOC_CERT_SOURCE, Path::new(".")) {
            Err(error) => error,
            Ok(_) => panic!("an extra checker record must fail closed"),
        };
        assert!(
            error.starts_with("internal.vcgen.call_transition_unvisited:"),
            "{error}"
        );
    }

    #[test]
    fn real_call_havoc_emits_a_non_skippable_transition_certificate() {
        let (_, _, result) = checked_call_havoc_certificate(CALL_HAVOC_CERT_SOURCE);
        assert_eq!(result.transition_certificates.len(), 1);
        let certificate = &result.transition_certificates[0];
        assert_eq!(certificate.place().render(), "values");
        assert!(matches!(
            &certificate.kind,
            crate::transition::TransitionCertificateKind::CallHavoc {
                transition: crate::transition::CallTransition {
                    referent: Ty::Array(_),
                    ..
                },
                fresh,
                observed,
                kind: crate::transition::CallHavocCertificateKind::Array { .. },
            } if fresh == observed
        ));

        let attempted_skip = HashSet::from([certificate.name.clone()]);
        let emitted = crate::lean::emit(
            &result,
            &[],
            &attempted_skip,
            &[],
            &crate::lean::EmittedNames::default(),
        )
        .finish("SableGeneratedVcgenTest");
        assert!(emitted.lean_source.contains("Sable.ArrayCallHavoc"));
        assert!(emitted.lean_source.contains("by exact ⟨rfl,"));
        assert_eq!(result.argument_schedule_certificates.len(), 1);
        assert!(
            emitted
                .lean_source
                .contains(&result.argument_schedule_certificates[0].thm_name)
        );
        assert_eq!(emitted.names.certificates.len(), 2);
        assert!(!emitted.names.thms.contains(&certificate.thm_name));
    }

    #[test]
    fn tampered_real_call_havoc_certificate_is_rejected_by_lean() {
        let (_, _, mut result) = checked_call_havoc_certificate(CALL_HAVOC_CERT_SOURCE);
        let before = match &result.transition_certificates[0].kind {
            crate::transition::TransitionCertificateKind::CallHavoc {
                kind: crate::transition::CallHavocCertificateKind::Array { before, .. },
                ..
            } => before.clone(),
            crate::transition::TransitionCertificateKind::CallHavoc {
                kind: crate::transition::CallHavocCertificateKind::Writeback,
                ..
            } => {
                panic!("the source call lends an array")
            }
            crate::transition::TransitionCertificateKind::SlotTake { .. }
            | crate::transition::TransitionCertificateKind::SlotPut { .. } => {
                panic!("the source has no owner-slot transition")
            }
        };
        // Adversarially restore the exact stale-state bug this certificate
        // fences: the caller observes its pre-call sequence instead of the
        // fresh sequence chosen for the callee's post-state.
        let crate::transition::TransitionCertificateKind::CallHavoc { observed, .. } =
            &mut result.transition_certificates[0].kind
        else {
            panic!("the source emits one call-havoc certificate")
        };
        *observed = before;
        let emitted = crate::lean::emit(
            &result,
            &[],
            &HashSet::new(),
            &[],
            &crate::lean::EmittedNames::default(),
        )
        .finish("SableGeneratedVcgenTest");

        let repo_root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("compiler crate has a repository parent");
        let environment = crate::lean::ProofEnvironment::capture(repo_root)
            .expect("the repository proof environment must be capturable");
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("test clock follows the Unix epoch")
            .as_nanos();
        let lean_file = std::env::temp_dir().join(format!(
            "sable_tampered_transition_{}_{}.lean",
            std::process::id(),
            nonce
        ));
        std::fs::write(&lean_file, &emitted.lean_source)
            .expect("the tampered generated document must be writable");
        let messages = crate::lean::run_lean(
            repo_root,
            &environment,
            &lean_file,
            None,
            &emitted.lean_source,
        )
        .expect("Lean must run and report the rejected theorem");
        let _ = std::fs::remove_file(&lean_file);
        let modules = crate::modules::ModuleSet::single(
            "transition_certificate.sable".into(),
            CALL_HAVOC_CERT_SOURCE.into(),
        );
        let diagnostics = crate::lean::diagnose(&emitted, &result, &messages, &modules);
        assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
        assert_eq!(
            diagnostics[0].name,
            "internal.transition_certificate_rejected"
        );
        assert_eq!(
            diagnostics[0].title,
            format!(
                "Lean rejected call-havoc transition certificate `{}`",
                result.transition_certificates[0].name
            )
        );
        assert_eq!(
            diagnostics[0].label,
            "fresh symbolic state was not certified at `values`"
        );
    }

    #[test]
    fn loop_havoc_refuses_untyped_and_stale_chained_names() {
        let _ = take_vc_type_refusal();
        let effects = CheckedLoopEffects {
            key: EffectSiteKey {
                owner: CallOwner::Function("probe".into()),
                span: Span::new(0, 0),
            },
            condition_span: Span::new(0, 0),
            mutations: vec![CheckedMutation::DirectWrite {
                place: Place::local("x"),
            }],
        };

        // An assigned name with a pre-loop env entry but no declared type
        // has no fresh-state story: latch, never a stale chain.
        with_generator(|generator| {
            generator
                .env
                .insert("x".to_string(), Val::Int("0".to_string()));
            generator.havoc(&effects);
        });
        let latched = take_vc_type_refusal().expect("the untyped name is latched");
        assert!(
            latched.starts_with("internal.vcgen.havoc_untyped_name:"),
            "{latched}"
        );

        // A composite key whose chain depends on a havocked name with no
        // stale binder has no pre-loop spelling: latch, never a chain that
        // the fresh binders would recapture.
        with_generator(|generator| {
            generator
                .var_tys
                .insert("x".to_string(), Ty::Int(IntTy::U64));
            generator
                .env
                .insert("x".to_string(), Val::Int("x".to_string()));
            generator
                .env
                .insert("b.f".to_string(), Val::Int("x".to_string()));
            generator.havoc(&effects);
        });
        let latched = take_vc_type_refusal().expect("the dead chain is latched");
        assert!(
            latched.starts_with("internal.vcgen.havoc_stale_chain:"),
            "{latched}"
        );
    }

    /// A call whose return type has no fresh-state story latches a named
    /// refusal instead of aborting. No `.sable` source reaches this — the
    /// parser and the checker both refuse a returned borrow first (ADR 0085)
    /// — so the `internal.` name's corpus exemption is earned here
    /// (ADR 0064, ADR 0074).
    #[test]
    fn a_call_return_with_no_state_story_latches_a_named_refusal() {
        let _ = take_vc_type_refusal();
        let mut f = minimal_fn();
        let mut callee = minimal_fn();
        callee.name = "g".to_string();
        callee.ret = Ty::borrow(Mutability::Shared, Ty::array(Ty::Int(IntTy::U64)));
        let call = Expr {
            kind: ExprKind::Call {
                callee: "g".to_string(),
                callee_span: Span::new(0, 0),
                type_args: Vec::new(),
                args: Vec::new(),
            },
            span: Span::new(0, 0),
            ty: Some(Ty::borrow(
                Mutability::Shared,
                Ty::array(Ty::Int(IntTy::U64)),
            )),
        };
        f.body.push(Stmt::ExprStmt(call.clone()));
        let mut control_program = parsed_program("fn probe() {} fn g() {}");
        control_program.fns = vec![f.clone(), callee.clone()];
        let control_program = crate::control::ControlProgram::build(&control_program)
            .expect("the forged call still has an exact control plan");
        let control = control_program
            .body(&CallOwner::Function("probe".into()), f.span)
            .expect("the forged caller has one retained control body");
        let classes: Vec<ClassDecl> = Vec::new();
        let records: Vec<RecordDecl> = Vec::new();
        let mut sigs: HashMap<String, FnSig> = HashMap::new();
        sigs.insert(
            "g".to_string(),
            FnSig {
                params: Vec::new(),
                ret: Ty::borrow(Mutability::Shared, Ty::array(Ty::Int(IntTy::U64))),
            },
        );
        let mut fn_map: HashMap<&str, &Fn> = HashMap::new();
        fn_map.insert("g", &callee);
        let class_map: HashMap<&str, &ClassDecl> = HashMap::new();
        let mut ownership = CheckedOwnershipPlan::default();
        ownership
            .calls
            .insert(CheckedCallTransition {
                key: CallSiteKey {
                    owner: CallOwner::Function("probe".to_string()),
                    span: Span::new(0, 0),
                    target: CallTarget::Function("g".to_string()),
                },
                receiver: None,
                arguments: Vec::new(),
            })
            .expect("the synthetic call has one checked identity");
        let mut out = empty_result();
        let mut generator = Generator {
            f: &f,
            fname: "probe".to_string(),
            call_owner: CallOwner::Function("probe".to_string()),
            cctx: Cctx::None,
            control: Some(control),
            classes: &classes,
            records: &records,
            sigs: &sigs,
            ownership: &ownership,
            visited_checked_calls: HashSet::new(),
            checked_call_visits: HashMap::new(),
            checked_slot_visits: HashMap::new(),
            visited_option_takes: HashSet::new(),
            visited_slot_transitions: HashSet::new(),
            visited_slot_actions: HashSet::new(),
            visited_exposures: HashSet::new(),
            visited_sealed_operations: HashSet::new(),
            visited_loops: HashSet::new(),
            visited_value_transfers: HashSet::new(),
            visited_assignments: HashSet::new(),
            visited_field_assignments: HashSet::new(),
            visited_temporary_drops: HashSet::new(),
            fn_map: &fn_map,
            class_map: &class_map,
            source: "",
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
            out: &mut out,
        };
        generator.eval(&call, control.plan().body_scope());
        let latched = take_vc_type_refusal().expect("the return shape is latched");
        assert!(
            latched.starts_with("internal.vcgen.call_return_unsupported:"),
            "{latched}"
        );
    }

    #[test]
    fn member_call_result_uses_the_shared_fail_closed_dispatch() {
        let _ = take_vc_type_refusal();
        with_generator(|generator| {
            let value = generator.bind_call_result(
                &Ty::array(Ty::Int(IntTy::U64)),
                "result",
                CallResultSite::Member,
            );
            assert!(matches!(value, Val::Int(ref placeholder) if placeholder == "result"));
            assert!(
                generator
                    .binders
                    .iter()
                    .any(|(name, ty)| name == "result" && ty == UNSUPPORTED_LEAN_TY)
            );
        });
        let latched = take_vc_type_refusal().expect("member array result is latched");
        assert!(
            latched.starts_with("internal.vcgen.call_return_unsupported:"),
            "{latched}"
        );
    }

    #[test]
    fn trait_and_method_value_boundaries_fail_in_vc_preflight() {
        let trait_program = parsed_program(
            r#"
trait Predicate {
    fn test(Self value) -> bool;
}
"#,
        );
        let error = validate_vc_type_domain(&trait_program)
            .expect_err("trait Bool results must fail before symbolic evaluation");
        assert!(error.contains("Boolean and POD-record trait returns"));

        let method_program = parsed_program(
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
        let error = validate_vc_type_domain(&method_program)
            .expect_err("method record results must fail before symbolic evaluation");
        assert!(error.contains("POD-record method returns"));
    }

    #[test]
    fn record_loop_havoc_rebinds_the_nominal_value_and_well_formedness() {
        let source = r#"
record Pair #[layout(size := 16, align := 8)] {
    #[offset(0)] u64 left;
    #[offset(8)] u64 right;
}

fn make_pair(u64 left, u64 right) -> Pair {
    return Pair(left, right);
}

fn loop_record(u64 count) -> u64 {
    mut Pair pair = make_pair(1, 2);
    mut u64 i = count;
    /// invariant pair.left = 1
    /// invariant pair.right = 2
    /// variant i
    while (i > 0) {
        pair = make_pair(1, 2);
        i = i - 1;
    }
    return pair.left;
}
"#;
        let (program, checked) = checked_program(source);
        let generated = generate(&program, &checked, source, std::path::Path::new("."))
            .expect("record loop should stay inside the VC type domain");
        let preservation = generated
            .obligations
            .iter()
            .find(|obligation| obligation.name.starts_with("loop_record.inv_preserved"))
            .expect("loop should emit an invariant-preservation obligation");

        assert!(
            preservation
                .binders
                .iter()
                .any(|(name, ty)| name == "pair" && ty == "SableR_Pair")
        );
        assert!(
            preservation
                .hyps
                .iter()
                .any(|(_, proposition)| proposition == "SableR_Pair.wf pair")
        );
    }
}
