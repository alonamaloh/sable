//! The compiler side of the SVM differential harness: lower a checked
//! function body in the machine's core subset to a Lean `List Stmt`
//! term over `lean/Sable/SVM.lean`, and canonicalize `interp.rs`
//! outcomes into the harness's wire format — which must match
//! `Config.render` on the Lean side character for character.
//!
//! Lowering is deliberately strict: anything outside the formalized
//! subset — class members, option-valued parameters/storage, transported arrays,
//! loop invariants — is a hard error, never a silent skip, so the harness
//! cannot compare less than it claims to. The mandatory loop `variant`
//! is the one asymmetry: erased here (ghost, design §4) but monitored
//! by the interpreter, so a diff program's variants must hold.

use crate::ast;
use crate::ast::*;
use crate::interp::{MmioEvent, ObservedRun, RtArray, RtVal};
use std::collections::{HashMap, HashSet};

#[derive(Clone)]
struct LocalBinding {
    ty: Ty,
    mutable: bool,
    initialized: bool,
}

/// Program metadata needed while lowering checked, index-bearing AST nodes.
/// Keeping this context explicit ensures record tags and layouts come from
/// the same checked program whose function body we lower.
#[derive(Clone)]
struct LowerCtx<'a> {
    program: &'a Program,
    locals: HashMap<String, LocalBinding>,
    declared: HashSet<String>,
    return_ty: Option<Ty>,
}

impl<'a> LowerCtx<'a> {
    /// A context for focused expression tests that do not mention a local
    /// place. Public function lowering always uses `for_function` instead.
    #[cfg(test)]
    fn bare(program: &'a Program) -> LowerCtx<'a> {
        LowerCtx {
            program,
            locals: HashMap::new(),
            declared: HashSet::new(),
            return_ty: None,
        }
    }

    /// Begin with parameters only. Locals enter `locals` as their declaration
    /// is crossed, so named array operations cannot resolve a future or
    /// out-of-scope declaration from a forged checked AST.
    fn for_function(program: &'a Program, function: &Fn) -> Result<LowerCtx<'a>, String> {
        let mut ctx = LowerCtx {
            program,
            locals: HashMap::new(),
            declared: HashSet::new(),
            return_ty: Some(function.ret.clone()),
        };
        for parameter in &function.params {
            ctx.insert_local(&parameter.name, parameter.ty.clone(), false, true)?;
        }
        Ok(ctx)
    }

    fn insert_local(
        &mut self,
        name: &str,
        ty: Ty,
        mutable: bool,
        initialized: bool,
    ) -> Result<(), String> {
        if !self.declared.insert(name.to_string()) {
            return Err(format!(
                "svm.local_type: duplicate checked local `{name}`; local types are ambiguous"
            ));
        }
        self.locals.insert(
            name.to_string(),
            LocalBinding {
                ty,
                mutable,
                initialized,
            },
        );
        Ok(())
    }

    fn initialized_local(&self, name: &str, operation: &str) -> Result<LocalBinding, String> {
        let Some(binding) = self.local(name) else {
            return Err(format!(
                "svm.local_type: {operation} names unknown or out-of-scope local `{name}`"
            ));
        };
        if !binding.initialized {
            return Err(format!(
                "svm.local_type: {operation} reads uninitialized local `{name}`"
            ));
        }
        Ok(binding)
    }

    fn record(&self, index: usize) -> Result<&'a RecordDecl, String> {
        self.program.records.get(index).ok_or_else(|| {
            format!("record index {index} is outside the checked program (lowering bug?)")
        })
    }

    fn local(&self, name: &str) -> Option<LocalBinding> {
        self.locals.get(name).cloned()
    }
}

/// Keep the aggregate representation boundary explicit. Arrays admit concrete
/// integers and, in the narrowly checked owned-local position, `bool`;
/// ordinary options admit both as well. The Lean constructors are intentionally
/// untyped, so every checked payload must be classified here instead of
/// inheriting lowering by accident.
fn validate_fn_payloads(ctx: &mut LowerCtx<'_>, f: &Fn) -> Result<(), String> {
    if !f.type_params.is_empty() {
        return Err(format!(
            "svm.type_parameter_unsupported: `{}` is still a generic declaration",
            f.name
        ));
    }
    for param in &f.params {
        validate_parameter_ty(&param.ty, &format!("parameter `{}`", param.name))?;
    }
    if f.ret.is_affine_option() {
        return Err(affine_option_unsupported(
            f.ret.clone(),
            &format!("return type of `{}`", f.name),
        ));
    }
    validate_ty_payload(f.ret.clone(), &format!("return type of `{}`", f.name))?;
    if f.ret.is_bool_array() {
        return Err(format!(
            "svm.bool_array_position_unsupported: `{}` returns a Boolean array; Boolean arrays are owned locals only",
            f.name
        ));
    }
    if f.ret.clone().is_resource() {
        return Err(format!(
            "svm.resource_return_unsupported: `{}` returns erased authority, which has no SVM value representation",
            f.name
        ));
    }
    if f.extern_info.is_some() {
        return Err(format!(
            "`{}` is an audited extern: the machine has no semantics for a foreign call",
            f.name
        ));
    }
    validate_stmt_payloads(ctx, &f.body)?;
    if f.ret != Ty::Unit && !block_definitely_returns(&f.body) {
        return Err(format!(
            "svm.missing_return: non-unit function `{}` can fall through without an SVM value",
            f.name
        ));
    }
    Ok(())
}

/// Check every container payload inside a type the machine will lower.
///
/// A traversal: exhaustive with no wildcard, so a new `Ty` constructor is a
/// compile error here rather than a shape that reaches the machine without
/// any gate seeing it (ADR 0064). Its leaves are the payload gates below,
/// which are allow-lists and never recurse.
pub(crate) fn validate_ty_payload(ty: Ty, context: &str) -> Result<(), String> {
    // An option whose present case owns is refused here rather than by the
    // copyable-option payload gate below, which would name the wrong rule
    // for a shape its lowering never handles.
    if ty.is_affine_option() {
        return Err(affine_option_unsupported(ty, context));
    }
    // A borrow carries no payload of its own, so what is gated is the
    // referent's: `&[[u64]]` meets the array payload rule exactly as
    // `[[u64]]` does.
    validate_container_payloads(ty.referent().clone(), context)
}

/// The payload rules for one type's own containers, exhaustive with no
/// wildcard so a new `Ty` constructor is a compile error here rather than a
/// shape that reaches the machine without any gate seeing it.
fn validate_container_payloads(ty: Ty, context: &str) -> Result<(), String> {
    match ty {
        Ty::Array(payload) => validate_array_payload(&payload, context),
        Ty::Option(payload) => validate_option_payload(&payload, context),
        Ty::Param(_) | Ty::Int(IntTy::TParam(_)) | Ty::Raw(IntTy::TParam(_)) => Err(format!(
            "svm.type_parameter_unsupported: {context} contains an unresolved type parameter"
        )),
        Ty::Int(_)
        | Ty::Bool
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

/// May a parameter carry this type into the formal machine.
///
/// A position gate on top of the payload traversal: what a type may contain
/// and what a call boundary may transport are separate questions, and the
/// machine answers them separately for the same type.
pub(crate) fn validate_parameter_ty(ty: &Ty, context: &str) -> Result<(), String> {
    validate_ty_payload(ty.clone(), context)?;
    // The owner is what a call boundary may not carry: an array reaches a
    // callee as `&[T]` or `&mut [T]`, which the machine transports as an
    // argument value and, for a unique borrow, a loan returned at the pop.
    if ty.is_owned_bool_array() {
        return Err(format!(
            "svm.bool_array_position_unsupported: {context} owns a Boolean array; an array crosses a call boundary as a borrow"
        ));
    }
    Ok(())
}

fn affine_option_unsupported(ty: Ty, context: &str) -> String {
    debug_assert!(ty.is_affine_option());
    format!(
        "svm.affine_option_unsupported: {context} has type `{}`; the formal SVM admits only explicit mutable local `option<[bool]>` construction, named `.is_some`, and atomic `.take` into a fresh owned Boolean-array local",
        ty.name()
    )
}

fn affine_option_take_position(option: &str) -> String {
    format!(
        "svm.affine_option_take_position: `.take` of affine option local `{option}` must directly initialize an explicit owned Boolean-array local"
    )
}

fn affine_bool_option_ty() -> Ty {
    Ty::affine_array_option(Ty::Bool)
}

fn is_affine_bool_option(ty: &Ty) -> bool {
    *ty == affine_bool_option_ty()
}

fn reject_named_affine_option(ctx: &LowerCtx<'_>, name: &str, context: &str) -> Result<(), String> {
    if let Some(binding) = ctx.local(name) {
        if binding.ty.is_affine_option() {
            return Err(affine_option_unsupported(binding.ty, context));
        }
    }
    Ok(())
}

/// May the formal machine lower an array with this payload.
///
/// A gate: an allow-list ending in a named refusal, which never recurses. The
/// allow-list is the Rust mirror of `Val.tag?` in `lean/Sable/SVM.lean` — the
/// machine's element tag is `int | bool`, and this is where that fact is
/// enforced on the way in.
///
/// It answers yes or a named error and nothing else, so there is exactly one
/// entry point: an array holds a full `Ty`, and the type of one element is the
/// payload its holder already has.
pub(crate) fn validate_array_payload(payload: &Ty, context: &str) -> Result<(), String> {
    match payload.payload_family() {
        // A record element is a machine value with a declaration tag:
        // `ValTag.record` is its admission, and a cross-record store is
        // tag confusion before it is anything else.
        PayloadFamily::Value | PayloadFamily::Record => Ok(()),
        // The SVM lowers only the monomorphized program, so a type
        // parameter answers alongside the unsupported families; option
        // elements answer with them, because arrays of options stay
        // closed.
        PayloadFamily::OptionOfValue
        | PayloadFamily::Param
        | PayloadFamily::Noncanonical
        | PayloadFamily::Unsupported => Err(format!(
            "svm.aggregate_payload_unsupported: {context} has array payload `{}`; \
                 the SVM currently lowers only concrete integer and Boolean payloads",
            payload.name()
        )),
    }
}

fn require_expr_annotation(
    expr: &Expr,
    expected: Ty,
    diagnostic: &str,
    context: &str,
) -> Result<(), String> {
    match &expr.ty {
        Some(actual) if *actual == expected => Ok(()),
        Some(actual) => Err(format!(
            "{diagnostic}: {context} is annotated `{}`; expected `{}`",
            actual.name(),
            expected.name()
        )),
        None => Err(format!(
            "{diagnostic}: {context} carries no checked type; expected `{}`",
            expected.name()
        )),
    }
}

/// The element type, binding mode, and declared mutability of an array place.
///
/// The binding mode is *derived* from the type rather than read out of a
/// field: an array owns unless a borrow names it, and this is the one place
/// the machine turns that shape question into the three-way answer its
/// writability rules need.
fn resolve_array(
    ctx: &LowerCtx<'_>,
    array: &str,
    operation: &str,
) -> Result<(Ty, BindingMode, bool), String> {
    let binding = ctx.initialized_local(array, operation)?;
    if binding.ty.is_affine_option() {
        return Err(affine_option_unsupported(
            binding.ty,
            &format!("{operation} source `{array}`"),
        ));
    }
    let Some((payload, mode)) = binding.ty.as_array() else {
        return Err(format!(
            "svm.array_place_type: {operation} names `{array}` of type `{}`; expected an array",
            binding.ty.name()
        ));
    };
    let payload = payload.clone();
    validate_array_payload(&payload, &format!("{operation} of `{array}`"))?;
    Ok((payload, mode, binding.mutable))
}

fn validate_array_index(
    ctx: &LowerCtx<'_>,
    expr: &Expr,
    array: &str,
    index: &Expr,
) -> Result<(), String> {
    let (payload, _, _) = resolve_array(ctx, array, "array index")?;
    require_expr_annotation(
        expr,
        payload,
        "svm.array_index_result_type",
        "array index result",
    )?;
    validate_sink_type(ctx, Ty::Int(IntTy::U64), index, "array index operand")?;
    validate_expr_payloads(ctx, index)
}

fn validate_array_len(ctx: &LowerCtx<'_>, expr: &Expr, array: &str) -> Result<(), String> {
    resolve_array(ctx, array, "array length")?;
    require_expr_annotation(
        expr,
        Ty::Int(IntTy::U64),
        "svm.array_len_result_type",
        "array length result",
    )
}

fn validate_alloc_array(
    ctx: &LowerCtx<'_>,
    expr: &Expr,
    elem: Ty,
    len: &Expr,
    init: &Expr,
) -> Result<(), String> {
    validate_array_payload(&elem, "alloc_array")?;
    require_expr_annotation(
        expr,
        Ty::Array(Box::new(elem.clone())),
        "svm.array_alloc_result_type",
        "alloc_array result",
    )?;
    validate_sink_type(ctx, Ty::Int(IntTy::U64), len, "alloc_array length")?;
    validate_sink_type(ctx, elem, init, "alloc_array initializer")?;
    validate_expr_payloads(ctx, len)?;
    validate_expr_payloads(ctx, init)
}

fn validate_array_literal_len(payload: Ty, len: usize) -> Result<(), String> {
    if payload == Ty::Bool && len > 50_000_000 {
        return Err(format!(
            "svm.array_literal_capacity: Boolean array literal has {len} elements; \
             literal expansion is supported only through the SVM allocation cap of 50000000"
        ));
    }
    Ok(())
}

fn validate_array_literal(
    ctx: &LowerCtx<'_>,
    expr: &Expr,
    elements: &[Expr],
) -> Result<(), String> {
    let payload = match &expr.ty {
        Some(Ty::Array(payload)) => payload,
        Some(actual) => {
            return Err(format!(
                "svm.array_literal_result_type: array literal is annotated `{}`; expected a supported owned array",
                actual.name()
            ));
        }
        None => {
            return Err(
                "svm.array_literal_result_type: array literal carries no checked type; expected a supported owned array"
                    .into(),
            );
        }
    };
    validate_array_payload(payload, "array literal")?;
    validate_array_literal_len(*payload.clone(), elements.len())?;
    for (index, value) in elements.iter().enumerate() {
        validate_sink_type(
            ctx,
            (**payload).clone(),
            value,
            &format!("array literal element {}", index + 1),
        )?;
        validate_expr_payloads(ctx, value)?;
    }
    Ok(())
}

fn validate_affine_bool_option_initializer(
    ctx: &LowerCtx<'_>,
    initializer: &Expr,
    local: &str,
) -> Result<(), String> {
    require_expr_annotation(
        initializer,
        affine_bool_option_ty(),
        "svm.affine_option_initializer_type",
        &format!("initializer of affine option `{local}`"),
    )?;
    match &initializer.kind {
        ExprKind::NoneE => Ok(()),
        ExprKind::SomeE(payload) => {
            let ExprKind::AllocArray { elem, len, init } = &payload.kind else {
                return Err(format!(
                    "svm.affine_option_initializer: affine option local `{local}` must be initialized by `none` or `some(alloc_array<bool>(...))`"
                ));
            };
            if *elem != Ty::Bool {
                return Err(format!(
                    "svm.affine_option_payload: affine option local `{local}` wraps `{}`; only a freshly allocated Boolean array is supported",
                    elem.name()
                ));
            }
            validate_alloc_array(ctx, payload, elem.clone(), len, init)?;
            require_expr_annotation(
                payload,
                Ty::array(Ty::Bool),
                "svm.affine_option_payload_type",
                &format!("payload of affine option `{local}`"),
            )
        }
        _ => Err(format!(
            "svm.affine_option_initializer: affine option local `{local}` must be initialized by `none` or `some(alloc_array<bool>(...))`"
        )),
    }
}

fn validate_affine_bool_option_decl(
    ctx: &LowerCtx<'_>,
    local: &str,
    ty: Ty,
    mutable: bool,
    initializer: Option<&Expr>,
) -> Result<(), String> {
    if !is_affine_bool_option(&ty.clone()) {
        return Err(affine_option_unsupported(
            ty,
            &format!("declaration `{local}`"),
        ));
    }
    if !mutable {
        return Err(format!(
            "svm.affine_option_immutable: affine option local `{local}` must be mutable"
        ));
    }
    let Some(initializer) = initializer else {
        return Err(format!(
            "svm.affine_option_initializer: affine option local `{local}` must be initialized by `none` or `some(alloc_array<bool>(...))`"
        ));
    };
    validate_affine_bool_option_initializer(ctx, initializer, local)
}

fn validate_affine_option_take(
    ctx: &LowerCtx<'_>,
    destination: &str,
    initializer: &Expr,
    option: &str,
) -> Result<(), String> {
    require_expr_annotation(
        initializer,
        Ty::array(Ty::Bool),
        "svm.affine_option_take_result",
        &format!("`.take` initializer of `{destination}`"),
    )?;
    if destination == option {
        return Err(format!(
            "svm.affine_option_take_alias: `.take` destination `{destination}` cannot also be its source"
        ));
    }
    if ctx.local(destination).is_some() || ctx.declared.contains(destination) {
        return Err(format!(
            "svm.local_type: duplicate checked local `{destination}`; local types are ambiguous"
        ));
    }
    let source = ctx.initialized_local(option, "affine-option take")?;
    if !is_affine_bool_option(&source.ty) {
        return if source.ty.is_affine_option() {
            Err(affine_option_unsupported(
                source.ty,
                &format!("`.take` source `{option}`"),
            ))
        } else {
            Err(format!(
                "svm.affine_option_take_source: `.take` source `{option}` has type `{}`; expected `option<[bool]>`",
                source.ty.name()
            ))
        };
    }
    if !source.mutable {
        return Err(format!(
            "svm.affine_option_immutable: `.take` source `{option}` must be mutable"
        ));
    }
    Ok(())
}

/// Boolean arrays have no call ABI or general first-class transport.
/// Their sole producer position is the initializer of a fresh owned local.
/// Keep that positional rule separate from payload classification: the latter
/// describes the machine representation, while this function describes the
/// intentionally smaller source-to-machine bridge.
fn validate_fresh_bool_array_initializer(
    ctx: &LowerCtx<'_>,
    declared_ty: Ty,
    initializer: &Expr,
    local: &str,
) -> Result<(), String> {
    if !declared_ty.is_owned_bool_array() {
        return Err(format!(
            "svm.bool_array_position_unsupported: local `{local}` has type `{}`; \
             Boolean arrays must be fresh owned locals",
            declared_ty.name()
        ));
    }
    match &initializer.kind {
        ExprKind::AllocArray {
            elem,
            len,
            init: value,
        } => {
            validate_alloc_array(ctx, initializer, elem.clone(), len, value)?;
        }
        ExprKind::ArrayLit(elements) => validate_array_literal(ctx, initializer, elements)?,
        ExprKind::OptTake { option, .. } => {
            return validate_affine_option_take(ctx, local, initializer, option);
        }
        _ => {
            return Err(format!(
                "svm.bool_array_transport_unsupported: initializer of `{local}` is not a fresh Boolean array literal or allocation"
            ));
        }
    }
    validate_sink_type(
        ctx,
        declared_ty,
        initializer,
        &format!("initializer of `{local}`"),
    )
}

fn validate_array_store(
    ctx: &LowerCtx<'_>,
    array: &str,
    index: &Expr,
    value: &Expr,
) -> Result<(), String> {
    let (payload, mutability, declared_mutable) = resolve_array(ctx, array, "array store")?;
    if mutability == BindingMode::Shared || (mutability == BindingMode::Owned && !declared_mutable)
    {
        return Err(format!(
            "svm.array_store_place: array store targets non-writable `{array}` of type `{}`",
            mutability.bind(Ty::array(payload)).name()
        ));
    }
    validate_sink_type(ctx, Ty::Int(IntTy::U64), index, "array store index")?;
    validate_sink_type(ctx, payload, value, "array store value")?;
    validate_expr_payloads(ctx, index)?;
    validate_expr_payloads(ctx, value)
}

fn call_return_ty(ctx: &LowerCtx<'_>, callee: &str) -> Result<Ty, String> {
    let mut matches = ctx
        .program
        .fns
        .iter()
        .filter(|function| function.name == callee);
    let Some(function) = matches.next() else {
        return Err(format!(
            "svm.call_target: call target `{callee}` is absent from the executable program"
        ));
    };
    if matches.next().is_some() {
        return Err(format!(
            "svm.call_target: call target `{callee}` is ambiguous in the executable program"
        ));
    }
    Ok(function.ret.clone())
}

/// Recover the type supplied by the expression's checked shape instead of
/// trusting its cached annotation as a second, forgeable source of truth.
fn semantic_expr_ty(
    ctx: &LowerCtx<'_>,
    expr: &Expr,
    expected: Ty,
    context: &str,
) -> Result<Ty, String> {
    if let Some(ty) = expr.ty.as_ref().filter(|ty| ty.is_affine_option()) {
        return Err(affine_option_unsupported(ty.clone(), context));
    }
    let semantic = match &expr.kind {
        ExprKind::Var(name) => {
            let ty = ctx.initialized_local(name, context)?.ty;
            if ty.is_owned_bool_array() {
                return Err(format!(
                    "svm.bool_array_transport_unsupported: {context} moves Boolean array local `{name}`; an owner is accessed by index or length and lent by borrow"
                ));
            }
            ty
        }
        // A borrow is a second name for storage its source keeps, so its type
        // is the source's array under the requested mode. What the machine
        // does with it is a call-boundary question, answered in `lower_call`.
        ExprKind::Borrow {
            array,
            field: None,
            mutable,
        } if expr
            .ty
            .as_ref()
            .is_some_and(|ty| ty.as_array_borrow().is_some()) =>
        {
            let (payload, mode, declared_mutable) = resolve_array(ctx, array, "array borrow")?;
            if *mutable
                && (mode == BindingMode::Shared
                    || (mode == BindingMode::Owned && !declared_mutable))
            {
                return Err(format!(
                    "svm.array_borrow_place: `&mut {array}` borrows non-writable `{}`",
                    mode.bind(Ty::array(payload)).name()
                ));
            }
            let requested = if *mutable {
                Mutability::Mut
            } else {
                Mutability::Shared
            };
            Ty::borrow(requested, Ty::array(payload))
        }
        ExprKind::AllocArray { elem, .. } => Ty::Array(Box::new(elem.clone())),
        ExprKind::ArrayLit(_) => match &expr.ty {
            Some(ty @ Ty::Array(_)) => ty,
            Some(actual) => {
                return Err(format!(
                    "svm.sink_type: {context} is an array literal annotated `{}`",
                    actual.name()
                ));
            }
            None => {
                return Err(format!(
                    "svm.sink_type: {context} is an array literal without a checked type"
                ));
            }
        }
        .clone(),
        ExprKind::Call { callee, .. } => call_return_ty(ctx, callee)?,
        ExprKind::ResOp { op, args, .. } => semantic_res_op_ty(ctx, *op, args, expected)?,
        ExprKind::RawOp { op, args, .. } => validate_raw_op(ctx, *op, args)?,
        ExprKind::DeviceOp { op, args, .. } => validate_device_op(ctx, *op, args)?,
        ExprKind::IntLit(value) => match &expr.ty {
            Some(actual @ Ty::Int(integer)) if !matches!(integer, IntTy::TParam(_)) => {
                if *value < integer.min() || *value > integer.max() {
                    return Err(format!(
                        "svm.sink_type: {context} has literal `{value}` outside `{}` range {}..={}",
                        integer.name(),
                        integer.min(),
                        integer.max()
                    ));
                }
                actual
            }
            _ => {
                return Err(format!(
                    "svm.sink_type: {context} has an integer literal with a non-integer annotation"
                ));
            }
        }
        .clone(),
        ExprKind::BoolLit(_) => Ty::Bool,
        ExprKind::OptTake { option, .. } => {
            return Err(affine_option_take_position(option));
        }
        ExprKind::Unary { op, operand } => match op {
            UnOp::Not => {
                validate_sink_type(ctx, Ty::Bool, operand, &format!("{context} operand"))?;
                Ty::Bool
            }
            UnOp::Neg => {
                let operand_ty = semantic_expr_ty(
                    ctx,
                    operand,
                    operand.ty.clone().unwrap_or(expected),
                    &format!("{context} operand"),
                )?;
                match operand_ty {
                    Ty::Int(integer) if integer.signed() => operand_ty,
                    Ty::Int(_) => {
                        return Err(format!(
                            "svm.sink_type: {context} negates an unsigned integer"
                        ));
                    }
                    actual => {
                        return Err(format!(
                            "svm.sink_type: {context} negates non-integer `{}`",
                            actual.name()
                        ));
                    }
                }
            }
        },
        ExprKind::Binary { op, lhs, rhs, .. } => {
            if matches!(op, BinOp::And | BinOp::Or) {
                validate_sink_type(ctx, Ty::Bool, lhs, &format!("{context} left operand"))?;
                validate_sink_type(ctx, Ty::Bool, rhs, &format!("{context} right operand"))?;
                Ty::Bool
            } else {
                let left = semantic_expr_ty(
                    ctx,
                    lhs,
                    lhs.ty.clone().unwrap_or(expected),
                    &format!("{context} left operand"),
                )?;
                let right = semantic_expr_ty(
                    ctx,
                    rhs,
                    rhs.ty.clone().unwrap_or(left.clone()),
                    &format!("{context} right operand"),
                )?;
                if left != right || !matches!(left, Ty::Int(_)) {
                    return Err(format!(
                        "svm.sink_type: {context} has incompatible operands `{}` and `{}`",
                        left.name(),
                        right.name()
                    ));
                }
                if op.is_comparison() { Ty::Bool } else { left }
            }
        }
        ExprKind::Widen { target, arg } | ExprKind::Narrow { target, arg } => {
            if matches!(target, IntTy::TParam(_)) {
                return Err(format!(
                    "svm.type_parameter_unsupported: {context} conversion target is unresolved"
                ));
            }
            let source = semantic_expr_ty(
                ctx,
                arg,
                arg.ty.clone().unwrap_or(Ty::Int(*target)),
                &format!("{context} conversion operand"),
            )?;
            let Ty::Int(source_integer) = source else {
                return Err(format!(
                    "svm.sink_type: {context} converts non-integer `{}`",
                    source.name()
                ));
            };
            if matches!(&expr.kind, ExprKind::Widen { .. })
                && (source_integer.min() < target.min() || source_integer.max() > target.max())
            {
                return Err(format!(
                    "svm.sink_type: {context} uses non-value-preserving widen from `{}` to `{}`",
                    source_integer.name(),
                    target.name()
                ));
            }
            Ty::Int(*target)
        }
        ExprKind::Index { array, index, .. } => {
            validate_array_index(ctx, expr, array, index)?;
            let (payload, _, _) = resolve_array(ctx, array, "array index")?;
            payload
        }
        ExprKind::Len { array } => {
            resolve_array(ctx, array, "array length")?;
            Ty::Int(IntTy::U64)
        }
        ExprKind::RecordField { obj, field, .. } => {
            semantic_record_field_ty(ctx, expr, obj, field)?
        }
        ExprKind::SomeE(inner) => {
            let repr = svm_option_repr(expr, "some")?;
            let payload = match repr {
                SvmOptionRepr::Ordinary(payload) => payload,
                SvmOptionRepr::RawRecord(record) => Ty::RawRecord(record),
                SvmOptionRepr::AffineBoolArray => {
                    unreachable!(
                        "general option constructor classification excludes affine options"
                    )
                }
            };
            validate_sink_type(ctx, payload, inner, &format!("{context} option payload"))?;
            expr.ty.clone().expect("classified option result")
        }
        ExprKind::NoneE => {
            svm_option_repr(expr, "none")?;
            expr.ty.clone().expect("classified option result")
        }
        ExprKind::IsSome { operand } => {
            validate_option_accessor(ctx, expr, operand, false)?;
            Ty::Bool
        }
        ExprKind::OptValue { operand } => {
            match validate_option_accessor(ctx, expr, operand, true)? {
                SvmOptionRepr::Ordinary(payload) => payload,
                SvmOptionRepr::RawRecord(record) => Ty::RawRecord(record),
                SvmOptionRepr::AffineBoolArray => {
                    unreachable!("affine options have no copying `.value` accessor")
                }
            }
        }
        _ => {
            if expr.ty.as_ref().is_some_and(|ty| ty.as_array().is_some()) {
                return Err(format!(
                    "svm.sink_type: {context} has an expression shape that cannot produce an array"
                ));
            }
            match &expr.ty {
                Some(actual) => actual.clone(),
                None if expected.is_resource()
                    && matches!(
                        expr.kind,
                        ExprKind::SelfField { .. } | ExprKind::Borrow { .. }
                    ) =>
                {
                    expected.clone()
                }
                None => {
                    return Err(format!(
                        "svm.sink_type: {context} carries no checked result type"
                    ));
                }
            }
        }
    };
    if let Some(annotation) = &expr.ty {
        if *annotation != semantic {
            return Err(format!(
                "svm.sink_type: {context} is semantically `{}` but annotated `{}`",
                semantic.name(),
                annotation.name()
            ));
        }
    } else if !semantic.is_resource() {
        return Err(format!(
            "svm.sink_type: {context} carries no checked type; expected `{}`",
            semantic.name()
        ));
    }
    Ok(semantic)
}

fn validate_local_var(
    ctx: &LowerCtx<'_>,
    expr: &Expr,
    name: &str,
    operation: &str,
) -> Result<LocalBinding, String> {
    let binding = ctx.initialized_local(name, operation)?;
    if binding.ty.is_owned_bool_array() {
        return Err(format!(
            "svm.bool_array_transport_unsupported: {operation} moves Boolean array local `{name}`; an owner is accessed by index or length and lent by borrow"
        ));
    }
    match &expr.ty {
        Some(annotation) if *annotation != binding.ty => Err(format!(
            "svm.local_type: {operation} names `{name}` of type `{}` but is annotated `{}`",
            binding.ty.name(),
            annotation.name()
        )),
        None if !binding.ty.clone().is_resource() => Err(format!(
            "svm.local_type: {operation} names non-resource `{name}` without a checked type"
        )),
        _ => Ok(binding),
    }
}

fn semantic_record_field_ty(
    ctx: &LowerCtx<'_>,
    expr: &Expr,
    obj: &str,
    field: &str,
) -> Result<Ty, String> {
    let binding = ctx.initialized_local(obj, "record field access")?;
    let Ty::Record(record_index) = binding.ty else {
        return Err(format!(
            "svm.record_field_place: `{obj}` has type `{}`; expected a record",
            binding.ty.name()
        ));
    };
    let record = ctx.record(record_index)?;
    let Some(declared_field) = record
        .fields
        .iter()
        .find(|candidate| candidate.name == field)
    else {
        return Err(format!(
            "svm.record_field_name: record `{}` has no field `{field}`",
            record.name
        ));
    };
    if expr.ty != Some(declared_field.ty.clone()) {
        return Err(format!(
            "svm.record_field_type: `{}.{field}` has type `{}` but is annotated `{}`",
            record.name,
            declared_field.ty.clone().name(),
            expr.ty
                .clone()
                .map_or_else(|| "<missing>".into(), |arg0: ast::Ty| Ty::name(&arg0))
        ));
    }
    Ok(declared_field.ty.clone())
}

fn validate_record_literal(
    ctx: &LowerCtx<'_>,
    expr: &Expr,
    record_name: &str,
    args: &[Expr],
) -> Result<usize, String> {
    let Some(Ty::Record(record_index)) = expr.ty else {
        return Err(format!(
            "svm.record_literal_type: `{record_name}(...)` carries no record type"
        ));
    };
    let record = ctx.record(record_index)?;
    if record.name != record_name {
        return Err(format!(
            "svm.record_literal_type: literal names `{record_name}` but tag names `{}`",
            record.name
        ));
    }
    if args.len() != record.fields.len() {
        return Err(format!(
            "svm.record_literal_arity: `{record_name}` has {} arguments for {} fields",
            args.len(),
            record.fields.len()
        ));
    }
    for (argument, field) in args.iter().zip(&record.fields) {
        validate_sink_type(
            ctx,
            field.ty.clone(),
            argument,
            &format!("record literal `{record_name}.{}`", field.name),
        )?;
    }
    Ok(record_index)
}

fn validate_sink_type(
    ctx: &LowerCtx<'_>,
    expected: Ty,
    value: &Expr,
    context: &str,
) -> Result<(), String> {
    let actual = semantic_expr_ty(ctx, value, expected.clone(), context)?;
    if actual != expected {
        return Err(format!(
            "svm.sink_type: {context} supplies `{}`; destination expects `{}`",
            actual.name(),
            expected.name()
        ));
    }
    Ok(())
}

fn validate_array_rebind(ctx: &LowerCtx<'_>, name: &str) -> Result<(), String> {
    if ctx
        .local(name)
        .is_some_and(|binding| binding.ty.as_array().is_some())
    {
        return Err(format!(
            "svm.array_rebind_unsupported: checked array `{name}` is rebound; arrays may only be mutated by element store"
        ));
    }
    Ok(())
}

fn validate_return(ctx: &LowerCtx<'_>, value: &Expr) -> Result<(), String> {
    let Some(ref expected) = ctx.return_ty else {
        return Err("svm.sink_type: return lowering has no function result type".into());
    };
    if expected.clone().is_resource() {
        return Err(
            "svm.resource_return_unsupported: erased authority has no SVM result representation"
                .into(),
        );
    }
    validate_sink_type(ctx, expected.clone(), value, "return value")
}

fn validate_array_exposure(ctx: &LowerCtx<'_>, array: &str, mutable: bool) -> Result<(), String> {
    let (payload, mutability, declared_mutable) = resolve_array(ctx, array, "array exposure")?;
    if payload != Ty::Int(IntTy::U8) {
        return Err(format!(
            "svm.array_expose_type: exposure names `{array}` of type `{}`; only byte arrays have SVM exposure semantics",
            mutability.bind(Ty::array(payload)).name()
        ));
    }
    if mutable
        && (mutability == BindingMode::Shared
            || (mutability == BindingMode::Owned && !declared_mutable))
    {
        return Err(format!(
            "svm.array_expose_type: mutable exposure targets non-writable `{array}`"
        ));
    }
    Ok(())
}

fn validate_system_dealloc(
    ctx: &LowerCtx<'_>,
    ptr: &Expr,
    res: &Expr,
    release: &Expr,
) -> Result<(), String> {
    validate_sink_type(ctx, Ty::Raw(IntTy::U8), ptr, "system deallocation pointer")?;
    for (value, expected, context) in [
        (
            res,
            Ty::Res(ResKind::RawSpan),
            "system deallocation raw authority",
        ),
        (
            release,
            Ty::Res(ResKind::SystemDealloc),
            "system deallocation release authority",
        ),
    ] {
        if !matches!(value.kind, ExprKind::Var(_)) {
            return Err(format!(
                "svm.resource_operand_place: {context} must be an active owned resource variable"
            ));
        }
        let actual = resolved_resource_place_ty(ctx, value, context)?;
        if actual != expected {
            return Err(format!(
                "svm.resource_operand_type: {context} supplies `{}`; expected `{}`",
                actual.name(),
                expected.name()
            ));
        }
    }
    Ok(())
}

fn validate_allocation_size(ctx: &LowerCtx<'_>, size: &Expr, context: &str) -> Result<(), String> {
    validate_sink_type(ctx, Ty::Int(IntTy::U64), size, context)?;
    let ExprKind::IntLit(value) = size.kind else {
        return Err(format!(
            "svm.allocation_size_literal: {context} must be a compile-time literal"
        ));
    };
    if !(1..=50_000_000).contains(&value) {
        return Err(format!(
            "svm.allocation_size_range: {context} `{value}` is outside 1..=50000000"
        ));
    }
    Ok(())
}

/// May the formal machine lower a copyable option with this payload. A gate
/// on the same terms as `validate_array_payload`.
pub(crate) fn validate_option_payload(payload: &Ty, context: &str) -> Result<(), String> {
    match payload.payload_family() {
        // `Val.opt : Option Val` is recursive in the formal machine, so a
        // nested option lowers exactly as a flat one.
        PayloadFamily::Value | PayloadFamily::OptionOfValue => Ok(()),
        PayloadFamily::Record
        | PayloadFamily::Param
        | PayloadFamily::Noncanonical
        | PayloadFamily::Unsupported => Err(format!(
            "svm.aggregate_payload_unsupported: {context} has option payload `{}`; \
                 the SVM currently lowers only concrete integer and Boolean option payloads",
            payload.name()
        )),
    }
}

#[derive(Clone)]
enum SvmOptionRepr {
    /// The payload of a copyable option, which is also the type of its present
    /// case. Every construction of this variant runs `validate_option_payload`
    /// first, so holding one is the evidence that the payload is admitted.
    Ordinary(Ty),
    RawRecord(usize),
    AffineBoolArray,
}

/// Classify an option constructor from its checked outer annotation.  The
/// Lean syntax is deliberately untyped, so accepting a missing or unrelated
/// annotation here would let a malformed public AST manufacture a value that
/// the source checker could never produce.
fn svm_option_repr(expr: &Expr, constructor: &str) -> Result<SvmOptionRepr, String> {
    match &expr.ty {
        Some(ty) if ty.is_affine_option() => Err(affine_option_unsupported(
            ty.clone(),
            &format!("`{constructor}` result"),
        )),
        Some(Ty::Option(payload)) => {
            validate_option_payload(payload, &format!("`{constructor}` result"))?;
            Ok(SvmOptionRepr::Ordinary(*payload.clone()))
        }
        Some(Ty::OptionRaw(record)) => Ok(SvmOptionRepr::RawRecord(*record)),
        Some(ty) => Err(format!(
            "svm.option_constructor_type: `{constructor}` result has type `{}`; \
             expected an ordinary or nullable-raw option annotation",
            ty.name()
        )),
        None => Err(format!(
            "svm.option_constructor_type: `{constructor}` result carries no type; \
             expected an ordinary or nullable-raw option annotation"
        )),
    }
}

fn validate_some_constructor(expr: &Expr, inner: &Expr) -> Result<SvmOptionRepr, String> {
    let repr = svm_option_repr(expr, "some")?;
    let expected = match repr {
        SvmOptionRepr::Ordinary(ref payload) => payload.clone(),
        SvmOptionRepr::RawRecord(record) => Ty::RawRecord(record),
        SvmOptionRepr::AffineBoolArray => {
            return Err(
                "svm.affine_option_unsupported: an ownership-bearing option has no general \
                 `some` constructor; it is built only as a fresh owned allocation"
                    .into(),
            );
        }
    };
    match &inner.ty {
        Some(actual) if *actual == expected => Ok(repr),
        Some(actual) => Err(format!(
            "svm.option_constructor_payload: `some(...)` is annotated `{}` but its payload has \
             type `{}`; malformed checked AST",
            expr.ty.clone().expect("classified option result").name(),
            actual.name()
        )),
        None => Err(format!(
            "svm.option_constructor_payload: `some(...)` payload carries no type; \
             expected `{}` from the result annotation",
            expected.name()
        )),
    }
}

/// Check whatever the representation still owes the program before an option
/// is lowered. Only a nullable raw pointer owes anything: it names a record,
/// and an index outside the checked program is a lowering bug rather than a
/// value the machine could hold.
fn check_option_repr(ctx: &LowerCtx<'_>, repr: SvmOptionRepr) -> Result<(), String> {
    match repr {
        SvmOptionRepr::Ordinary(_) => Ok(()),
        SvmOptionRepr::RawRecord(record) => ctx.record(record).map(|_| ()),
        SvmOptionRepr::AffineBoolArray => {
            unreachable!("general option classification excludes affine options")
        }
    }
}

fn validate_option_accessor(
    ctx: &LowerCtx<'_>,
    expr: &Expr,
    operand: &Expr,
    value: bool,
) -> Result<SvmOptionRepr, String> {
    let accessor = if value { ".value" } else { ".is_some" };
    let repr = match &operand.ty {
        // The owning family is classified first: `.value` on it is a copy,
        // and the ordinary arm below would hand it the copying lowering.
        Some(ty) if ty.is_affine_option() && value => {
            return Err(affine_option_unsupported(
                ty.clone(),
                "copying `.value` accessor operand",
            ));
        }
        Some(ty) if is_affine_bool_option(ty) => {
            let ExprKind::Var(name) = &operand.kind else {
                return Err(
                    "svm.affine_option_temporary: `.is_some` requires a named affine-option local"
                        .into(),
                );
            };
            let binding = ctx.initialized_local(name, "affine-option `.is_some`")?;
            if binding.ty != *ty {
                return Err(format!(
                    "svm.local_type: affine-option `.is_some` names `{name}` of type `{}` but its operand is annotated `{}`",
                    binding.ty.name(),
                    ty.name()
                ));
            }
            if !binding.mutable {
                return Err(format!(
                    "svm.affine_option_immutable: affine option local `{name}` must be mutable"
                ));
            }
            SvmOptionRepr::AffineBoolArray
        }
        Some(ty) if ty.is_affine_option() => {
            return Err(affine_option_unsupported(
                ty.clone(),
                &format!("`{accessor}` operand"),
            ));
        }
        Some(Ty::Option(payload)) => {
            validate_option_payload(payload, "option accessor operand")?;
            SvmOptionRepr::Ordinary(*payload.clone())
        }
        Some(Ty::OptionRaw(record)) => SvmOptionRepr::RawRecord(*record),
        Some(ty) => {
            return Err(format!(
                "svm.option_accessor_operand: `{accessor}` operand has type `{}`; \
                 expected an ordinary or nullable-raw option annotation",
                ty.name()
            ));
        }
        None => {
            return Err(format!(
                "svm.option_accessor_operand: `{accessor}` operand carries no type; \
                 expected an ordinary or nullable-raw option annotation"
            ));
        }
    };
    let expected = if value {
        match repr {
            SvmOptionRepr::Ordinary(ref payload) => payload.clone(),
            SvmOptionRepr::RawRecord(record) => Ty::RawRecord(record),
            SvmOptionRepr::AffineBoolArray => {
                unreachable!("affine options have no copying `.value` accessor")
            }
        }
    } else {
        Ty::Bool
    };
    match &expr.ty {
        Some(actual) if *actual == expected => Ok(repr),
        Some(actual) => Err(format!(
            "svm.option_accessor_result: `{accessor}` is annotated `{}`; expected `{}` \
             from its operand type",
            actual.name(),
            expected.name()
        )),
        None => Err(format!(
            "svm.option_accessor_result: `{accessor}` carries no result type; \
             expected `{}` from its operand type",
            expected.name()
        )),
    }
}

/// Re-check positional exclusions from the checked-language boundary.  The
/// differential harness must remain strict even if it is ever handed a
/// malformed or prematurely widened checked AST.
fn validate_program_option_positions(program: &Program) -> Result<(), String> {
    fn validate_function_positions(
        function: &Fn,
        context: &str,
        trait_member: bool,
    ) -> Result<(), String> {
        for parameter in &function.params {
            validate_parameter_ty(
                &parameter.ty,
                &format!("{context} parameter `{}`", parameter.name),
            )?;
        }
        if function.ret.is_affine_option() {
            return Err(affine_option_unsupported(
                function.ret.clone(),
                &format!("{context} return type"),
            ));
        }
        if function.ret.is_bool_array() {
            return Err(format!(
                "svm.bool_array_position_unsupported: {context} returns a Boolean array; Boolean arrays are owned locals only"
            ));
        }
        if trait_member {
            if let Some(parameter) = function
                .params
                .iter()
                .find(|parameter| matches!(parameter.ty, Ty::Option(_)))
            {
                return Err(format!(
                    "svm.option_position_unsupported: {context} parameter `{}` is an ordinary option; \
                     trait option parameters are not in the SVM model",
                    parameter.name
                ));
            }
            if let Ty::Option(payload) = &function.ret {
                validate_option_payload(payload, context)?;
                return Err(format!(
                    "svm.option_position_unsupported: {context} returns an ordinary option; \
                     trait option returns are not in the SVM model"
                ));
            }
        }
        if function.extern_info.is_some() {
            return Err(format!(
                "`{}` is an audited extern: the machine has no semantics for a foreign call",
                function.name
            ));
        }
        Ok(())
    }

    for function in program.fns.iter().chain(&program.fn_templates) {
        validate_function_positions(function, &format!("function `{}`", function.name), false)?;
    }
    for class in program.classes.iter().chain(&program.class_templates) {
        for field in &class.fields {
            if field.ty.is_affine_option() {
                return Err(affine_option_unsupported(
                    field.ty.clone(),
                    &format!("class `{}.{}` field", class.name, field.name),
                ));
            }
            if field.ty.is_bool_array() {
                return Err(format!(
                    "svm.bool_array_position_unsupported: class `{}.{}` has a Boolean-array-typed field; Boolean arrays are owned locals only",
                    class.name, field.name
                ));
            }
            if let Ty::Option(payload) = &field.ty {
                validate_option_payload(payload, &format!("class `{}`", class.name))?;
                return Err(format!(
                    "svm.option_position_unsupported: class `{}.{}` has an option-typed field; \
                     option-valued fields are not in the SVM model",
                    class.name, field.name
                ));
            }
        }
        for initializer in &class.inits {
            validate_function_positions(
                initializer,
                &format!("initializer `{}::{}`", class.name, initializer.name),
                false,
            )?;
        }
        for method in &class.methods {
            validate_function_positions(
                &method.f,
                &format!("method `{}.{}`", class.name, method.f.name),
                false,
            )?;
        }
    }
    for record in &program.records {
        if record.layout.size <= 0
            || record.layout.align <= 0
            || (record.layout.align & (record.layout.align - 1)) != 0
        {
            return Err(format!(
                "svm.record_schema_layout: record `{}` has size {} and alignment {}; size must be positive and alignment a positive power of two",
                record.name, record.layout.size, record.layout.align
            ));
        }
        let mut field_names = HashSet::new();
        let mut extents: Vec<(i128, i128, &str)> = Vec::new();
        for field in &record.fields {
            if field.ty.is_affine_option() {
                return Err(affine_option_unsupported(
                    field.ty.clone(),
                    &format!("record `{}.{}` field", record.name, field.name),
                ));
            }
            if field.ty.is_bool_array() {
                return Err(format!(
                    "svm.bool_array_position_unsupported: record `{}.{}` has a Boolean-array-typed field; Boolean arrays are owned locals only",
                    record.name, field.name
                ));
            }
            if !field_names.insert(field.name.as_str()) {
                return Err(format!(
                    "svm.record_schema_duplicate: record `{}` repeats field `{}`",
                    record.name, field.name
                ));
            }
            let Some(field_layout) = field.ty.storage_layout() else {
                return Err(format!(
                    "svm.record_schema_type: record `{}.{}` has unsupported field type `{}`",
                    record.name,
                    field.name,
                    field.ty.name()
                ));
            };
            let Some(end) = field.offset.checked_add(field_layout.size) else {
                return Err(format!(
                    "svm.record_schema_geometry: record `{}.{}` extent overflows",
                    record.name, field.name
                ));
            };
            if record.layout.align % field_layout.align != 0 {
                return Err(format!(
                    "svm.record_schema_geometry: record `{}.{}` needs field alignment {}, but outer alignment is {}",
                    record.name, field.name, field_layout.align, record.layout.align
                ));
            }
            if field.offset < 0
                || field.offset % field_layout.align != 0
                || end > record.layout.size
            {
                return Err(format!(
                    "svm.record_schema_geometry: record `{}.{}` offset {} and {}-byte extent do not fit size {} at alignment {}",
                    record.name,
                    field.name,
                    field.offset,
                    field_layout.size,
                    record.layout.size,
                    field_layout.align
                ));
            }
            if let Some((_, _, previous)) = extents
                .iter()
                .find(|(lo, hi, _)| field.offset < *hi && *lo < end)
            {
                return Err(format!(
                    "svm.record_schema_geometry: record `{}` fields `{previous}` and `{}` overlap",
                    record.name, field.name
                ));
            }
            extents.push((field.offset, end, field.name.as_str()));
        }
    }
    for trait_ in &program.traits {
        for method in &trait_.methods {
            validate_function_positions(
                method,
                &format!("trait method `{}::{}`", trait_.name, method.name),
                true,
            )?;
        }
    }
    for implementation in &program.impls {
        for function in &implementation.fns {
            validate_function_positions(
                function,
                &format!(
                    "trait implementation method `{}::{}`",
                    implementation.trait_name, function.name
                ),
                true,
            )?;
        }
    }
    Ok(())
}

fn validate_scoped_stmts(ctx: &mut LowerCtx<'_>, stmts: &[Stmt]) -> Result<(), String> {
    let mut child = ctx.clone();
    let result = validate_stmt_payloads(&mut child, stmts);
    ctx.declared = child.declared;
    result
}

fn block_definitely_returns(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|stmt| match stmt {
        Stmt::Return { .. } => true,
        Stmt::If {
            then_block,
            else_block: Some(else_block),
            ..
        } => block_definitely_returns(then_block) && block_definitely_returns(else_block),
        Stmt::Unsafe { body, .. } => block_definitely_returns(body),
        _ => false,
    })
}

fn contains_return(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|stmt| match stmt {
        Stmt::Return { .. } => true,
        Stmt::If {
            then_block,
            else_block,
            ..
        } => contains_return(then_block) || else_block.as_deref().is_some_and(contains_return),
        Stmt::While { body, .. } | Stmt::Unsafe { body, .. } | Stmt::Expose { body, .. } => {
            contains_return(body)
        }
        _ => false,
    })
}

fn merge_if_initialization(
    ctx: &mut LowerCtx<'_>,
    before: &HashMap<String, LocalBinding>,
    then_locals: &HashMap<String, LocalBinding>,
    then_returns: bool,
    else_locals: &HashMap<String, LocalBinding>,
    else_returns: bool,
) {
    for (name, original) in before {
        let initialized = match (then_returns, else_returns) {
            (false, false) => {
                then_locals.get(name).is_some_and(|local| local.initialized)
                    && else_locals.get(name).is_some_and(|local| local.initialized)
            }
            (false, true) => then_locals.get(name).is_some_and(|local| local.initialized),
            (true, false) => else_locals.get(name).is_some_and(|local| local.initialized),
            (true, true) => original.initialized,
        };
        ctx.locals
            .get_mut(name)
            .expect("pre-branch local remains active")
            .initialized = initialized;
    }
}

fn merge_executed_scope_initialization(
    ctx: &mut LowerCtx<'_>,
    before: &HashMap<String, LocalBinding>,
    after: &HashMap<String, LocalBinding>,
) {
    for name in before.keys() {
        ctx.locals
            .get_mut(name)
            .expect("pre-scope local remains active")
            .initialized = after
            .get(name)
            .expect("pre-scope local remains active in child")
            .initialized;
    }
}

fn validate_stmt_payloads(ctx: &mut LowerCtx<'_>, stmts: &[Stmt]) -> Result<(), String> {
    for stmt in stmts {
        match stmt {
            Stmt::Decl {
                ty,
                init,
                name,
                mutable,
                ..
            } => {
                if ty.is_affine_option() {
                    validate_affine_bool_option_decl(
                        ctx,
                        name,
                        ty.clone(),
                        *mutable,
                        init.as_ref(),
                    )?;
                } else if ty.is_bool_array() {
                    let Some(init) = init else {
                        return Err(format!(
                            "svm.bool_array_fresh_local: Boolean array local `{name}` must be initialized by a fresh literal or allocation"
                        ));
                    };
                    validate_fresh_bool_array_initializer(ctx, ty.clone(), init, name)?;
                } else if let Some(init) = init {
                    validate_ty_payload(ty.clone(), &format!("declaration `{name}`"))?;
                    validate_expr_payloads(ctx, init)?;
                    validate_sink_type(ctx, ty.clone(), init, &format!("initializer of `{name}`"))?;
                } else {
                    validate_ty_payload(ty.clone(), &format!("declaration `{name}`"))?;
                }
                ctx.insert_local(name, ty.clone(), *mutable, init.is_some())?;
            }
            Stmt::Assign { name, value, .. } => {
                let Some(binding) = ctx.local(name) else {
                    return Err(format!(
                        "svm.local_type: assignment names unknown or out-of-scope local `{name}`"
                    ));
                };
                if !binding.mutable {
                    return Err(format!(
                        "svm.local_type: assignment targets immutable local `{name}`"
                    ));
                }
                if binding.ty.is_affine_option() {
                    return Err(affine_option_unsupported(
                        binding.ty,
                        &format!("whole-option assignment to `{name}`"),
                    ));
                }
                validate_expr_payloads(ctx, value)?;
                validate_sink_type(
                    ctx,
                    binding.ty.clone(),
                    value,
                    &format!("assignment to `{name}`"),
                )?;
                validate_array_rebind(ctx, name)?;
                ctx.locals
                    .get_mut(name)
                    .expect("resolved assignment")
                    .initialized = true;
            }
            Stmt::ExprStmt(value) | Stmt::FieldAssign { value, .. } => {
                validate_expr_payloads(ctx, value)?;
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                validate_expr_payloads(ctx, cond)?;
                validate_sink_type(ctx, Ty::Bool, cond, "if condition")?;
                let before = ctx.locals.clone();
                let mut then_ctx = ctx.clone();
                validate_stmt_payloads(&mut then_ctx, then_block)?;
                ctx.declared = then_ctx.declared.clone();

                let mut else_ctx = ctx.clone();
                else_ctx.locals = before.clone();
                if let Some(else_block) = else_block {
                    validate_stmt_payloads(&mut else_ctx, else_block)?;
                    ctx.declared = else_ctx.declared.clone();
                }

                merge_if_initialization(
                    ctx,
                    &before,
                    &then_ctx.locals,
                    block_definitely_returns(then_block),
                    &else_ctx.locals,
                    else_block.as_deref().is_some_and(block_definitely_returns),
                );
            }
            Stmt::Return { value, .. } => {
                if let Some(value) = value {
                    validate_expr_payloads(ctx, value)?;
                    validate_return(ctx, value)?;
                }
            }
            Stmt::Assert(_) => {}
            Stmt::VarDecl {
                name,
                init,
                ty: Some(ty),
                mutable,
                ..
            } => {
                if matches!(init.kind, ExprKind::OptTake { .. }) {
                    return Err(format!(
                        "svm.affine_option_take_position: inferred declaration `{name}` cannot receive `.take`; use an explicit owned `[bool]` declaration"
                    ));
                }
                if ty.is_affine_option() {
                    return Err(affine_option_unsupported(
                        ty.clone(),
                        &format!("inferred declaration `{name}`"),
                    ));
                }
                validate_ty_payload(ty.clone(), &format!("inferred declaration `{name}`"))?;
                if ty.is_bool_array() {
                    validate_fresh_bool_array_initializer(ctx, ty.clone(), init, name)?;
                } else {
                    validate_expr_payloads(ctx, init)?;
                    validate_sink_type(ctx, ty.clone(), init, &format!("initializer of `{name}`"))?;
                }
                ctx.insert_local(name, ty.clone(), *mutable, true)?;
            }
            Stmt::VarDecl { name, ty: None, .. } => {
                return Err(format!(
                    "svm.local_type: inferred declaration `{name}` carries no checked type"
                ));
            }
            Stmt::FieldStore { index, value, .. } => {
                validate_expr_payloads(ctx, index)?;
                validate_expr_payloads(ctx, value)?;
            }
            Stmt::Store {
                array,
                index,
                value,
                ..
            } => validate_array_store(ctx, array, index, value)?,
            Stmt::While { cond, body, .. } => {
                validate_expr_payloads(ctx, cond)?;
                validate_sink_type(ctx, Ty::Bool, cond, "while condition")?;
                validate_scoped_stmts(ctx, body)?;
            }
            Stmt::Unsafe { body, .. } => validate_stmt_payloads(ctx, body)?,
            Stmt::Expose {
                array,
                mutable,
                ptr,
                res,
                body,
                ..
            } => {
                validate_array_exposure(ctx, array, *mutable)?;
                if contains_return(body) {
                    return Err(
                        "svm.expose_return: return inside array exposure would bypass generated copyback and release"
                            .into(),
                    );
                }
                let before = ctx.locals.clone();
                let mut child = ctx.clone();
                child.insert_local(ptr, Ty::Raw(IntTy::U8), false, true)?;
                child.insert_local(res, Ty::Res(ResKind::RawSpan), *mutable, true)?;
                let result = validate_stmt_payloads(&mut child, body);
                ctx.declared = child.declared.clone();
                result?;
                merge_executed_scope_initialization(ctx, &before, &child.locals);
            }
            Stmt::StaticAlloc { size, ptr, res, .. } => {
                validate_allocation_size(ctx, size, "static allocation size")?;
                validate_expr_payloads(ctx, size)?;
                ctx.insert_local(ptr, Ty::Raw(IntTy::U8), false, true)?;
                ctx.insert_local(res, Ty::Res(ResKind::RawSpan), true, true)?;
            }
            Stmt::SystemAlloc {
                size,
                ptr,
                res,
                release,
                ..
            } => {
                validate_allocation_size(ctx, size, "system allocation size")?;
                validate_expr_payloads(ctx, size)?;
                ctx.insert_local(ptr, Ty::Raw(IntTy::U8), false, true)?;
                ctx.insert_local(res, Ty::Res(ResKind::RawSpan), true, true)?;
                ctx.insert_local(release, Ty::Res(ResKind::SystemDealloc), false, true)?;
            }
            Stmt::SystemDealloc {
                ptr, res, release, ..
            } => {
                validate_expr_payloads(ctx, ptr)?;
                validate_expr_payloads(ctx, res)?;
                validate_expr_payloads(ctx, release)?;
                validate_system_dealloc(ctx, ptr, res, release)?;
            }
        }
    }
    Ok(())
}

/// Resolve an A-normal call against the same executable program that will be
/// emitted, and re-check all cached types.  Call and option constructors in the
/// Lean core are untyped, so a forged result annotation must not be able to
/// turn a scalar return into an option (or vice versa).
fn validate_call_signature(
    ctx: &LowerCtx<'_>,
    call: &Expr,
    callee: &str,
    args: &[Expr],
) -> Result<(), String> {
    let ExprKind::Call { type_args, .. } = &call.kind else {
        return Err("svm.call_shape: call validator received a non-call expression".into());
    };
    if !type_args.is_empty() {
        return Err(
            "svm.type_parameter_unsupported: generic type arguments escaped monomorphization"
                .into(),
        );
    }
    let mut matches = ctx
        .program
        .fns
        .iter()
        .filter(|function| function.name == callee);
    let Some(function) = matches.next() else {
        return Err(format!(
            "svm.call_target: call target `{callee}` is absent from the executable program"
        ));
    };
    if matches.next().is_some() {
        return Err(format!(
            "svm.call_target: call target `{callee}` is ambiguous in the executable program"
        ));
    }
    match &call.ty {
        Some(actual) if *actual == function.ret => {}
        Some(actual) => {
            return Err(format!(
                "svm.call_result_type: call to `{callee}` is annotated `{}`; callee returns `{}`",
                actual.name(),
                function.ret.clone().name()
            ));
        }
        None => {
            return Err(format!(
                "svm.call_result_type: call to `{callee}` carries no result type; callee returns `{}`",
                function.ret.clone().name()
            ));
        }
    }
    if args.len() != function.params.len() {
        return Err(format!(
            "svm.call_arity: call to `{callee}` supplies {} argument(s); callee expects {}",
            args.len(),
            function.params.len()
        ));
    }
    if function.ret.clone().is_resource()
        || function
            .params
            .iter()
            .any(|parameter| parameter.ty.clone().is_resource())
    {
        return Err(format!(
            "svm.call_resource_unsupported: `{callee}` has resource parameters or result; erased authority has no SVM call ABI"
        ));
    }
    for (index, (arg, parameter)) in args.iter().zip(&function.params).enumerate() {
        validate_sink_type(
            ctx,
            parameter.ty.clone(),
            arg,
            &format!("argument {} to `{callee}`", index + 1),
        )
        .map_err(|error| {
            format!(
                "svm.call_argument_type: argument {} to `{callee}` does not match parameter `{}`: {error}",
                index + 1,
                parameter.name
            )
        })?;
    }
    Ok(())
}

fn validate_expr_payloads(ctx: &LowerCtx<'_>, expr: &Expr) -> Result<(), String> {
    if let Some(ty) = &expr.ty {
        validate_ty_payload(ty.clone(), "expression annotation")?;
        if ty.is_owned_bool_array()
            && !matches!(
                &expr.kind,
                ExprKind::OptTake { .. } | ExprKind::OptValue { .. }
            )
        {
            return Err(
                "svm.bool_array_position_unsupported: an owned-Boolean-array expression is only supported as the initializer of a fresh owned local"
                    .into(),
            );
        }
    }

    match &expr.kind {
        ExprKind::Index { array, index, .. } => {
            validate_array_index(ctx, expr, array, index)?;
        }
        ExprKind::AllocArray { elem, len, init } => {
            validate_alloc_array(ctx, expr, elem.clone(), len, init)?;
        }
        ExprKind::ArrayLit(elements) => {
            validate_array_literal(ctx, expr, elements)?;
        }
        ExprKind::Len { array } => {
            validate_array_len(ctx, expr, array)?;
        }
        ExprKind::Widen { target, arg } | ExprKind::Narrow { target, arg } => {
            if matches!(target, IntTy::TParam(_)) {
                return Err(
                    "svm.type_parameter_unsupported: conversion target contains an unresolved type parameter"
                        .into(),
                );
            }
            semantic_expr_ty(
                ctx,
                expr,
                expr.ty.clone().unwrap_or(Ty::Int(*target)),
                "conversion expression",
            )?;
            validate_expr_payloads(ctx, arg)?;
        }
        ExprKind::Call {
            callee,
            type_args,
            args,
            ..
        } => {
            if !type_args.is_empty() {
                return Err(
                    "svm.type_parameter_unsupported: generic type arguments escaped monomorphization"
                        .into(),
                );
            }
            validate_call_signature(ctx, expr, callee, args)?;
            for arg in args {
                validate_expr_payloads(ctx, arg)?;
            }
        }
        ExprKind::CtorCall {
            type_args, args, ..
        } => {
            if !type_args.is_empty() {
                return Err(
                    "svm.type_parameter_unsupported: generic type arguments escaped monomorphization"
                        .into(),
                );
            }
            for arg in args {
                validate_expr_payloads(ctx, arg)?;
            }
        }
        ExprKind::SomeE(operand) => {
            validate_some_constructor(expr, operand)?;
            semantic_expr_ty(
                ctx,
                expr,
                expr.ty.clone().unwrap_or(Ty::Unit),
                "option constructor",
            )?;
            validate_expr_payloads(ctx, operand)?;
        }
        ExprKind::NoneE => {
            svm_option_repr(expr, "none")?;
        }
        ExprKind::IsSome { operand } => {
            let repr = validate_option_accessor(ctx, expr, operand, false)?;
            semantic_expr_ty(ctx, expr, Ty::Bool, "option is_some accessor")?;
            if !matches!(repr, SvmOptionRepr::AffineBoolArray) {
                validate_expr_payloads(ctx, operand)?;
            }
        }
        ExprKind::OptValue { operand } => {
            validate_option_accessor(ctx, expr, operand, true)?;
            semantic_expr_ty(
                ctx,
                expr,
                expr.ty.clone().unwrap_or(Ty::Unit),
                "option value accessor",
            )?;
            validate_expr_payloads(ctx, operand)?;
        }
        ExprKind::OptTake { option, .. } => {
            return Err(affine_option_take_position(option));
        }
        ExprKind::Unary { operand, .. } => {
            semantic_expr_ty(
                ctx,
                expr,
                expr.ty.clone().unwrap_or(Ty::Unit),
                "unary expression",
            )?;
            validate_expr_payloads(ctx, operand)?;
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            semantic_expr_ty(
                ctx,
                expr,
                expr.ty.clone().unwrap_or(Ty::Unit),
                "binary expression",
            )?;
            validate_expr_payloads(ctx, lhs)?;
            validate_expr_payloads(ctx, rhs)?;
        }
        ExprKind::ResOp { args, .. } => {
            semantic_expr_ty(
                ctx,
                expr,
                expr.ty.clone().unwrap_or(Ty::Unit),
                "sealed resource expression",
            )?;
            for arg in args {
                validate_expr_payloads(ctx, arg)?;
            }
        }
        ExprKind::RawOp { args, .. } => {
            semantic_expr_ty(
                ctx,
                expr,
                expr.ty.clone().unwrap_or(Ty::Unit),
                "raw operation expression",
            )?;
            for arg in args {
                validate_expr_payloads(ctx, arg)?;
            }
        }
        ExprKind::DeviceOp { args, .. } => {
            semantic_expr_ty(
                ctx,
                expr,
                expr.ty.clone().unwrap_or(Ty::Unit),
                "device operation expression",
            )?;
            for arg in args {
                validate_expr_payloads(ctx, arg)?;
            }
        }
        ExprKind::RecordLit { record, args, .. } => {
            validate_record_literal(ctx, expr, record, args)?;
            for arg in args {
                validate_expr_payloads(ctx, arg)?;
            }
        }
        ExprKind::TraitCall { args, .. } => {
            for arg in args {
                validate_expr_payloads(ctx, arg)?;
            }
        }
        ExprKind::MethodCall { recv, args, .. } => {
            reject_named_affine_option(ctx, recv, "a method receiver")?;
            for arg in args {
                validate_expr_payloads(ctx, arg)?;
            }
        }
        ExprKind::SelfFieldIndex { index, .. } => {
            validate_expr_payloads(ctx, index)?;
        }
        ExprKind::ClassFieldIndex { obj, index, .. } => {
            reject_named_affine_option(ctx, obj, "a class-field index receiver")?;
            validate_expr_payloads(ctx, index)?;
        }
        ExprKind::Var(name) => {
            validate_local_var(ctx, expr, name, "variable expression")?;
        }
        ExprKind::IntLit(_) => {
            semantic_expr_ty(
                ctx,
                expr,
                expr.ty.clone().unwrap_or(Ty::Unit),
                "integer literal",
            )?;
        }
        ExprKind::BoolLit(_) => {
            semantic_expr_ty(
                ctx,
                expr,
                expr.ty.clone().unwrap_or(Ty::Unit),
                "Boolean literal",
            )?;
        }
        ExprKind::Borrow { array, .. } => {
            reject_named_affine_option(ctx, array, "a borrow source")?;
        }
        ExprKind::SelfField { .. } | ExprKind::SelfFieldLen { .. } => {}
        ExprKind::ClassField { obj, .. } | ExprKind::ClassFieldLen { obj, .. } => {
            reject_named_affine_option(ctx, obj, "a class-field receiver")?;
        }
        ExprKind::RecordField { obj, field, .. } => {
            reject_named_affine_option(ctx, obj, "a record-field receiver")?;
            semantic_record_field_ty(ctx, expr, obj, field)?;
        }
    }
    Ok(())
}

/// Lower a zero-argument function's body to a Lean `List Stmt` term.
pub fn lower_fn(program: &Program, f: &Fn) -> Result<String, String> {
    if let Some(parameter) = f
        .params
        .iter()
        .find(|parameter| parameter.ty.is_affine_option())
    {
        return Err(affine_option_unsupported(
            parameter.ty.clone(),
            &format!("parameter `{}`", parameter.name),
        ));
    }
    if f.ret.is_affine_option() {
        return Err(affine_option_unsupported(
            f.ret.clone(),
            &format!("return type of `{}`", f.name),
        ));
    }
    if !f.params.is_empty() {
        return Err("differential subjects must take no parameters".into());
    }
    validate_program_option_positions(program)?;
    let mut validation_ctx = LowerCtx::for_function(program, f)?;
    validate_fn_payloads(&mut validation_ctx, f)?;
    let mut lowering_ctx = LowerCtx::for_function(program, f)?;
    lower_block(&mut lowering_ctx, &f.body)
}

/// Lower any function to a `Prog.ofList` entry: `("name", ⟨[params],
/// body⟩)`. A parameter is either a machine value or a borrowed array —
/// the machine binds the caller's sequence, and a unique borrow's exit
/// value returns to the caller's local when the frame pops (`Arg.lend`).
/// Resources, class receivers, and owned arrays stay outside.
pub fn lower_fn_entry(program: &Program, f: &Fn) -> Result<String, String> {
    validate_program_option_positions(program)?;
    let mut validation_ctx = LowerCtx::for_function(program, f)?;
    validate_fn_payloads(&mut validation_ctx, f)?;
    let mut lowering_ctx = LowerCtx::for_function(program, f)?;
    for p in &f.params {
        match &p.ty {
            Ty::Int(_) | Ty::Bool => {}
            Ty::Option(payload) => {
                validate_option_payload(payload, &format!("parameter `{}`", p.name))?;
            }
            Ty::Record(ri) | Ty::RawRecord(ri) | Ty::OptionRaw(ri) => {
                lowering_ctx.record(*ri)?;
            }
            borrowed if borrowed.as_array_borrow().is_some() => {}
            _ => {
                return Err(format!(
                    "parameter `{}`: its type is outside the SVM core subset (resources are scoped out)",
                    p.name
                ));
            }
        }
    }
    let params: Vec<String> = f.params.iter().map(|p| format!("\"{}\"", p.name)).collect();
    Ok(format!(
        "(\"{}\", ⟨[{}], {}⟩)",
        f.name,
        params.join(", "),
        lower_block(&mut lowering_ctx, &f.body)?
    ))
}

/// Fresh names for the statements an exposure expands into. A counter is
/// enough: lowering is single-threaded and one pass.
fn next_loan() -> usize {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static N: AtomicUsize = AtomicUsize::new(0);
    N.fetch_add(1, Ordering::Relaxed)
}

fn lower_block(ctx: &mut LowerCtx<'_>, stmts: &[Stmt]) -> Result<String, String> {
    lower_block_erasing(ctx, stmts)
}

fn lower_block_erasing(ctx: &mut LowerCtx<'_>, stmts: &[Stmt]) -> Result<String, String> {
    let mut out = Vec::new();
    for s in stmts {
        if let Some(t) = lower_stmt_erasing(ctx, s)? {
            out.push(t);
        }
    }
    Ok(format!("[{}]", out.join(", ")))
}

fn lower_scoped_block(ctx: &mut LowerCtx<'_>, stmts: &[Stmt]) -> Result<String, String> {
    let mut child = ctx.clone();
    let result = lower_block_erasing(&mut child, stmts);
    ctx.declared = child.declared;
    result
}

fn lower_stmt_erasing(ctx: &mut LowerCtx<'_>, s: &Stmt) -> Result<Option<String>, String> {
    Ok(match s {
        Stmt::Decl {
            name,
            ty,
            mutable,
            init,
            ..
        } if ty.is_affine_option() => {
            validate_affine_bool_option_decl(ctx, name, ty.clone(), *mutable, init.as_ref())?;
            let lowered =
                lower_affine_bool_option_bind(ctx, name, ty.clone(), *mutable, init.as_ref())?;
            ctx.insert_local(name, ty.clone(), *mutable, true)?;
            Some(lowered)
        }
        Stmt::Decl {
            name,
            ty,
            mutable,
            init,
            ..
        } if ty.is_bool_array() => {
            let Some(initializer) = init else {
                return Err(format!(
                    "svm.bool_array_fresh_local: Boolean array local `{name}` must be initialized by a fresh literal or allocation"
                ));
            };
            let lowered = lower_fresh_bool_array_bind(ctx, name, ty.clone(), initializer)?;
            ctx.insert_local(name, ty.clone(), *mutable, true)?;
            Some(lowered)
        }
        // A ⊥ slot: the machine conflates "undeclared" with ⊥, and
        // definite initialization guarantees assignment-before-read.
        Stmt::Decl {
            name,
            ty,
            mutable,
            init: None,
            ..
        } => {
            ctx.insert_local(name, ty.clone(), *mutable, false)?;
            None
        }
        Stmt::Decl {
            name,
            ty,
            mutable,
            init: Some(e),
            ..
        } if ty.clone().is_resource() => {
            validate_sink_type(ctx, ty.clone(), e, &format!("initializer of `{name}`"))?;
            let lowered = lower_erased_resource_bind(ctx, name, e)?;
            ctx.insert_local(name, ty.clone(), *mutable, true)?;
            lowered
        }
        Stmt::Decl {
            name,
            ty,
            mutable,
            init: Some(e),
            ..
        } => {
            validate_sink_type(ctx, ty.clone(), e, &format!("initializer of `{name}`"))?;
            let lowered = lower_bind(ctx, name, e)?;
            ctx.insert_local(name, ty.clone(), *mutable, true)?;
            Some(lowered)
        }
        Stmt::VarDecl {
            name,
            init,
            ty: Some(_),
            ..
        } if matches!(init.kind, ExprKind::OptTake { .. }) => {
            return Err(format!(
                "svm.affine_option_take_position: inferred declaration `{name}` cannot receive `.take`; use an explicit owned `[bool]` declaration"
            ));
        }
        Stmt::VarDecl {
            name,
            init: _,
            ty: Some(ty),
            ..
        } if ty.is_affine_option() => {
            return Err(affine_option_unsupported(
                ty.clone(),
                &format!("inferred declaration `{name}`"),
            ));
        }
        Stmt::VarDecl {
            name,
            init,
            ty: Some(ty),
            mutable,
            ..
        } if ty.is_bool_array() => {
            let lowered = lower_fresh_bool_array_bind(ctx, name, ty.clone(), init)?;
            ctx.insert_local(name, ty.clone(), *mutable, true)?;
            Some(lowered)
        }
        Stmt::VarDecl {
            name,
            init,
            ty: Some(ty),
            mutable,
            ..
        } if ty.clone().is_resource() => {
            validate_sink_type(ctx, ty.clone(), init, &format!("initializer of `{name}`"))?;
            let lowered = lower_erased_resource_bind(ctx, name, init)?;
            ctx.insert_local(name, ty.clone(), *mutable, true)?;
            lowered
        }
        Stmt::VarDecl {
            name,
            init,
            ty: Some(ty),
            mutable,
            ..
        } => {
            validate_sink_type(ctx, ty.clone(), init, &format!("initializer of `{name}`"))?;
            let lowered = lower_bind(ctx, name, init)?;
            ctx.insert_local(name, ty.clone(), *mutable, true)?;
            Some(lowered)
        }
        Stmt::VarDecl { name, ty: None, .. } => {
            return Err(format!(
                "svm.local_type: inferred declaration `{name}` carries no checked type"
            ));
        }
        // `unsafe { ... }` is a marker with no machine step of its own.
        Stmt::Unsafe { body, .. } => {
            let inner = lower_block_erasing(ctx, body)?;
            // Splice the body in place: the block does not scope.
            Some(
                inner
                    .trim_start_matches('[')
                    .trim_end_matches(']')
                    .to_string(),
            )
        }
        Stmt::StaticAlloc { size, ptr, res, .. } => {
            validate_allocation_size(ctx, size, "static allocation size")?;
            let lowered = format!("(.rawAlloc \"{ptr}\" {})", lower_expr(ctx, size)?);
            ctx.insert_local(ptr, Ty::Raw(IntTy::U8), false, true)?;
            ctx.insert_local(res, Ty::Res(ResKind::RawSpan), true, true)?;
            Some(lowered)
        }
        Stmt::SystemAlloc {
            size,
            ptr,
            res,
            release,
            ..
        } => {
            validate_allocation_size(ctx, size, "system allocation size")?;
            let lowered = format!("(.rawAlloc \"{ptr}\" {})", lower_expr(ctx, size)?);
            ctx.insert_local(ptr, Ty::Raw(IntTy::U8), false, true)?;
            ctx.insert_local(res, Ty::Res(ResKind::RawSpan), true, true)?;
            ctx.insert_local(release, Ty::Res(ResKind::SystemDealloc), false, true)?;
            Some(lowered)
        }
        Stmt::SystemDealloc {
            ptr, res, release, ..
        } => {
            validate_system_dealloc(ctx, ptr, res, release)?;
            Some(format!("(.rawFree {})", lower_expr(ctx, ptr)?))
        }
        // The machine has no exposure primitive: the construct *is* the
        // loan-allocation model, so lowering spells it out — allocate,
        // copy the bytes in, run the body, copy the final bytes back,
        // release. A native backend would take the address of the
        // existing buffer instead; nonescape is what makes the two
        // observationally equivalent (ADR 0026).
        Stmt::Expose {
            array,
            mutable,
            ptr,
            res,
            body,
            ..
        } => {
            validate_array_exposure(ctx, array, *mutable)?;
            if contains_return(body) {
                return Err(
                    "svm.expose_return: return inside array exposure would bypass generated copyback and release"
                        .into(),
                );
            }
            let id = next_loan();
            let loan = format!("_loan{id}");
            let i = format!("_li{id}");
            let t = format!("_lb{id}");
            let n = format!("(.len \"{array}\")");
            let at = format!("(.ptrAdd (.var \"{loan}\") (.var \"{i}\"))");
            let before = ctx.locals.clone();
            let mut child = ctx.clone();
            child.insert_local(ptr, Ty::Raw(IntTy::U8), false, true)?;
            child.insert_local(res, Ty::Res(ResKind::RawSpan), *mutable, true)?;
            let inner_result = lower_block_erasing(&mut child, body);
            ctx.declared = child.declared.clone();
            let inner = inner_result?;
            merge_executed_scope_initialization(ctx, &before, &child.locals);
            let inner = inner.trim_start_matches('[').trim_end_matches(']');
            let mut parts: Vec<String> = Vec::new();
            parts.push(format!("(.rawAlloc \"{loan}\" {n})"));
            parts.push(format!("(.assign \"{i}\" (.intLit .u64 0))"));
            parts.push(format!(
                "(.while (.cmp .lt (.var \"{i}\") {n}) \
                 [(.rawStore8 {at} (.index \"{array}\" (.var \"{i}\"))), \
                  (.assign \"{i}\" (.wrapArith .add .u64 (.var \"{i}\") (.intLit .u64 1)))])"
            ));
            // The body's own pointer name is the loan's start. `res` is
            // erased: authority has no runtime representation.
            parts.push(format!("(.assign \"{ptr}\" (.var \"{loan}\"))"));
            if !inner.is_empty() {
                parts.push(inner.to_string());
            }
            if *mutable {
                parts.push(format!("(.assign \"{i}\" (.intLit .u64 0))"));
                parts.push(format!(
                    "(.while (.cmp .lt (.var \"{i}\") {n}) \
                     [(.rawLoad8 \"{t}\" {at}), \
                      (.store \"{array}\" (.var \"{i}\") (.var \"{t}\")), \
                      (.assign \"{i}\" (.wrapArith .add .u64 (.var \"{i}\") (.intLit .u64 1)))])"
                ));
            }
            parts.push(format!("(.rawFree (.var \"{loan}\"))"));
            Some(parts.join(", "))
        }
        Stmt::Assign { name, value, .. } => {
            let Some(binding) = ctx.local(name) else {
                return Err(format!(
                    "svm.local_type: assignment names unknown or out-of-scope local `{name}`"
                ));
            };
            if !binding.mutable {
                return Err(format!(
                    "svm.local_type: assignment targets immutable local `{name}`"
                ));
            }
            if binding.ty.is_affine_option() {
                return Err(affine_option_unsupported(
                    binding.ty,
                    &format!("whole-option assignment to `{name}`"),
                ));
            }
            validate_sink_type(
                ctx,
                binding.ty.clone(),
                value,
                &format!("assignment to `{name}`"),
            )?;
            validate_array_rebind(ctx, name)?;
            let lowered = if binding.ty.is_resource() {
                lower_erased_resource_bind(ctx, name, value)?
            } else {
                Some(lower_bind(ctx, name, value)?)
            };
            ctx.locals
                .get_mut(name)
                .expect("resolved assignment")
                .initialized = true;
            lowered
        }
        Stmt::Store {
            array,
            index,
            value,
            ..
        } => {
            validate_array_store(ctx, array, index, value)?;
            Some(format!(
                "(.store \"{array}\" {} {})",
                lower_expr(ctx, index)?,
                lower_expr(ctx, value)?
            ))
        }
        Stmt::If {
            cond,
            then_block,
            else_block,
        } => {
            validate_sink_type(ctx, Ty::Bool, cond, "if condition")?;
            let condition = lower_expr(ctx, cond)?;
            let before = ctx.locals.clone();

            let mut then_ctx = ctx.clone();
            let then = lower_block_erasing(&mut then_ctx, then_block)?;
            ctx.declared = then_ctx.declared.clone();

            let mut else_ctx = ctx.clone();
            else_ctx.locals = before.clone();
            let els = match else_block {
                Some(block) => lower_block_erasing(&mut else_ctx, block)?,
                None => "[]".into(),
            };
            ctx.declared = else_ctx.declared.clone();
            merge_if_initialization(
                ctx,
                &before,
                &then_ctx.locals,
                block_definitely_returns(then_block),
                &else_ctx.locals,
                else_block.as_deref().is_some_and(block_definitely_returns),
            );
            Some(format!("(.ite {condition} {then} {els})"))
        }
        Stmt::While {
            cond,
            invariants,
            body,
            ..
        } => {
            if !invariants.is_empty() {
                return Err(
                    "loop invariants are outside the differential subset (interp monitors \
                     them; the machine does not)"
                        .into(),
                );
            }
            validate_sink_type(ctx, Ty::Bool, cond, "while condition")?;
            let condition = lower_expr(ctx, cond)?;
            let body = lower_scoped_block(ctx, body)?;
            Some(format!("(.while {condition} {body})"))
        }
        Stmt::Return { value: Some(e), .. } => {
            validate_return(ctx, e)?;
            Some(format!("(.ret {})", lower_expr(ctx, e)?))
        }
        Stmt::Return { value: None, .. } => {
            return Err("bare `return;` has no SVM form (fall off the end instead)".into());
        }
        // A call for effect: `f(args);` — the discarded-result form of
        // the machine's A-normal call.
        Stmt::ExprStmt(e) => match &e.kind {
            // Raw operations are statements in the machine (ADR 0025).
            // Resource arguments are erased: authority has no runtime
            // representation, so only the pointer and value lower.
            ExprKind::RawOp { op, args, .. } => {
                let result = validate_raw_op(ctx, *op, args)?;
                if e.ty != Some(result.clone()) {
                    return Err(format!(
                        "svm.raw_result_type: `{}` produces `{}` but is annotated `{}`",
                        op.name(),
                        result.name(),
                        e.ty.clone()
                            .map_or_else(|| "<missing>".into(), |arg0: ast::Ty| Ty::name(&arg0))
                    ));
                }
                Some(match op {
                    RawOp::Store8 => format!(
                        "(.rawStore8 {} {})",
                        lower_expr(ctx, &args[0])?,
                        lower_expr(ctx, &args[1])?
                    ),
                    RawOp::CellInitU64 => format!(
                        "(.rawCellInitU64 {} {})",
                        lower_expr(ctx, &args[0])?,
                        lower_expr(ctx, &args[1])?
                    ),
                    RawOp::CellDropU64 => {
                        format!("(.rawCellDropU64 {})", lower_expr(ctx, &args[0])?)
                    }
                    RawOp::CellInitRecord(ri) => {
                        ctx.record(*ri)?;
                        format!(
                            "(.rawCellInitRecord {ri} {} {})",
                            lower_expr(ctx, &args[0])?,
                            lower_expr(ctx, &args[1])?
                        )
                    }
                    RawOp::CellDropRecord(ri) => {
                        ctx.record(*ri)?;
                        format!("(.rawCellDropRecord {ri} {})", lower_expr(ctx, &args[0])?)
                    }
                    RawOp::HeaderInit => {
                        let p = lower_expr(ctx, &args[0])?;
                        let next_p = format!("(.ptrAdd {p} (.intLit .u64 8))");
                        format!(
                            "(.rawCellInitU64 {p} {}), (.rawCellInitU64 {next_p} {})",
                            lower_expr(ctx, &args[1])?,
                            lower_expr(ctx, &args[2])?
                        )
                    }
                    RawOp::HeaderClear => {
                        let p = lower_expr(ctx, &args[0])?;
                        let next_p = format!("(.ptrAdd {p} (.intLit .u64 8))");
                        format!("(.rawCellDropU64 {p}), (.rawCellDropU64 {next_p})")
                    }
                    RawOp::Copy => {
                        return Err("`raw_copy_nonoverlapping` has no single machine step: \
                                the machine copies a byte at a time, and lowering it \
                                would invent a loop the source did not write"
                            .into());
                    }
                    _ => return Err(format!("`{}` produces a value", op.name())),
                })
            }
            ExprKind::DeviceOp { op, args, .. } => {
                let result = validate_device_op(ctx, *op, args)?;
                if e.ty != Some(result.clone()) {
                    return Err(format!(
                        "svm.device_result_type: `{}` produces `{}` but is annotated `{}`",
                        op.name(),
                        result.name(),
                        e.ty.clone()
                            .map_or_else(|| "<missing>".into(), |arg0: ast::Ty| Ty::name(&arg0))
                    ));
                }
                Some(match op {
                    DeviceOp::UartWrite => {
                        format!("(.uartWrite {})", lower_expr(ctx, &args[0])?)
                    }
                    DeviceOp::UartStatus => {
                        return Err("`uart_status` produces a value".into());
                    }
                })
            }
            ExprKind::Call { .. } => Some(lower_call(ctx, &None, e)?),
            ExprKind::ResOp { op, args, .. } => {
                semantic_expr_ty(
                    ctx,
                    e,
                    e.ty.clone().unwrap_or(Ty::Unit),
                    "sealed resource expression statement",
                )?;
                lower_resource_op_stmt(ctx, *op, args)?
            }
            ExprKind::OptTake { option, .. } => {
                return Err(affine_option_take_position(option));
            }
            _ => {
                return Err("expression statements are outside the SVM core subset".into());
            }
        },
        Stmt::Assert(_) => {
            return Err("`/// assert` is outside the SVM core subset".into());
        }
        Stmt::FieldAssign { .. } | Stmt::FieldStore { .. } => {
            return Err("class members are outside the SVM core subset".into());
        }
    })
}

/// Lower the runtime part of a resource-producing expression. Most sealed
/// resource operations only redistribute static authority and therefore have
/// no machine step. The exceptions below have interpreter-visible state: a
/// differential subject must either use the matching profile statement or be
/// rejected until the SVM models that state too.
fn lower_resource_op_stmt(
    ctx: &LowerCtx<'_>,
    op: ResOp,
    args: &[Expr],
) -> Result<Option<String>, String> {
    match op {
        ResOp::TestUart => Ok(Some(format!("(.testUartProfile {})", {
            validate_sealed_resource_operands(ctx, op, args)?;
            lower_expr(ctx, &args[0])?
        }))),
        ResOp::TestWorld
        | ResOp::OpenFileOf
        | ResOp::ResourceMapEmpty
        | ResOp::ResourceMapTake
        | ResOp::ResourceMapPut => Err(format!(
            "`{}` has interpreter-visible runtime state but no SVM statement",
            op.name()
        )),
        _ => {
            ensure_erased_resource_operands_inert(ctx, op, args)?;
            Ok(None)
        }
    }
}

fn resolved_resource_place_ty(
    ctx: &LowerCtx<'_>,
    expr: &Expr,
    operation: &str,
) -> Result<Ty, String> {
    let actual = match &expr.kind {
        ExprKind::Var(name) => {
            let binding = ctx.initialized_local(name, operation)?;
            if !binding.ty.clone().is_resource() {
                return Err(format!(
                    "svm.resource_operand_type: {operation} names `{name}` of non-resource type `{}`",
                    binding.ty.name()
                ));
            }
            binding.ty
        }
        ExprKind::Borrow {
            array,
            field: None,
            mutable,
        } => {
            let binding = ctx.initialized_local(array, operation)?;
            let requested = if *mutable {
                Mutability::Mut
            } else {
                Mutability::Shared
            };
            let kind = match binding.ty {
                Ty::Res(kind) => {
                    if *mutable && !binding.mutable {
                        return Err(format!(
                            "svm.resource_operand_type: {operation} mutably borrows immutable resource local `{array}`"
                        ));
                    }
                    kind
                }
                ref borrowed if borrowed.as_res_borrow().is_some() => {
                    let (kind, source_mutability) = borrowed
                        .as_res_borrow()
                        .expect("the arm's guard already matched this shape");
                    if *mutable && source_mutability != Mutability::Mut {
                        return Err(format!(
                            "svm.resource_operand_type: {operation} mutably reborrows shared resource local `{array}`"
                        ));
                    }
                    kind
                }
                actual => {
                    return Err(format!(
                        "svm.resource_operand_type: {operation} borrows `{array}` of non-resource type `{}`",
                        actual.name()
                    ));
                }
            };
            Ty::borrow(requested, Ty::Res(kind))
        }
        ExprKind::Borrow { field: Some(_), .. } | ExprKind::SelfField { .. } => {
            return Err(format!(
                "svm.resource_operand_place: {operation} uses a resource field; class members are outside the SVM local environment"
            ));
        }
        ExprKind::OptTake { option, .. } => {
            return Err(affine_option_take_position(option));
        }
        _ => {
            return Err(format!(
                "svm.resource_operand_place: {operation} requires a local resource variable or local resource borrow"
            ));
        }
    };
    if let Some(annotation) = &expr.ty {
        if *annotation != actual {
            return Err(format!(
                "svm.resource_operand_type: {operation} is semantically `{}` but annotated `{}`",
                actual.name(),
                annotation.name()
            ));
        }
    }
    Ok(actual)
}

fn sealed_resource_operand_types(
    ctx: &LowerCtx<'_>,
    op: ResOp,
    args: &[Expr],
) -> Result<Vec<Ty>, String> {
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
        return Err(format!(
            "svm.resource_operand_arity: `{}` expects {arity} operands, found {}",
            op.name(),
            args.len()
        ));
    }

    let mutable_ref = |kind| Ty::borrow(Mutability::Mut, Ty::Res(kind));
    let owned = Ty::Res;
    let u64_ty = Ty::Int(IntTy::U64);
    let result = match op {
        ResOp::SplitOff => vec![mutable_ref(ResKind::RawSpan), u64_ty],
        ResOp::Join => vec![owned(ResKind::RawSpan), owned(ResKind::RawSpan)],
        ResOp::OpenFileOf => vec![mutable_ref(ResKind::PosixWorld), Ty::Int(IntTy::I32)],
        ResOp::TestWorld | ResOp::TestUart => vec![u64_ty],
        ResOp::AllocatorCreate => vec![owned(ResKind::RawSpan)],
        ResOp::AllocatorDestroy => vec![owned(ResKind::AllocatorState)],
        ResOp::AllocatorTake | ResOp::AllocatorTakeFree | ResOp::AllocatorTakeHeader => {
            vec![mutable_ref(ResKind::AllocatorState), u64_ty]
        }
        ResOp::AllocatorStepHeader => {
            vec![mutable_ref(ResKind::AllocatorState), u64_ty.clone(), u64_ty]
        }
        ResOp::AllocatorPut => vec![
            mutable_ref(ResKind::AllocatorState),
            owned(ResKind::BlockLease),
        ],
        ResOp::AllocatorPutFree => vec![
            mutable_ref(ResKind::AllocatorState),
            owned(ResKind::FreeBlock),
        ],
        ResOp::AllocatorPutHeader => vec![
            mutable_ref(ResKind::AllocatorState),
            owned(ResKind::FreeHeader),
        ],
        ResOp::FreeBlockSplit => vec![mutable_ref(ResKind::FreeBlock), u64_ty],
        ResOp::FreeBlockJoin => vec![owned(ResKind::FreeBlock), owned(ResKind::FreeBlock)],
        ResOp::FreeBlockLease => vec![owned(ResKind::FreeBlock)],
        ResOp::BlockLeaseFree => vec![owned(ResKind::BlockLease)],
        ResOp::ResourceMapEmpty => Vec::new(),
        ResOp::ResourceMapTake | ResOp::ResourceMapPut => {
            let map_ty =
                resolved_resource_place_ty(ctx, &args[0], &format!("`{}` operand 1", op.name()))?;
            let Some((
                map_kind
                @ (ResKind::ResourceMapPointsToU64 | ResKind::ResourceMapPointsToRecord(_)),
                Mutability::Mut,
            )) = map_ty.as_res_borrow()
            else {
                return Err(format!(
                    "svm.resource_operand_type: `{}` operand 1 must be a mutable supported resource-map borrow",
                    op.name()
                ));
            };
            if op == ResOp::ResourceMapTake {
                vec![map_ty, u64_ty]
            } else {
                let cell = match map_kind {
                    ResKind::ResourceMapPointsToU64 => ResKind::PointsToU64,
                    ResKind::ResourceMapPointsToRecord(record) => ResKind::PointsToRecord(record),
                    _ => unreachable!(),
                };
                vec![map_ty, u64_ty, owned(cell)]
            }
        }
    };
    Ok(result)
}

fn validate_sealed_resource_operands(
    ctx: &LowerCtx<'_>,
    op: ResOp,
    args: &[Expr],
) -> Result<(), String> {
    let expected = sealed_resource_operand_types(ctx, op, args)?;
    for (index, (arg, expected)) in args.iter().zip(expected).enumerate() {
        let context = format!("`{}` operand {}", op.name(), index + 1);
        if expected.clone().is_resource() {
            let actual = resolved_resource_place_ty(ctx, arg, &context)?;
            if actual != expected {
                return Err(format!(
                    "svm.resource_operand_type: {context} supplies `{}`; expected `{}`",
                    actual.name(),
                    expected.name()
                ));
            }
        } else {
            validate_sink_type(ctx, expected, arg, &context)?;
        }
    }
    Ok(())
}

fn semantic_res_op_ty(
    ctx: &LowerCtx<'_>,
    op: ResOp,
    args: &[Expr],
    expected: Ty,
) -> Result<Ty, String> {
    validate_sealed_resource_operands(ctx, op, args)?;
    Ok(match op {
        ResOp::SplitOff | ResOp::Join | ResOp::AllocatorDestroy => Ty::Res(ResKind::RawSpan),
        ResOp::OpenFileOf => Ty::Res(ResKind::OpenFile),
        ResOp::TestWorld => Ty::Res(ResKind::PosixWorld),
        ResOp::TestUart => Ty::Res(ResKind::Uart),
        ResOp::AllocatorCreate => Ty::Res(ResKind::AllocatorState),
        ResOp::AllocatorTake | ResOp::FreeBlockLease => Ty::Res(ResKind::BlockLease),
        ResOp::AllocatorPut | ResOp::AllocatorPutFree | ResOp::AllocatorPutHeader => Ty::Unit,
        ResOp::AllocatorTakeFree | ResOp::FreeBlockSplit | ResOp::FreeBlockJoin => {
            Ty::Res(ResKind::FreeBlock)
        }
        ResOp::AllocatorTakeHeader | ResOp::AllocatorStepHeader => Ty::Res(ResKind::FreeHeader),
        ResOp::BlockLeaseFree => Ty::Res(ResKind::FreeBlock),
        ResOp::ResourceMapEmpty => match expected {
            Ty::Res(kind @ ResKind::ResourceMapPointsToU64)
            | Ty::Res(kind @ ResKind::ResourceMapPointsToRecord(_)) => Ty::Res(kind),
            _ => Ty::Res(ResKind::ResourceMapPointsToU64),
        },
        ResOp::ResourceMapTake => {
            let map = resolved_resource_place_ty(ctx, &args[0], "resource_map_take operand 1")?;
            match map.as_res_borrow() {
                Some((ResKind::ResourceMapPointsToU64, Mutability::Mut)) => {
                    Ty::Res(ResKind::PointsToU64)
                }
                Some((ResKind::ResourceMapPointsToRecord(record), Mutability::Mut)) => {
                    Ty::Res(ResKind::PointsToRecord(record))
                }
                _ => unreachable!("sealed resource operand validation checked map kind"),
            }
        }
        ResOp::ResourceMapPut => Ty::Unit,
    })
}

fn validate_typed_operand(
    ctx: &LowerCtx<'_>,
    value: &Expr,
    expected: Ty,
    context: &str,
) -> Result<(), String> {
    if expected.clone().is_resource() {
        let actual = resolved_resource_place_ty(ctx, value, context)?;
        if actual != expected {
            return Err(format!(
                "svm.resource_operand_type: {context} supplies `{}`; expected `{}`",
                actual.name(),
                expected.name()
            ));
        }
        Ok(())
    } else {
        validate_sink_type(ctx, expected, value, context)
    }
}

fn raw_op_signature(ctx: &LowerCtx<'_>, op: RawOp, args: &[Expr]) -> Result<(Vec<Ty>, Ty), String> {
    if args.len() != op.arity() {
        return Err(format!(
            "svm.raw_operand_arity: `{}` expects {} operands, found {}",
            op.name(),
            op.arity(),
            args.len()
        ));
    }
    let raw = Ty::Raw(IntTy::U8);
    let u8_ty = Ty::Int(IntTy::U8);
    let u64_ty = Ty::Int(IntTy::U64);
    let shared = |kind| Ty::borrow(Mutability::Shared, Ty::Res(kind));
    let mutable = |kind| Ty::borrow(Mutability::Mut, Ty::Res(kind));
    let owned = Ty::Res;
    let resource_kind = |index: usize| -> Option<ResKind> {
        resolved_resource_place_ty(
            ctx,
            &args[index],
            &format!("`{}` operand {}", op.name(), index + 1),
        )
        .ok()
        .and_then(|ty| ty.res_kind())
    };
    let leased = match op {
        RawOp::IntoCellU64 | RawOp::FromCellU64 => resource_kind(1),
        RawOp::CellInitU64 => resource_kind(2),
        RawOp::CellReadU64 | RawOp::CellTakeU64 | RawOp::CellDropU64 => resource_kind(1),
        _ => None,
    }
    .is_some_and(|kind| matches!(kind, ResKind::BlockLease | ResKind::LeasedPointsToU64));

    let signature = match op {
        RawOp::Offset => (vec![raw.clone(), u64_ty], raw),
        RawOp::Load8 => (vec![raw, shared(ResKind::RawSpan)], u8_ty),
        RawOp::Store8 => (vec![raw, u8_ty, mutable(ResKind::RawSpan)], Ty::Unit),
        RawOp::Copy => (
            vec![
                raw.clone(),
                raw,
                u64_ty,
                shared(ResKind::RawSpan),
                mutable(ResKind::RawSpan),
            ],
            Ty::Unit,
        ),
        RawOp::IntoCellU64 => (
            vec![
                raw,
                owned(if leased {
                    ResKind::BlockLease
                } else {
                    ResKind::RawSpan
                }),
            ],
            owned(if leased {
                ResKind::LeasedPointsToU64
            } else {
                ResKind::PointsToU64
            }),
        ),
        RawOp::FromCellU64 => (
            vec![
                raw,
                owned(if leased {
                    ResKind::LeasedPointsToU64
                } else {
                    ResKind::PointsToU64
                }),
            ],
            owned(if leased {
                ResKind::BlockLease
            } else {
                ResKind::RawSpan
            }),
        ),
        RawOp::CellInitU64 => (
            vec![
                raw,
                u64_ty,
                mutable(if leased {
                    ResKind::LeasedPointsToU64
                } else {
                    ResKind::PointsToU64
                }),
            ],
            Ty::Unit,
        ),
        RawOp::CellReadU64 => (
            vec![
                raw,
                shared(if leased {
                    ResKind::LeasedPointsToU64
                } else {
                    ResKind::PointsToU64
                }),
            ],
            u64_ty,
        ),
        RawOp::CellTakeU64 => (
            vec![
                raw,
                mutable(if leased {
                    ResKind::LeasedPointsToU64
                } else {
                    ResKind::PointsToU64
                }),
            ],
            u64_ty,
        ),
        RawOp::CellDropU64 => (
            vec![
                raw,
                mutable(if leased {
                    ResKind::LeasedPointsToU64
                } else {
                    ResKind::PointsToU64
                }),
            ],
            Ty::Unit,
        ),
        RawOp::IntoCellRecord(record) => (
            vec![Ty::RawRecord(record), owned(ResKind::RawSpan)],
            owned(ResKind::PointsToRecord(record)),
        ),
        RawOp::FromCellRecord(record) => (
            vec![
                Ty::RawRecord(record),
                owned(ResKind::PointsToRecord(record)),
            ],
            owned(ResKind::RawSpan),
        ),
        RawOp::CellInitRecord(record) => (
            vec![
                Ty::RawRecord(record),
                Ty::Record(record),
                mutable(ResKind::PointsToRecord(record)),
            ],
            Ty::Unit,
        ),
        RawOp::CellReadRecord(record) => (
            vec![
                Ty::RawRecord(record),
                shared(ResKind::PointsToRecord(record)),
            ],
            Ty::Record(record),
        ),
        RawOp::CellTakeRecord(record) => (
            vec![
                Ty::RawRecord(record),
                mutable(ResKind::PointsToRecord(record)),
            ],
            Ty::Record(record),
        ),
        RawOp::CellDropRecord(record) => (
            vec![
                Ty::RawRecord(record),
                mutable(ResKind::PointsToRecord(record)),
            ],
            Ty::Unit,
        ),
        RawOp::CastRecord(record) => (vec![raw], Ty::RawRecord(record)),
        RawOp::PointerOffsetRecord(record) => (vec![Ty::RawRecord(record)], u64_ty),
        RawOp::IntoFreeHeader => (
            vec![raw, owned(ResKind::FreeBlock)],
            owned(ResKind::FreeHeader),
        ),
        RawOp::FromFreeHeader => (
            vec![raw, owned(ResKind::FreeHeader)],
            owned(ResKind::FreeBlock),
        ),
        RawOp::HeaderInit => (
            vec![raw, u64_ty.clone(), u64_ty, mutable(ResKind::FreeHeader)],
            Ty::Unit,
        ),
        RawOp::HeaderSize | RawOp::HeaderNext => (vec![raw, shared(ResKind::FreeHeader)], u64_ty),
        RawOp::HeaderClear => (vec![raw, mutable(ResKind::FreeHeader)], Ty::Unit),
    };
    Ok(signature)
}

fn validate_raw_op(ctx: &LowerCtx<'_>, op: RawOp, args: &[Expr]) -> Result<Ty, String> {
    let (expected, result) = raw_op_signature(ctx, op, args)?;
    for (index, (value, expected)) in args.iter().zip(expected).enumerate() {
        validate_typed_operand(
            ctx,
            value,
            expected,
            &format!("`{}` operand {}", op.name(), index + 1),
        )?;
    }
    Ok(result)
}

fn validate_device_op(ctx: &LowerCtx<'_>, op: DeviceOp, args: &[Expr]) -> Result<Ty, String> {
    let (expected, result) = match op {
        DeviceOp::UartStatus => (
            vec![Ty::borrow(Mutability::Mut, Ty::Res(ResKind::Uart))],
            Ty::Int(IntTy::U8),
        ),
        DeviceOp::UartWrite => (
            vec![
                Ty::Int(IntTy::U8),
                Ty::borrow(Mutability::Mut, Ty::Res(ResKind::Uart)),
            ],
            Ty::Unit,
        ),
    };
    if args.len() != expected.len() {
        return Err(format!(
            "svm.device_operand_arity: `{}` expects {} operands, found {}",
            op.name(),
            expected.len(),
            args.len()
        ));
    }
    for (index, (value, expected)) in args.iter().zip(expected).enumerate() {
        validate_typed_operand(
            ctx,
            value,
            expected,
            &format!("`{}` operand {}", op.name(), index + 1),
        )?;
    }
    Ok(result)
}

/// An authority-only operation has no SVM statement, but source operands are
/// still evaluated before its erased result is produced. Erase the operation
/// only when each operand is syntactically known to have no runtime effect and
/// no trap. Anything richer must either gain an explicit discard/effect
/// lowering or remain outside the differential subset; silently dropping it
/// would make the harness compare a different program.
fn ensure_erased_resource_operands_inert(
    ctx: &LowerCtx<'_>,
    op: ResOp,
    args: &[Expr],
) -> Result<(), String> {
    let expected = sealed_resource_operand_types(ctx, op, args)?;
    for (index, arg) in args.iter().enumerate() {
        let expected = expected[index].clone();
        let inert = match &arg.kind {
            // Checked literals are in range and cannot trap.
            ExprKind::IntLit(_) | ExprKind::BoolLit(_) => true,
            // A scalar local read and a checked local resource place are both
            // side-effect-free. Resource variables deliberately may lack a
            // cached annotation, so resolve them through the active context.
            ExprKind::Var(_) if expected.clone().is_resource() => {
                resolved_resource_place_ty(
                    ctx,
                    arg,
                    &format!("`{}` operand {}", op.name(), index + 1),
                )? == expected
            }
            ExprKind::Var(_) => true,
            ExprKind::Borrow { .. } if expected.clone().is_resource() => {
                resolved_resource_place_ty(
                    ctx,
                    arg,
                    &format!("`{}` operand {}", op.name(), index + 1),
                )? == expected
            }
            ExprKind::OptTake { option, .. } => {
                return Err(affine_option_take_position(option));
            }
            // Calls, arithmetic (including division), raw/device operations,
            // and nested resource transformations may trap or mutate runtime
            // state. Reject them instead of trying to infer purity here.
            _ => false,
        };
        if !inert {
            return Err(format!(
                "`{}` operand {} is not provably runtime-inert; the SVM lowerer \
                 will not erase its evaluation",
                op.name(),
                index + 1
            ));
        }
    }
    validate_sealed_resource_operands(ctx, op, args)
}

/// Resource locals themselves are erased, but evaluating their initializer or
/// assignment may still perform a machine transition. Pure moves and sealed
/// authority-only transformations disappear; raw role changes, calls, and the
/// UART profile selector keep their runtime effect.
fn lower_erased_resource_bind(
    ctx: &LowerCtx<'_>,
    name: &str,
    e: &Expr,
) -> Result<Option<String>, String> {
    match &e.kind {
        ExprKind::Var(_) => Ok(None),
        ExprKind::ResOp { op, args, .. } => lower_resource_op_stmt(ctx, *op, args),
        ExprKind::RawOp { .. } => Ok(Some(lower_bind(ctx, name, e)?)),
        ExprKind::Call { .. } => Ok(Some(lower_call(ctx, &None, e)?)),
        ExprKind::OptTake { option, .. } => Err(affine_option_take_position(option)),
        _ => Err("resource-valued expression is outside the SVM core subset".into()),
    }
}

/// Materialize the exact local affine-option construction surface. The Lean
/// value representation deliberately remains the recursive `.opt`, but the
/// Rust bridge admits only a freshly allocated Boolean array as its payload.
fn lower_affine_bool_option_bind(
    ctx: &LowerCtx<'_>,
    name: &str,
    declared_ty: Ty,
    mutable: bool,
    initializer: Option<&Expr>,
) -> Result<String, String> {
    validate_affine_bool_option_decl(ctx, name, declared_ty, mutable, initializer)?;
    let initializer = initializer.expect("validated affine option initializer");
    match &initializer.kind {
        ExprKind::NoneE => Ok(format!("(.assign \"{name}\" (.noneE))")),
        ExprKind::SomeE(payload) => {
            let ExprKind::AllocArray { len, init, .. } = &payload.kind else {
                unreachable!("validated affine-option payload")
            };
            Ok(format!(
                "(.assign \"{name}\" (.someE (.allocArray {} {})))",
                lower_expr(ctx, len)?,
                lower_expr(ctx, init)?
            ))
        }
        _ => unreachable!("validated affine-option initializer"),
    }
}

/// Materialize the one Boolean-array producer position admitted by the SVM
/// bridge. A literal first evaluates its elements into compiler-reserved
/// temporaries in source order, then expands to a false-filled allocation and
/// ordered stores. Evaluating the elements before the allocation is material:
/// an element trap must beat construction, just as it does in `interp.rs`.
/// Empty literals still get an unambiguous Boolean payload without adding a
/// second array-literal expression to the Lean core.
fn lower_fresh_bool_array_bind(
    ctx: &LowerCtx<'_>,
    name: &str,
    declared_ty: Ty,
    initializer: &Expr,
) -> Result<String, String> {
    validate_fresh_bool_array_initializer(ctx, declared_ty, initializer, name)?;
    match &initializer.kind {
        ExprKind::AllocArray { len, init, .. } => Ok(format!(
            "(.assign \"{name}\" (.allocArray {} {}))",
            lower_expr(ctx, len)?,
            lower_expr(ctx, init)?
        )),
        ExprKind::ArrayLit(elements) => {
            let temporaries: Result<Vec<(String, String)>, String> = elements
                .iter()
                .enumerate()
                .map(|(index, value)| {
                    // Source identifiers beginning with `_` are reserved by
                    // the lexer, and checked local names are function-unique.
                    // The explicit lookup keeps the public lowerer fail-closed
                    // if a forged checked AST bypasses those front-end rules.
                    let temporary = format!("_bool_lit_{name}_{index}");
                    if ctx.local(&temporary).is_some() {
                        return Err(format!(
                            "svm.bool_array_temp_collision: compiler Boolean-literal temporary `{temporary}` collides with a forged checked local"
                        ));
                    }
                    Ok((temporary, lower_expr(ctx, value)?))
                })
                .collect();
            let temporaries = temporaries?;
            let mut statements: Vec<String> = temporaries
                .iter()
                .map(|(temporary, value)| format!("(.assign \"{temporary}\" {value})"))
                .collect();
            statements.push(format!(
                "(.assign \"{name}\" (.allocArray (.intLit .u64 {}) (.boolLit false)))",
                elements.len()
            ));
            for (index, (temporary, _)) in temporaries.iter().enumerate() {
                statements.push(format!(
                    "(.store \"{name}\" (.intLit .u64 {index}) (.var \"{temporary}\"))"
                ));
            }
            Ok(statements.join(", "))
        }
        ExprKind::OptTake { option, .. } => {
            validate_affine_option_take(ctx, name, initializer, option)?;
            Ok(format!("(.optTake \"{name}\" \"{option}\")"))
        }
        _ => unreachable!("fresh Boolean array validation accepted a transport"),
    }
}

/// `x = e;` — an assign, or (A-normalized, ADR 0005) a call when `e`
/// is exactly a call; calls nested deeper stay outside the subset.
fn lower_bind(ctx: &LowerCtx<'_>, name: &str, e: &Expr) -> Result<String, String> {
    match &e.kind {
        ExprKind::OptTake { option, .. } => Err(affine_option_take_position(option)),
        ExprKind::Call { .. } => lower_call(ctx, &Some(name.to_string()), e),
        ExprKind::DeviceOp {
            op: DeviceOp::UartStatus,
            args,
            ..
        } => {
            let result = validate_device_op(ctx, DeviceOp::UartStatus, args)?;
            if e.ty != Some(result) {
                return Err("svm.device_result_type: forged `uart_status` result type".into());
            }
            Ok(format!("(.uartStatus \"{name}\")"))
        }
        ExprKind::DeviceOp {
            op: DeviceOp::UartWrite,
            ..
        } => Err("`uart_write` produces no value".into()),
        ExprKind::RecordLit { record, args, .. } => {
            let ri = validate_record_literal(ctx, e, record, args)?;
            let decl = ctx.record(ri)?;
            let fields = decl
                .fields
                .iter()
                .map(|field| format!("\"{}\"", field.name))
                .collect::<Vec<_>>()
                .join(", ");
            let values: Result<Vec<String>, String> =
                args.iter().map(|arg| lower_expr(ctx, arg)).collect();
            Ok(format!(
                "(.recordMake \"{name}\" {ri} [{fields}] [{}])",
                values?.join(", ")
            ))
        }
        // A load is a machine statement that binds its destination.
        ExprKind::RawOp {
            op: RawOp::Load8,
            args,
            ..
        } => {
            let result = validate_raw_op(ctx, RawOp::Load8, args)?;
            if e.ty != Some(result) {
                return Err("svm.raw_result_type: forged `raw_load8` result type".into());
            }
            Ok(format!(
                "(.rawLoad8 \"{name}\" {})",
                lower_expr(ctx, &args[0])?
            ))
        }
        ExprKind::RawOp { op, args, .. } => {
            let result = validate_raw_op(ctx, *op, args)?;
            if e.ty != Some(result.clone()) {
                return Err(format!(
                    "svm.raw_result_type: `{}` produces `{}` but is annotated `{}`",
                    op.name(),
                    result.name(),
                    e.ty.clone()
                        .map_or_else(|| "<missing>".into(), |arg0: ast::Ty| Ty::name(&arg0))
                ));
            }
            match op {
                // Resource destinations are erased; the role-changing machine
                // instruction is nevertheless observable in the heap.
                RawOp::IntoCellU64 => {
                    Ok(format!("(.rawIntoCellU64 {})", lower_expr(ctx, &args[0])?))
                }
                RawOp::FromCellU64 => {
                    Ok(format!("(.rawFromCellU64 {})", lower_expr(ctx, &args[0])?))
                }
                RawOp::IntoCellRecord(ri) => {
                    let decl = ctx.record(*ri)?;
                    Ok(format!(
                        "(.rawIntoCellRecord {ri} {} {} {})",
                        decl.layout.size,
                        decl.layout.align,
                        lower_expr(ctx, &args[0])?
                    ))
                }
                RawOp::FromCellRecord(ri) => {
                    // Resolve the index even though this instruction needs no
                    // geometry, so malformed checked ASTs still fail strictly.
                    ctx.record(*ri)?;
                    Ok(format!(
                        "(.rawFromCellRecord {ri} {})",
                        lower_expr(ctx, &args[0])?
                    ))
                }
                RawOp::IntoFreeHeader => {
                    let p = lower_expr(ctx, &args[0])?;
                    let next_p = format!("(.ptrAdd {p} (.intLit .u64 8))");
                    Ok(format!("(.rawIntoCellU64 {p}), (.rawIntoCellU64 {next_p})"))
                }
                RawOp::FromFreeHeader => {
                    let p = lower_expr(ctx, &args[0])?;
                    let next_p = format!("(.ptrAdd {p} (.intLit .u64 8))");
                    Ok(format!("(.rawFromCellU64 {p}), (.rawFromCellU64 {next_p})"))
                }
                RawOp::CellReadU64 => Ok(format!(
                    "(.rawCellReadU64 \"{name}\" {})",
                    lower_expr(ctx, &args[0])?
                )),
                RawOp::CellTakeU64 => Ok(format!(
                    "(.rawCellTakeU64 \"{name}\" {})",
                    lower_expr(ctx, &args[0])?
                )),
                RawOp::CellReadRecord(ri) => {
                    ctx.record(*ri)?;
                    Ok(format!(
                        "(.rawCellReadRecord {ri} \"{name}\" {})",
                        lower_expr(ctx, &args[0])?
                    ))
                }
                RawOp::CellTakeRecord(ri) => {
                    ctx.record(*ri)?;
                    Ok(format!(
                        "(.rawCellTakeRecord {ri} \"{name}\" {})",
                        lower_expr(ctx, &args[0])?
                    ))
                }
                RawOp::HeaderSize => Ok(format!(
                    "(.rawCellReadU64 \"{name}\" {})",
                    lower_expr(ctx, &args[0])?
                )),
                RawOp::HeaderNext => {
                    let p = lower_expr(ctx, &args[0])?;
                    Ok(format!(
                        "(.rawCellReadU64 \"{name}\" (.ptrAdd {p} (.intLit .u64 8)))"
                    ))
                }
                _ => Ok(format!("(.assign \"{name}\" {})", lower_expr(ctx, e)?)),
            }
        }
        _ => Ok(format!("(.assign \"{name}\" {})", lower_expr(ctx, e)?)),
    }
}

fn lower_call(ctx: &LowerCtx<'_>, dst: &Option<String>, call: &Expr) -> Result<String, String> {
    let ExprKind::Call { callee, args, .. } = &call.kind else {
        unreachable!("lower_call requires an ordinary call expression")
    };
    validate_call_signature(ctx, call, callee, args)?;
    let lowered: Result<Vec<String>, String> = args.iter().map(|arg| lower_arg(ctx, arg)).collect();
    let d = match dst {
        Some(x) => format!("(some \"{x}\")"),
        None => "none".into(),
    };
    Ok(format!(
        "(.call {d} \"{callee}\" [{}])",
        lowered?.join(", ")
    ))
}

/// Lower one call argument.
///
/// A unique array borrow becomes `Arg.lend`: the machine binds the caller's
/// sequence on entry and returns the callee's exit value to that same local
/// when the frame pops, which is what makes a `&mut` store visible to the
/// caller. Every other argument is `Arg.byValue` — a shared borrow included,
/// because its whole promise is that the callee does not write, and a value
/// is exactly that promise. Lending needs a name to return to, so a unique
/// borrow of anything but a local fails closed.
fn lower_arg(ctx: &LowerCtx<'_>, arg: &Expr) -> Result<String, String> {
    let Some((_, mutability)) = arg.ty.as_ref().and_then(Ty::as_array_borrow) else {
        return Ok(format!("(.byValue {})", lower_expr(ctx, arg)?));
    };
    let source = match &arg.kind {
        ExprKind::Borrow {
            array,
            field: None,
            mutable: _,
        } => array,
        ExprKind::Var(name) => name,
        _ => {
            return Err(format!(
                "svm.array_borrow_place: an array borrow argument must name a local; `{}` does not",
                arg.ty.as_ref().map_or_else(|| "<untyped>".into(), Ty::name)
            ));
        }
    };
    validate_expr_payloads(ctx, arg)?;
    ctx.initialized_local(source, "array borrow argument")?;
    Ok(match mutability {
        Mutability::Mut => format!("(.lend \"{source}\")"),
        Mutability::Shared => format!("(.byValue (.var \"{source}\"))"),
    })
}

fn lower_expr(ctx: &LowerCtx<'_>, e: &Expr) -> Result<String, String> {
    validate_expr_payloads(ctx, e)?;
    Ok(match &e.kind {
        ExprKind::IntLit(n) => {
            format!("(.intLit {} {})", lean_ty(expr_int_ty(e)?)?, int_lit(*n))
        }
        ExprKind::BoolLit(b) => format!("(.boolLit {b})"),
        ExprKind::Var(x) => {
            validate_local_var(ctx, e, x, "variable expression")?;
            format!("(.var \"{x}\")")
        }
        ExprKind::DeviceOp { op, args, .. } => {
            let result = validate_device_op(ctx, *op, args)?;
            if e.ty != Some(result.clone()) {
                return Err(format!(
                    "svm.device_result_type: `{}` produces `{}` but is annotated `{}`",
                    op.name(),
                    result.name(),
                    e.ty.clone()
                        .map_or_else(|| "<missing>".into(), |arg0: ast::Ty| Ty::name(&arg0))
                ));
            }
            return Err(format!(
                "`{}` is a statement in the profile machine, not an expression",
                op.name()
            ));
        }
        ExprKind::ResOp { op, .. } => {
            // Resource transformations are static: they redistribute
            // authority and there is nothing for the machine to do. A
            // differential subject containing one is a subject about
            // nothing, so it is an error rather than a silent erasure.
            return Err(format!(
                "`{}` is static: there is no machine step to compare",
                op.name()
            ));
        }
        ExprKind::RawOp { op, args, .. } => {
            let result = validate_raw_op(ctx, *op, args)?;
            if e.ty != Some(result.clone()) {
                return Err(format!(
                    "svm.raw_result_type: `{}` produces `{}` but is annotated `{}`",
                    op.name(),
                    result.name(),
                    e.ty.clone()
                        .map_or_else(|| "<missing>".into(), |arg0: ast::Ty| Ty::name(&arg0))
                ));
            }
            let lowered: Result<Vec<String>, String> =
                args.iter().map(|arg| lower_expr(ctx, arg)).collect();
            let lowered = lowered?;
            match op {
                RawOp::Offset => format!("(.ptrAdd {} {})", lowered[0], lowered[1]),
                RawOp::CastRecord(ri) => {
                    ctx.record(*ri)?;
                    lowered[0].clone()
                }
                RawOp::PointerOffsetRecord(ri) => {
                    ctx.record(*ri)?;
                    format!("(.ptrOffset {})", lowered[0])
                }
                // The rest are statements in the machine (§ADR 0025), so
                // they cannot appear in expression position here; the
                // statement lowering handles them.
                _ => {
                    return Err(format!(
                        "`{}` is a statement in the machine, not an expression",
                        op.name()
                    ));
                }
            }
        }
        ExprKind::Unary { op, operand } => match op {
            UnOp::Not => format!("(.not {})", lower_expr(ctx, operand)?),
            UnOp::Neg => format!(
                "(.neg {} {})",
                lean_ty(expr_int_ty(e)?)?,
                lower_expr(ctx, operand)?
            ),
        },
        ExprKind::Binary { op, lhs, rhs, .. } => {
            let l = lower_expr(ctx, lhs)?;
            let r = lower_expr(ctx, rhs)?;
            match op {
                BinOp::And => format!("(.and {l} {r})"),
                BinOp::Or => format!("(.or {l} {r})"),
                BinOp::Lt => format!("(.cmp .lt {l} {r})"),
                BinOp::Le => format!("(.cmp .le {l} {r})"),
                BinOp::Gt => format!("(.cmp .gt {l} {r})"),
                BinOp::Ge => format!("(.cmp .ge {l} {r})"),
                BinOp::Eq => format!("(.cmp .eq {l} {r})"),
                BinOp::Ne => format!("(.cmp .ne {l} {r})"),
                BinOp::Add | BinOp::Sub | BinOp::Mul => {
                    let sym = match op {
                        BinOp::Add => ".add",
                        BinOp::Sub => ".sub",
                        _ => ".mul",
                    };
                    format!("(.arith {sym} {} {l} {r})", lean_ty(expr_int_ty(e)?)?)
                }
                BinOp::Div => format!("(.div {} {l} {r})", lean_ty(expr_int_ty(e)?)?),
                BinOp::Rem => format!("(.mod {} {l} {r})", lean_ty(expr_int_ty(e)?)?),
            }
        }
        ExprKind::Index { array, index, .. } => {
            validate_array_index(ctx, e, array, index)?;
            format!("(.index \"{array}\" {})", lower_expr(ctx, index)?)
        }
        ExprKind::Len { array } => {
            validate_array_len(ctx, e, array)?;
            format!("(.len \"{array}\")")
        }
        ExprKind::Widen { target, arg } => {
            format!("(.widen {} {})", lean_ty(*target)?, lower_expr(ctx, arg)?)
        }
        ExprKind::Narrow { target, arg } => {
            format!("(.narrow {} {})", lean_ty(*target)?, lower_expr(ctx, arg)?)
        }
        // The machine has one option family (ADR 0062); a nullable raw pointer
        // is an ordinary option carrying a pointer, so every representation
        // below emits the same machine constructor. The representation decides
        // only which payloads and positions are admitted — and, for a raw
        // pointer, which record tag must be checked against the program.
        ExprKind::SomeE(inner) => {
            check_option_repr(ctx, validate_some_constructor(e, inner)?)?;
            format!("(.someE {})", lower_expr(ctx, inner)?)
        }
        ExprKind::NoneE => {
            check_option_repr(ctx, svm_option_repr(e, "none")?)?;
            "(.noneE)".into()
        }
        ExprKind::IsSome { operand } => match validate_option_accessor(ctx, e, operand, false)? {
            SvmOptionRepr::AffineBoolArray => {
                let ExprKind::Var(name) = &operand.kind else {
                    unreachable!("validated named affine-option accessor")
                };
                format!("(.optIsSome (.var \"{name}\"))")
            }
            repr @ (SvmOptionRepr::Ordinary(_) | SvmOptionRepr::RawRecord(_)) => {
                check_option_repr(ctx, repr)?;
                format!("(.optIsSome {})", lower_expr(ctx, operand)?)
            }
        },
        ExprKind::OptValue { operand } => match validate_option_accessor(ctx, e, operand, true)? {
            SvmOptionRepr::AffineBoolArray => {
                unreachable!("affine options have no copying `.value` accessor")
            }
            repr @ (SvmOptionRepr::Ordinary(_) | SvmOptionRepr::RawRecord(_)) => {
                check_option_repr(ctx, repr)?;
                format!("(.optValue {})", lower_expr(ctx, operand)?)
            }
        },
        ExprKind::OptTake { option, .. } => return Err(affine_option_take_position(option)),
        ExprKind::RecordField { obj, field, .. } => {
            format!("(.recordField (.var \"{obj}\") \"{field}\")")
        }
        ExprKind::AllocArray { elem, len, init } => {
            validate_alloc_array(ctx, e, elem.clone(), len, init)?;
            format!(
                "(.allocArray {} {})",
                lower_expr(ctx, len)?,
                lower_expr(ctx, init)?
            )
        }
        ExprKind::Call { .. }
        | ExprKind::CtorCall { .. }
        | ExprKind::RecordLit { .. }
        | ExprKind::MethodCall { .. }
        | ExprKind::TraitCall { .. } => {
            return Err("calls are outside the SVM core subset".into());
        }
        ExprKind::ArrayLit(elements) => {
            validate_array_literal(ctx, e, elements)?;
            return Err("array literals are outside the SVM core subset (use alloc_array)".into());
        }
        ExprKind::Borrow { .. } => {
            return Err("borrows are outside the SVM core subset".into());
        }
        ExprKind::SelfField { .. }
        | ExprKind::SelfFieldLen { .. }
        | ExprKind::SelfFieldIndex { .. }
        | ExprKind::ClassField { .. }
        | ExprKind::ClassFieldLen { .. }
        | ExprKind::ClassFieldIndex { .. } => {
            return Err("class members are outside the SVM core subset".into());
        }
    })
}

fn int_lit(n: i128) -> String {
    if n < 0 {
        format!("({n})")
    } else {
        n.to_string()
    }
}

fn expr_int_ty(e: &Expr) -> Result<IntTy, String> {
    match e.ty {
        Some(Ty::Int(it)) => Ok(it),
        _ => Err("expression carries no integer type (unchecked program?)".into()),
    }
}

fn lean_ty(t: IntTy) -> Result<String, String> {
    match t {
        IntTy::TParam(_) => Err("type parameter survived monomorphization".into()),
        _ => Ok(format!(".{}", t.name())),
    }
}

/// Canonicalize an interpreter outcome into the harness wire format
/// (`done <val>` / `trap <name> <data>`), matching the Lean side's
/// `Config.render`. Unrecognized traps stay verbatim under an
/// `unclassified:` prefix so a comparison failure shows them.
pub fn canonical_outcome(program: &Program, res: Result<RtVal, String>) -> String {
    // A raw failure the interpreter described precisely is the machine's
    // `undef`; the harness compares classifications, not prose.
    if let Err(msg) = &res {
        if let Some(_detail) = msg.strip_prefix("undef: ") {
            return "undef".into();
        }
    }
    match res {
        Ok(v) => format!("done {}", render_rt_val(program, &v)),
        Err(msg) => classify_trap(&msg),
    }
}

/// Canonicalize the outcome and every machine-profile observation. Bare
/// executions deliberately retain the core wire format byte-for-byte; once
/// the UART profile is selected, the suffix must match `SVMUart.Config.render`
/// exactly so the differential oracle also detects dropped, duplicated, or
/// reordered device accesses.
pub fn canonical_observed(program: &Program, observed: ObservedRun) -> String {
    let ObservedRun {
        outcome,
        mmio,
        uart_profile,
        uart_cursor,
    } = observed;
    let core = canonical_outcome(program, outcome);
    if uart_profile.is_none() {
        return core;
    }
    let trace = mmio
        .iter()
        .map(|event| match event {
            MmioEvent::Read {
                address,
                width,
                value,
            } => format!("read(uart0,status,{address},{width},{value})"),
            MmioEvent::Write {
                address,
                width,
                value,
            } => format!("write(uart0,tx,{address},{width},{value})"),
        })
        .collect::<Vec<_>>()
        .join(",");
    format!(
        "{core} | profile={} cursor={uart_cursor} trace=[{trace}]",
        crate::profile::UART_POLL_V1_ID
    )
}

/// Scalars nested inside an aggregate are spelled bare on the wire — `arr
/// [1, 2]`, `opt some 7` — because the aggregate already names the shape.
/// Anything else falls back to the general value rendering. One helper
/// serves array elements and option payloads, mirroring the machine's
/// `Val.renderInner`, so the two positions cannot drift apart.
fn render_inner(program: &Program, value: &RtVal) -> String {
    match value {
        RtVal::Int(n) => n.to_string(),
        RtVal::Bool(b) => b.to_string(),
        other => render_rt_val(program, other),
    }
}

fn render_elements(program: &Program, array: &RtArray) -> String {
    array
        .iter()
        .map(|element| render_inner(program, element))
        .collect::<Vec<_>>()
        .join(", ")
}

fn render_rt_val(program: &Program, value: &RtVal) -> String {
    match value {
        RtVal::Unit => "unit".into(),
        RtVal::Int(n) => format!("int {n}"),
        RtVal::Bool(b) => format!("bool {b}"),
        RtVal::Arr(a) => format!("arr [{}]", render_elements(program, &a.borrow())),
        RtVal::Ptr(a, o) => format!("ptr {a}+{o}"),
        RtVal::Opt { value: None, .. } => "opt none".into(),
        RtVal::Opt {
            value: Some(value), ..
        } => format!("opt some {}", render_inner(program, value)),
        RtVal::AffineOptBoolArray(None) => "opt none".into(),
        RtVal::AffineOptBoolArray(Some(array)) => format!(
            "opt some {}",
            render_inner(program, &RtVal::Arr(array.clone()))
        ),
        // A class value cannot exist in the machine, so an affine class
        // option never reaches a rendered differential outcome; render
        // honestly if a future caller asks.
        RtVal::AffineOptClass { value: None, .. } => "opt none".into(),
        RtVal::AffineOptClass { value: Some(_), .. } => "opt some <class>".into(),
        // A nullable raw pointer is an ordinary option carrying a pointer,
        // so it takes the ordinary option spelling.
        RtVal::PtrOpt(None) => "opt none".into(),
        RtVal::PtrOpt(Some((allocation, offset))) => format!(
            "opt some {}",
            render_inner(program, &RtVal::Ptr(*allocation, *offset))
        ),
        RtVal::Record { record, fields } => {
            let Some(decl) = program.records.get(*record) else {
                return format!("unclassified record tag {record}");
            };
            let rendered = decl
                .fields
                .iter()
                .map(|field| match fields.get(&field.name) {
                    Some(value) => {
                        format!("{}={}", field.name, render_rt_val(program, value))
                    }
                    None => format!("{}=<missing>", field.name),
                })
                .collect::<Vec<_>>()
                .join(", ");
            format!("record {record} {{{rendered}}}")
        }
        RtVal::Obj { .. } => "unclassified class value".into(),
        RtVal::ResMap(..) => "unclassified erased resource map".into(),
    }
}

/// Map `interp.rs`'s rendered trap messages onto the machine's
/// structural traps. This is a harness-only concern: the interpreter
/// speaks to humans, the machine speaks constructors, and the mapping
/// between them lives here and nowhere else.
fn classify_trap(msg: &str) -> String {
    if msg == "division by zero" {
        return "trap divByZero".into();
    }
    if msg == "`.value` of an empty option" {
        return "trap optionNone".into();
    }
    if msg == "`.take` of an empty affine option" {
        return "trap optionNone".into();
    }
    if let Some(rest) = msg.strip_prefix("Euclidean quotient overflows: ") {
        if let Some(ty) = rest.strip_suffix(".min / -1") {
            return format!("trap overflow {ty}");
        }
    }
    if let Some(len) = msg.strip_prefix("OOM trap: alloc_array of length ") {
        return format!("trap oom {len}");
    }
    if let Some(rest) = msg.strip_prefix("narrow out of range: ") {
        if let Some((v, tail)) = rest.split_once(" does not fit in `") {
            if let Some(ty) = tail.strip_suffix('`') {
                return format!("trap narrowOOB {ty} {v}");
            }
        }
    }
    // "index out of bounds: index {i}, length {len}" for loads;
    // stores prefix it with "store ".
    let idx = msg.strip_prefix("store ").unwrap_or(msg);
    if let Some(rest) = idx.strip_prefix("index out of bounds: index ") {
        if let Some((i, len)) = rest.split_once(", length ") {
            return format!("trap indexOOB {i} {len}");
        }
    }
    // "overflow: `{src}` = {val} does not fit in `{ty}` ({op})"
    if msg.starts_with("overflow: ") {
        if let Some(pos) = msg.rfind(" does not fit in `") {
            let tail = &msg[pos + " does not fit in `".len()..];
            if let Some(ty) = tail.split('`').next() {
                return format!("trap overflow {ty}");
            }
        }
    }
    format!("unclassified: {msg}")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::span::Span;

    /// The wire format is compared against the machine's `Config.render`
    /// byte for byte, and every option payload is spelled by one helper, so
    /// a payload's spelling inside an option must equal its spelling bare.
    #[test]
    fn option_payloads_are_spelled_like_the_payload_itself() {
        use crate::interp::{RtVal, rt_bools};
        use std::cell::RefCell;
        use std::rc::Rc;
        let program = empty_program();
        let array = Rc::new(RefCell::new(rt_bools(&[true, false])));

        assert_eq!(render_rt_val(&program, &RtVal::Ptr(3, 4)), "ptr 3+4");
        assert_eq!(
            render_rt_val(&program, &RtVal::PtrOpt(Some((3, 4)))),
            "opt some ptr 3+4"
        );
        assert_eq!(render_rt_val(&program, &RtVal::PtrOpt(None)), "opt none");

        assert_eq!(
            render_rt_val(&program, &RtVal::Arr(array.clone())),
            "arr [true, false]"
        );
        assert_eq!(
            render_rt_val(&program, &RtVal::AffineOptBoolArray(Some(array))),
            "opt some arr [true, false]"
        );
        assert_eq!(
            render_rt_val(&program, &RtVal::AffineOptBoolArray(None)),
            "opt none"
        );
    }

    fn expr(kind: ExprKind, ty: Ty) -> Expr {
        Expr {
            kind,
            span: Span::new(0, 0),
            ty: Some(ty),
        }
    }

    fn empty_program() -> Program {
        Program {
            fns: Vec::new(),
            fn_templates: Vec::new(),
            class_templates: Vec::new(),
            classes: Vec::new(),
            records: Vec::new(),
            traits: Vec::new(),
            impls: Vec::new(),
            discharges: Vec::new(),
            ghosts: Vec::new(),
            defers: Vec::new(),
            assumes: Vec::new(),
            operators: Vec::new(),
            uses: Vec::new(),
            consts: Vec::new(),
        }
    }

    fn checked_fn(ret: Ty, body: Vec<Stmt>) -> Fn {
        Fn {
            is_pub: false,
            extern_info: None,
            name: "subject".into(),
            name_span: Span::new(0, 0),
            type_params: Vec::new(),
            type_bounds: Vec::new(),
            requires: Vec::new(),
            proof_reuse: ProofReuse::None,
            params: Vec::new(),
            ret,
            pres: Vec::new(),
            posts: Vec::new(),
            variant: None,
            body,
            span: Span::new(0, 0),
        }
    }

    #[test]
    fn lowering_rejects_unmodeled_option_payloads() {
        let program = empty_program();
        let unsupported = [
            Ty::Record(0),
            Ty::Param(TypeParamId::from_legacy(0)),
            Ty::Int(IntTy::TParam(0)),
        ];

        for payload in unsupported {
            let function = checked_fn(Ty::option(payload.clone()), Vec::new());
            let error = lower_fn(&program, &function)
                .expect_err("an unmodeled option must not inherit recursive SVM lowering");
            assert!(
                error.starts_with("svm.aggregate_payload_unsupported:"),
                "{payload:?}: {error}"
            );
        }
    }

    #[test]
    fn affine_option_lowering_is_local_atomic_and_fail_closed() {
        let program = empty_program();
        let affine_bool = Ty::affine_array_option(Ty::Bool);
        let affine_integer = Ty::affine_array_option(Ty::Int(IntTy::I32));
        let bool_array = Ty::array(Ty::Bool);

        for ty in [affine_bool.clone(), affine_integer.clone()] {
            let error = lower_fn(&program, &checked_fn(ty.clone(), Vec::new()))
                .expect_err("an affine option must not inherit ordinary option lowering");
            assert!(
                error.starts_with("svm.affine_option_unsupported:"),
                "{ty:?}: {error}"
            );
        }

        let mut parameterized = checked_fn(Ty::Unit, Vec::new());
        parameterized.params.push(Param {
            name: "pending".into(),
            ty: affine_bool.clone(),
            span: Span::new(0, 0),
            consumes: false,
        });
        let error = lower_fn(&program, &parameterized)
            .expect_err("the zero-argument harness gate must retain the affine diagnostic");
        assert!(
            error.starts_with("svm.affine_option_unsupported:"),
            "{error}"
        );

        let none_local = checked_fn(
            Ty::Unit,
            vec![Stmt::Decl {
                ty: affine_bool.clone(),
                name: "pending".into(),
                name_span: Span::new(0, 0),
                init: Some(expr(ExprKind::NoneE, affine_bool.clone())),
                mutable: true,
            }],
        );
        assert_eq!(
            lower_fn(&program, &none_local).unwrap(),
            "[(.assign \"pending\" (.noneE))]"
        );

        let mut ctx = LowerCtx::bare(&program);
        ctx.insert_local("pending", affine_bool.clone(), true, true)
            .unwrap();
        let accessor = expr(
            ExprKind::IsSome {
                operand: Box::new(expr(ExprKind::Var("pending".into()), affine_bool.clone())),
            },
            Ty::Bool,
        );
        assert_eq!(
            lower_expr(&ctx, &accessor).unwrap(),
            "(.optIsSome (.var \"pending\"))"
        );

        let take = expr(
            ExprKind::OptTake {
                option: "pending".into(),
                option_span: Span::new(0, 0),
            },
            bool_array.clone(),
        );
        assert_eq!(
            lower_fresh_bool_array_bind(&ctx, "bytes", bool_array.clone(), &take).unwrap(),
            "(.optTake \"bytes\" \"pending\")"
        );
        assert!(
            lower_expr(&ctx, &take)
                .unwrap_err()
                .starts_with("svm.affine_option_take_position:")
        );

        let value = expr(
            ExprKind::OptValue {
                operand: Box::new(expr(ExprKind::Var("pending".into()), affine_bool.clone())),
            },
            bool_array.clone(),
        );
        assert!(
            validate_expr_payloads(&ctx, &value)
                .unwrap_err()
                .starts_with("svm.affine_option_unsupported:")
        );

        let inferred_take = checked_fn(
            Ty::Unit,
            vec![Stmt::VarDecl {
                name: "bytes".into(),
                name_span: Span::new(0, 0),
                init: take.clone(),
                mutable: false,
                ty: Some(bool_array.clone()),
            }],
        );
        assert!(
            lower_fn(&program, &inferred_take)
                .unwrap_err()
                .starts_with("svm.affine_option_take_position:")
        );

        let alias = expr(
            ExprKind::OptTake {
                option: "pending".into(),
                option_span: Span::new(0, 0),
            },
            bool_array,
        );
        assert!(
            validate_affine_option_take(&ctx, "pending", &alias, "pending")
                .unwrap_err()
                .starts_with("svm.affine_option_take_alias:")
        );

        let mut immutable = LowerCtx::bare(&program);
        immutable
            .insert_local("pending", affine_bool, false, true)
            .unwrap();
        assert!(
            validate_affine_option_take(&immutable, "bytes", &take, "pending")
                .unwrap_err()
                .starts_with("svm.affine_option_immutable:")
        );

        let mut wrong_payload = LowerCtx::bare(&program);
        wrong_payload
            .insert_local("pending", affine_integer, true, true)
            .unwrap();
        assert!(
            validate_affine_option_take(&wrong_payload, "bytes", &take, "pending")
                .unwrap_err()
                .starts_with("svm.affine_option_unsupported:")
        );
    }

    #[test]
    fn lowering_rejects_invalid_record_layout_before_raw_use() {
        let mut program = empty_program();
        program.records.push(RecordDecl {
            is_pub: false,
            name: "BadLayout".into(),
            name_span: Span::new(0, 0),
            layout: StorageLayout { size: 1, align: 0 },
            layout_span: Span::new(0, 0),
            fields: Vec::new(),
            span: Span::new(0, 0),
        });

        let error = validate_program_option_positions(&program)
            .expect_err("zero alignment must be rejected before any raw record operation");
        assert!(error.starts_with("svm.record_schema_layout:"), "{error}");

        program.records[0].layout = StorageLayout { size: 8, align: 8 };
        program.records[0].fields.push(RecordField {
            name: "word".into(),
            ty: Ty::Int(IntTy::U64),
            offset: 1,
            span: Span::new(0, 0),
            offset_span: Span::new(0, 0),
        });
        let error = validate_program_option_positions(&program)
            .expect_err("misaligned record field geometry must fail SVM preflight");
        assert!(error.starts_with("svm.record_schema_geometry:"), "{error}");
    }

    #[test]
    fn lowering_supports_boolean_option_construction_and_accessors() {
        let program = empty_program();
        let bool_option = Ty::option(Ty::Bool);
        let mut ctx = LowerCtx::bare(&program);
        ctx.insert_local("choice", bool_option.clone(), false, true)
            .unwrap();

        let some_false = expr(
            ExprKind::SomeE(Box::new(expr(ExprKind::BoolLit(false), Ty::Bool))),
            bool_option.clone(),
        );
        assert_eq!(
            lower_expr(&ctx, &some_false).unwrap(),
            "(.someE (.boolLit false))"
        );
        assert_eq!(
            lower_expr(&ctx, &expr(ExprKind::NoneE, bool_option.clone())).unwrap(),
            "(.noneE)"
        );

        let option_var = || expr(ExprKind::Var("choice".into()), bool_option.clone());
        let is_some = expr(
            ExprKind::IsSome {
                operand: Box::new(option_var()),
            },
            Ty::Bool,
        );
        let value = expr(
            ExprKind::OptValue {
                operand: Box::new(option_var()),
            },
            Ty::Bool,
        );
        assert_eq!(
            lower_expr(&ctx, &is_some).unwrap(),
            "(.optIsSome (.var \"choice\"))"
        );
        assert_eq!(
            lower_expr(&ctx, &value).unwrap(),
            "(.optValue (.var \"choice\"))"
        );
    }

    #[test]
    fn option_constructors_require_coherent_checked_annotations() {
        let program = empty_program();
        let mut ctx = LowerCtx::bare(&program);
        ctx.insert_local("pointer", Ty::RawRecord(0), false, true)
            .unwrap();
        let bool_option = Ty::option(Ty::Bool);

        let wrong_payload = expr(
            ExprKind::SomeE(Box::new(expr(ExprKind::IntLit(1), Ty::Int(IntTy::I32)))),
            bool_option.clone(),
        );
        let nested_payload = expr(
            ExprKind::SomeE(Box::new(expr(
                ExprKind::SomeE(Box::new(expr(ExprKind::BoolLit(false), Ty::Bool))),
                bool_option.clone(),
            ))),
            bool_option.clone(),
        );
        let non_option_result = expr(ExprKind::NoneE, Ty::Bool);
        let missing_result = Expr {
            kind: ExprKind::SomeE(Box::new(expr(ExprKind::BoolLit(false), Ty::Bool))),
            span: Span::new(0, 0),
            ty: None,
        };
        let missing_payload = expr(
            ExprKind::SomeE(Box::new(Expr {
                kind: ExprKind::BoolLit(false),
                span: Span::new(0, 0),
                ty: None,
            })),
            bool_option.clone(),
        );

        for (malformed, diagnostic) in [
            (&wrong_payload, "svm.option_constructor_payload:"),
            (&nested_payload, "svm.option_constructor_payload:"),
            (&non_option_result, "svm.option_constructor_type:"),
            (&missing_result, "svm.option_constructor_type:"),
            (&missing_payload, "svm.option_constructor_payload:"),
        ] {
            let preflight = validate_expr_payloads(&ctx, malformed)
                .expect_err("malformed public AST must fail SVM preflight");
            assert!(preflight.starts_with(diagnostic), "{preflight}");
            let lowering = lower_expr(&ctx, malformed)
                .expect_err("direct expression lowering must enforce the same boundary");
            assert!(lowering.starts_with(diagnostic), "{lowering}");
        }

        let valid_bool = expr(
            ExprKind::SomeE(Box::new(expr(ExprKind::BoolLit(false), Ty::Bool))),
            bool_option.clone(),
        );
        let valid_int = expr(
            ExprKind::SomeE(Box::new(expr(ExprKind::IntLit(7), Ty::Int(IntTy::I32)))),
            Ty::option(Ty::Int(IntTy::I32)),
        );
        let valid_none = expr(ExprKind::NoneE, bool_option);
        for valid in [&valid_bool, &valid_int, &valid_none] {
            validate_expr_payloads(&ctx, valid).expect("coherent ordinary option constructor");
            lower_expr(&ctx, valid).expect("coherent ordinary option lowering");
        }

        let valid_raw = expr(
            ExprKind::SomeE(Box::new(expr(
                ExprKind::Var("pointer".into()),
                Ty::RawRecord(0),
            ))),
            Ty::OptionRaw(0),
        );
        validate_expr_payloads(&ctx, &valid_raw).expect("coherent nullable-raw constructor");
        validate_expr_payloads(&ctx, &expr(ExprKind::NoneE, Ty::OptionRaw(0)))
            .expect("coherent nullable-raw none constructor");

        let unsupported = expr(ExprKind::NoneE, Ty::option(Ty::Record(0)));
        let error = validate_expr_payloads(&ctx, &unsupported)
            .expect_err("record option payloads remain outside the supported subset");
        assert!(
            error.starts_with("svm.aggregate_payload_unsupported:"),
            "{error}"
        );
    }

    #[test]
    fn option_accessors_require_coherent_checked_annotations() {
        let program = empty_program();
        let bool_option = Ty::option(Ty::Bool);
        let int_option = Ty::option(Ty::Int(IntTy::I32));
        let mut ctx = LowerCtx::bare(&program);
        ctx.insert_local("choice", bool_option.clone(), false, true)
            .unwrap();
        ctx.insert_local("number", int_option.clone(), false, true)
            .unwrap();
        ctx.insert_local("pointer", Ty::OptionRaw(0), false, true)
            .unwrap();
        let bool_operand = || expr(ExprKind::Var("choice".into()), bool_option.clone());
        let int_operand = || expr(ExprKind::Var("number".into()), int_option.clone());

        let wrong_is_some_result = expr(
            ExprKind::IsSome {
                operand: Box::new(bool_operand()),
            },
            Ty::Int(IntTy::I32),
        );
        let wrong_bool_value_result = expr(
            ExprKind::OptValue {
                operand: Box::new(bool_operand()),
            },
            Ty::Int(IntTy::I32),
        );
        let wrong_int_value_result = expr(
            ExprKind::OptValue {
                operand: Box::new(int_operand()),
            },
            Ty::Bool,
        );
        let missing_result = Expr {
            kind: ExprKind::OptValue {
                operand: Box::new(bool_operand()),
            },
            span: Span::new(0, 0),
            ty: None,
        };
        let missing_operand = expr(
            ExprKind::IsSome {
                operand: Box::new(Expr {
                    kind: ExprKind::Var("choice".into()),
                    span: Span::new(0, 0),
                    ty: None,
                }),
            },
            Ty::Bool,
        );
        let non_option_operand = expr(
            ExprKind::OptValue {
                operand: Box::new(expr(ExprKind::BoolLit(false), Ty::Bool)),
            },
            Ty::Bool,
        );

        for (malformed, diagnostic) in [
            (&wrong_is_some_result, "svm.option_accessor_result:"),
            (&wrong_bool_value_result, "svm.option_accessor_result:"),
            (&wrong_int_value_result, "svm.option_accessor_result:"),
            (&missing_result, "svm.option_accessor_result:"),
            (&missing_operand, "svm.option_accessor_operand:"),
            (&non_option_operand, "svm.option_accessor_operand:"),
        ] {
            let preflight = validate_expr_payloads(&ctx, malformed)
                .expect_err("malformed public AST must fail SVM preflight");
            assert!(preflight.starts_with(diagnostic), "{preflight}");
            let lowering = lower_expr(&ctx, malformed)
                .expect_err("direct expression lowering must enforce the same boundary");
            assert!(lowering.starts_with(diagnostic), "{lowering}");
        }

        let valid = [
            expr(
                ExprKind::IsSome {
                    operand: Box::new(bool_operand()),
                },
                Ty::Bool,
            ),
            expr(
                ExprKind::OptValue {
                    operand: Box::new(bool_operand()),
                },
                Ty::Bool,
            ),
            expr(
                ExprKind::OptValue {
                    operand: Box::new(int_operand()),
                },
                Ty::Int(IntTy::I32),
            ),
        ];
        for accessor in &valid {
            validate_expr_payloads(&ctx, accessor).expect("coherent ordinary option accessor");
            lower_expr(&ctx, accessor).expect("coherent ordinary option accessor lowering");
        }

        let raw_operand = || expr(ExprKind::Var("pointer".into()), Ty::OptionRaw(0));
        validate_expr_payloads(
            &ctx,
            &expr(
                ExprKind::IsSome {
                    operand: Box::new(raw_operand()),
                },
                Ty::Bool,
            ),
        )
        .expect("coherent nullable-raw presence test");
        validate_expr_payloads(
            &ctx,
            &expr(
                ExprKind::OptValue {
                    operand: Box::new(raw_operand()),
                },
                Ty::RawRecord(0),
            ),
        )
        .expect("coherent nullable-raw projection");
    }

    #[test]
    fn canonical_boolean_option_spelling_is_not_integer_or_nested_bool() {
        let program = empty_program();
        let absent = RtVal::Opt {
            payload: Ty::Bool,
            value: None,
        };
        let false_value = RtVal::Opt {
            payload: Ty::Bool,
            value: Some(Box::new(RtVal::Bool(false))),
        };
        let true_value = RtVal::Opt {
            payload: Ty::Bool,
            value: Some(Box::new(RtVal::Bool(true))),
        };
        let affine_none = RtVal::AffineOptBoolArray(None);
        let affine_empty = RtVal::AffineOptBoolArray(Some(std::rc::Rc::new(
            std::cell::RefCell::new(crate::interp::rt_bools(&[])),
        )));
        let affine_values = RtVal::AffineOptBoolArray(Some(std::rc::Rc::new(
            std::cell::RefCell::new(crate::interp::rt_bools(&[true, false])),
        )));

        assert_eq!(render_rt_val(&program, &absent), "opt none");
        assert_eq!(render_rt_val(&program, &false_value), "opt some false");
        assert_eq!(render_rt_val(&program, &true_value), "opt some true");
        assert_eq!(render_rt_val(&program, &affine_none), "opt none");
        assert_eq!(render_rt_val(&program, &affine_empty), "opt some arr []");
        assert_eq!(
            render_rt_val(&program, &affine_values),
            "opt some arr [true, false]"
        );
        assert_eq!(
            classify_trap("`.take` of an empty affine option"),
            "trap optionNone"
        );
    }

    #[test]
    fn lowering_admits_copyable_option_parameters_and_gates_their_payloads() {
        let program = empty_program();
        for payload in [Ty::Bool, Ty::Int(IntTy::U64)] {
            let mut function = checked_fn(Ty::Unit, Vec::new());
            function.params.push(Param {
                name: "choice".into(),
                ty: Ty::option(payload.clone()),
                span: Span::new(0, 0),
                consumes: false,
            });
            let entry = lower_fn_entry(&program, &function).unwrap_or_else(|error| {
                panic!(
                    "`option<{}>` is a machine parameter value: {error}",
                    payload.name()
                )
            });
            assert!(entry.contains("\"choice\""), "{entry}");
        }

        let mut generic = checked_fn(Ty::Unit, Vec::new());
        generic.params.push(Param {
            name: "choice".into(),
            ty: Ty::option(Ty::Param(TypeParamId::from_legacy(0))),
            span: Span::new(0, 0),
            consumes: false,
        });
        let error = lower_fn_entry(&program, &generic)
            .expect_err("an unresolved option payload has no machine representation");
        assert!(
            error.starts_with("svm.aggregate_payload_unsupported:"),
            "{error}"
        );

        let mut affine = checked_fn(Ty::Unit, Vec::new());
        affine.params.push(Param {
            name: "choice".into(),
            ty: Ty::affine_array_option(Ty::Bool),
            span: Span::new(0, 0),
            consumes: false,
        });
        let error = lower_fn_entry(&program, &affine)
            .expect_err("an ownership-bearing option has no machine call ABI");
        assert!(
            error.starts_with("svm.affine_option_unsupported:"),
            "{error}"
        );
    }

    #[test]
    fn lowering_rejects_boolean_arrays_outside_fresh_owned_locals() {
        let program = empty_program();
        let array_ty = Ty::array(Ty::Bool);

        let mut parameter = checked_fn(Ty::Bool, Vec::new());
        parameter.params.push(Param {
            name: "bits".into(),
            ty: array_ty.clone(),
            span: Span::new(0, 0),
            consumes: false,
        });
        let error = lower_fn_entry(&program, &parameter)
            .expect_err("Boolean arrays have no SVM parameter ABI");
        assert!(
            error.starts_with("svm.bool_array_position_unsupported:"),
            "{error}"
        );

        let returned = checked_fn(array_ty.clone(), Vec::new());
        let error =
            lower_fn_entry(&program, &returned).expect_err("Boolean arrays have no SVM result ABI");
        assert!(
            error.starts_with("svm.bool_array_position_unsupported:"),
            "{error}"
        );

        let mut field_program = empty_program();
        field_program.classes.push(ClassDecl {
            is_pub: false,
            name: "Holder".into(),
            name_span: Span::new(0, 0),
            type_params: Vec::new(),
            type_bounds: Vec::new(),
            proof_reuse: ProofReuse::None,
            fields: vec![Field {
                name: "bits".into(),
                ty: array_ty,
                span: Span::new(0, 0),
                must_consume: false,
            }],
            invariants: Vec::new(),
            inits: Vec::new(),
            methods: Vec::new(),
            deinit: None,
            span: Span::new(0, 0),
        });
        let error = validate_program_option_positions(&field_program)
            .expect_err("Boolean arrays cannot enter class storage");
        assert!(
            error.starts_with("svm.bool_array_position_unsupported:"),
            "{error}"
        );
    }

    #[test]
    fn lowering_rejects_residual_generic_declarations() {
        let program = empty_program();
        let mut function = checked_fn(Ty::option(Ty::Bool), Vec::new());
        function.type_params.push("T".into());
        function.type_bounds.push(None);

        let error = lower_fn(&program, &function)
            .expect_err("the SVM accepts only post-monomorphization declarations");
        assert!(
            error.starts_with("svm.type_parameter_unsupported:"),
            "{error}"
        );
    }

    #[test]
    fn lowering_rejects_nonunit_fallthrough_and_resource_results() {
        let program = empty_program();
        let fallthrough = checked_fn(Ty::Int(IntTy::U64), Vec::new());
        assert!(
            lower_fn_entry(&program, &fallthrough)
                .expect_err("a non-unit entry must return on every path")
                .starts_with("svm.missing_return:")
        );

        let resource_result = checked_fn(Ty::Res(ResKind::RawSpan), Vec::new());
        assert!(
            lower_fn_entry(&program, &resource_result)
                .expect_err("erased authority has no SVM result representation")
                .starts_with("svm.resource_return_unsupported:")
        );
    }

    #[test]
    fn a_normal_calls_require_coherent_executable_signatures() {
        let mut program = empty_program();
        let mut choose = checked_fn(Ty::option(Ty::Bool), Vec::new());
        choose.name = "choose".into();
        choose.params.push(Param {
            name: "selector".into(),
            ty: Ty::Int(IntTy::I32),
            span: Span::new(0, 0),
            consumes: false,
        });
        program.fns.push(choose);
        let ctx = LowerCtx::bare(&program);
        let call = |args: Vec<Expr>, ty: Option<Ty>| Expr {
            kind: ExprKind::Call {
                callee: "choose".into(),
                callee_span: Span::new(0, 0),
                type_args: Vec::new(),
                args,
            },
            span: Span::new(0, 0),
            ty,
        };
        let selector = || expr(ExprKind::IntLit(0), Ty::Int(IntTy::I32));

        let valid = call(vec![selector()], Some(Ty::option(Ty::Bool)));
        validate_expr_payloads(&ctx, &valid).expect("checked option-returning call");
        assert_eq!(
            lower_call(&ctx, &Some("choice".into()), &valid).unwrap(),
            "(.call (some \"choice\") \"choose\" [(.byValue (.intLit .i32 0))])"
        );

        let wrong_result = call(vec![selector()], Some(Ty::Int(IntTy::I32)));
        let missing_result = call(vec![selector()], None);
        let wrong_arity = call(Vec::new(), Some(Ty::option(Ty::Bool)));
        let wrong_argument = call(
            vec![expr(ExprKind::BoolLit(false), Ty::Bool)],
            Some(Ty::option(Ty::Bool)),
        );
        let missing_argument = call(
            vec![Expr {
                kind: ExprKind::IntLit(0),
                span: Span::new(0, 0),
                ty: None,
            }],
            Some(Ty::option(Ty::Bool)),
        );
        for (malformed, diagnostic) in [
            (&wrong_result, "svm.call_result_type:"),
            (&missing_result, "svm.call_result_type:"),
            (&wrong_arity, "svm.call_arity:"),
            (&wrong_argument, "svm.call_argument_type:"),
            (&missing_argument, "svm.call_argument_type:"),
        ] {
            let preflight = validate_expr_payloads(&ctx, malformed)
                .expect_err("malformed call must fail SVM preflight");
            assert!(preflight.starts_with(diagnostic), "{preflight}");
            let lowering = lower_call(&ctx, &Some("choice".into()), malformed)
                .expect_err("direct call lowering must enforce the same signature");
            assert!(lowering.starts_with(diagnostic), "{lowering}");
        }

        let mut resource_program = empty_program();
        let mut consume = checked_fn(Ty::Unit, Vec::new());
        consume.name = "consume".into();
        consume.params.push(Param {
            name: "authority".into(),
            ty: Ty::Res(ResKind::Uart),
            span: Span::new(0, 0),
            consumes: false,
        });
        resource_program.fns.push(consume);
        let mut resource_ctx = LowerCtx::bare(&resource_program);
        resource_ctx
            .insert_local("uart", Ty::Res(ResKind::Uart), false, true)
            .unwrap();
        let erased_resource_call = Expr {
            kind: ExprKind::Call {
                callee: "consume".into(),
                callee_span: Span::new(0, 0),
                type_args: Vec::new(),
                args: vec![Expr {
                    kind: ExprKind::Var("uart".into()),
                    span: Span::new(0, 0),
                    ty: None,
                }],
            },
            span: Span::new(0, 0),
            ty: Some(Ty::Unit),
        };
        let error = validate_expr_payloads(&resource_ctx, &erased_resource_call)
            .expect_err("erased resource authority has no ordinary SVM call ABI");
        assert!(
            error.starts_with("svm.call_resource_unsupported:"),
            "{error}"
        );
    }

    #[test]
    fn lowering_rejects_boolean_and_nested_residual_type_arguments() {
        let program = empty_program();
        let ctx = LowerCtx::bare(&program);
        for generic in [
            GenericTy::Bool,
            GenericTy::Option(Box::new(GenericTy::Bool)),
        ] {
            let call = expr(
                ExprKind::Call {
                    callee: "identity".into(),
                    callee_span: Span::new(0, 0),
                    type_args: vec![TypeArg {
                        ty: generic.clone(),
                        span: Span::new(0, 0),
                    }],
                    args: Vec::new(),
                },
                Ty::Bool,
            );
            let error = validate_expr_payloads(&ctx, &call)
                .expect_err("all residual generic use sites are outside the SVM input");
            assert_eq!(
                error,
                "svm.type_parameter_unsupported: generic type arguments escaped monomorphization"
            );
        }
    }

    #[test]
    fn lowering_rejects_option_fields_and_trait_returns_independently() {
        let mut class_program = empty_program();
        class_program.classes.push(ClassDecl {
            is_pub: false,
            name: "Holder".into(),
            name_span: Span::new(0, 0),
            type_params: Vec::new(),
            type_bounds: Vec::new(),
            proof_reuse: ProofReuse::None,
            fields: vec![Field {
                name: "choice".into(),
                ty: Ty::option(Ty::Bool),
                span: Span::new(0, 0),
                must_consume: false,
            }],
            invariants: Vec::new(),
            inits: Vec::new(),
            methods: Vec::new(),
            deinit: None,
            span: Span::new(0, 0),
        });
        let field_error = validate_program_option_positions(&class_program)
            .expect_err("the machine has no option-valued class storage");
        assert!(
            field_error.starts_with("svm.option_position_unsupported:"),
            "{field_error}"
        );

        let mut trait_program = empty_program();
        trait_program.traits.push(TraitDecl {
            is_pub: false,
            name: "Chooser".into(),
            name_span: Span::new(0, 0),
            specs: Vec::new(),
            methods: vec![checked_fn(Ty::option(Ty::Bool), Vec::new())],
            span: Span::new(0, 0),
        });
        let trait_error = validate_program_option_positions(&trait_program)
            .expect_err("the machine does not model option-valued trait results");
        assert!(
            trait_error.starts_with("svm.option_position_unsupported:"),
            "{trait_error}"
        );

        let mut trait_param_program = empty_program();
        let mut method = checked_fn(Ty::Unit, Vec::new());
        method.params.push(Param {
            name: "choice".into(),
            ty: Ty::option(Ty::Bool),
            span: Span::new(0, 0),
            consumes: false,
        });
        trait_param_program.traits.push(TraitDecl {
            is_pub: false,
            name: "Chooser".into(),
            name_span: Span::new(0, 0),
            specs: Vec::new(),
            methods: vec![method],
            span: Span::new(0, 0),
        });
        let trait_param_error = validate_program_option_positions(&trait_param_program)
            .expect_err("the machine does not model option-valued trait parameters");
        assert!(
            trait_param_error.starts_with("svm.option_position_unsupported:"),
            "{trait_param_error}"
        );
    }

    #[test]
    fn lowering_rejects_externs_before_they_can_become_empty_bodies() {
        let program = empty_program();
        let mut function = checked_fn(Ty::option(Ty::Bool), Vec::new());
        function.extern_info = Some(ExternInfo {
            abi: "C".into(),
            audit_id: "test-only".into(),
            reason: "exercise the lowering boundary".into(),
            span: Span::new(0, 0),
        });

        let error = lower_fn_entry(&program, &function)
            .expect_err("an extern must not lower as a no-op function");
        assert!(error.contains("audited extern"), "{error}");
    }

    #[test]
    fn lowering_materializes_fresh_boolean_array_allocations_and_literals() {
        let program = empty_program();
        let ctx = LowerCtx::bare(&program);
        let array_ty = Ty::array(Ty::Bool);
        let allocation = expr(
            ExprKind::AllocArray {
                elem: Ty::Bool,
                len: Box::new(expr(ExprKind::IntLit(3), Ty::Int(IntTy::U64))),
                init: Box::new(expr(ExprKind::BoolLit(true), Ty::Bool)),
            },
            array_ty.clone(),
        );
        assert_eq!(
            lower_fresh_bool_array_bind(&ctx, "allocated", array_ty.clone(), &allocation).unwrap(),
            "(.assign \"allocated\" (.allocArray (.intLit .u64 3) (.boolLit true)))"
        );

        let literal = expr(
            ExprKind::ArrayLit(vec![
                expr(ExprKind::BoolLit(true), Ty::Bool),
                expr(ExprKind::BoolLit(false), Ty::Bool),
            ]),
            array_ty.clone(),
        );
        assert_eq!(
            lower_fresh_bool_array_bind(&ctx, "literal", array_ty.clone(), &literal).unwrap(),
            "(.assign \"_bool_lit_literal_0\" (.boolLit true)), \
             (.assign \"_bool_lit_literal_1\" (.boolLit false)), \
             (.assign \"literal\" (.allocArray (.intLit .u64 2) (.boolLit false))), \
             (.store \"literal\" (.intLit .u64 0) (.var \"_bool_lit_literal_0\")), \
             (.store \"literal\" (.intLit .u64 1) (.var \"_bool_lit_literal_1\"))"
        );
        let empty = expr(ExprKind::ArrayLit(Vec::new()), array_ty.clone());
        assert_eq!(
            lower_fresh_bool_array_bind(&ctx, "empty", array_ty.clone(), &empty).unwrap(),
            "(.assign \"empty\" (.allocArray (.intLit .u64 0) (.boolLit false)))"
        );

        let error = validate_array_literal_len(Ty::Bool, 50_000_001)
            .expect_err("literal expansion must remain inside the formal allocation cap");
        assert!(error.starts_with("svm.array_literal_capacity:"), "{error}");
        validate_array_literal_len(Ty::Bool, 50_000_000)
            .expect("the exact formal allocation cap remains lowerable");

        let mut forged_ctx = LowerCtx::bare(&program);
        forged_ctx
            .insert_local("_bool_lit_literal_0", Ty::Bool, false, true)
            .unwrap();
        let error = lower_fresh_bool_array_bind(&forged_ctx, "literal", array_ty, &literal)
            .expect_err("forged compiler-reserved locals cannot capture literal temporaries");
        assert!(
            error.starts_with("svm.bool_array_temp_collision:"),
            "{error}"
        );
    }

    #[test]
    fn boolean_arrays_reject_uninitialized_alias_rebind_and_exposure() {
        let program = empty_program();
        let array_ty = Ty::array(Ty::Bool);
        let literal = || {
            expr(
                ExprKind::ArrayLit(vec![expr(ExprKind::BoolLit(true), Ty::Bool)]),
                array_ty.clone(),
            )
        };
        let declaration = |name: &str, mutable: bool| Stmt::Decl {
            ty: array_ty.clone(),
            name: name.into(),
            name_span: Span::new(0, 0),
            init: Some(literal()),
            mutable,
        };

        let uninitialized = checked_fn(
            Ty::Unit,
            vec![Stmt::Decl {
                ty: array_ty.clone(),
                name: "bits".into(),
                name_span: Span::new(0, 0),
                init: None,
                mutable: true,
            }],
        );
        let error = lower_fn(&program, &uninitialized)
            .expect_err("Boolean arrays must always be fresh and initialized");
        assert!(error.starts_with("svm.bool_array_fresh_local:"), "{error}");

        let aliased = checked_fn(
            Ty::Unit,
            vec![
                declaration("source", false),
                Stmt::Decl {
                    ty: array_ty.clone(),
                    name: "alias".into(),
                    name_span: Span::new(0, 0),
                    init: Some(expr(ExprKind::Var("source".into()), array_ty.clone())),
                    mutable: false,
                },
            ],
        );
        let error =
            lower_fn(&program, &aliased).expect_err("Boolean array locals cannot be aliased");
        assert!(
            error.starts_with("svm.bool_array_transport_unsupported:"),
            "{error}"
        );

        let rebound = checked_fn(
            Ty::Unit,
            vec![
                declaration("bits", true),
                Stmt::Assign {
                    name: "bits".into(),
                    name_span: Span::new(0, 0),
                    value: literal(),
                },
            ],
        );
        let error =
            lower_fn(&program, &rebound).expect_err("Boolean array locals cannot be rebound");
        assert!(
            error.starts_with("svm.bool_array_position_unsupported:")
                || error.starts_with("svm.array_rebind_unsupported:"),
            "{error}"
        );

        let exposure = checked_fn(
            Ty::Unit,
            vec![
                declaration("bits", true),
                Stmt::Expose {
                    kw_span: Span::new(0, 0),
                    array: "bits".into(),
                    array_span: Span::new(0, 0),
                    mutable: true,
                    ptr: "ptr".into(),
                    ptr_span: Span::new(0, 0),
                    res: "memory".into(),
                    res_span: Span::new(0, 0),
                    body: Vec::new(),
                },
            ],
        );
        let error = lower_fn(&program, &exposure)
            .expect_err("Boolean array locals cannot cross the exposure bridge");
        assert!(error.starts_with("svm.array_expose_type:"), "{error}");
    }

    #[test]
    fn a_borrowed_boolean_array_is_a_call_argument_and_a_unique_one_is_a_loan() {
        let program = empty_program();
        let array_ty = Ty::array(Ty::Bool);
        let shared_ty = Ty::array_ref(Ty::Bool, Mutability::Shared);
        let unique_ty = Ty::array_ref(Ty::Bool, Mutability::Mut);

        let mut ctx = LowerCtx::bare(&program);
        ctx.insert_local("bits", array_ty.clone(), true, true)
            .unwrap();
        ctx.insert_local("frozen", array_ty, false, true).unwrap();
        ctx.insert_local("lent", unique_ty.clone(), false, true)
            .unwrap();

        let borrow = |array: &str, mutable: bool, ty: Ty| Expr {
            kind: ExprKind::Borrow {
                array: array.into(),
                field: None,
                mutable,
            },
            span: Span::new(0, 0),
            ty: Some(ty),
        };

        // A shared borrow may only be read, so the caller's sequence is what
        // the callee is owed; a unique one is a loan the pop returns.
        assert_eq!(
            lower_arg(&ctx, &borrow("bits", false, shared_ty.clone())).unwrap(),
            "(.byValue (.var \"bits\"))"
        );
        assert_eq!(
            lower_arg(&ctx, &borrow("bits", true, unique_ty.clone())).unwrap(),
            "(.lend \"bits\")"
        );
        // A reborrow by name lends the same storage one frame further, so the
        // loans compose back to the owner.
        assert_eq!(
            lower_arg(&ctx, &expr(ExprKind::Var("lent".into()), unique_ty.clone())).unwrap(),
            "(.lend \"lent\")"
        );

        // A loan needs a local to return to.
        let field_borrow = Expr {
            kind: ExprKind::Borrow {
                array: "bits".into(),
                field: Some("flags".into()),
                mutable: true,
            },
            span: Span::new(0, 0),
            ty: Some(unique_ty.clone()),
        };
        let error = lower_arg(&ctx, &field_borrow).expect_err("a loan must name a local");
        assert!(error.starts_with("svm.array_borrow_place:"), "{error}");

        // A borrow's type is its source's array under the requested mode, and
        // an immutable owner has no unique borrow to give.
        assert_eq!(
            semantic_expr_ty(
                &ctx,
                &borrow("bits", false, shared_ty.clone()),
                shared_ty.clone(),
                "argument 1",
            )
            .unwrap(),
            shared_ty
        );
        let error = semantic_expr_ty(
            &ctx,
            &borrow("frozen", true, unique_ty.clone()),
            unique_ty,
            "argument 1",
        )
        .expect_err("an immutable owner cannot be lent uniquely");
        assert!(error.starts_with("svm.array_borrow_place:"), "{error}");
    }

    #[test]
    fn lowering_checks_alloc_array_element_even_if_annotation_is_integer() {
        let program = empty_program();
        let allocation = expr(
            ExprKind::AllocArray {
                elem: Ty::option(Ty::Int(IntTy::U64)),
                len: Box::new(expr(ExprKind::IntLit(1), Ty::Int(IntTy::U64))),
                init: Box::new(expr(ExprKind::IntLit(0), Ty::Int(IntTy::U8))),
            },
            Ty::array(Ty::Int(IntTy::U8)),
        );
        let function = checked_fn(
            Ty::Unit,
            vec![Stmt::Decl {
                ty: Ty::array(Ty::Int(IntTy::U8)),
                name: "values".into(),
                name_span: Span::new(0, 0),
                init: Some(allocation),
                mutable: false,
            }],
        );

        let error = lower_fn(&program, &function)
            .expect_err("AllocArray's own payload must be checked independently");
        assert_eq!(
            error,
            "svm.aggregate_payload_unsupported: alloc_array has array payload \
             `option<u64>`; the SVM currently lowers only concrete integer and Boolean \
             payloads"
        );
    }

    #[test]
    fn lowering_requires_concrete_integer_index_annotation() {
        let program = empty_program();
        let load = expr(
            ExprKind::Index {
                array: "values".into(),
                array_span: Span::new(0, 0),
                index: Box::new(expr(ExprKind::IntLit(0), Ty::Int(IntTy::U64))),
            },
            Ty::Bool,
        );
        let function = checked_fn(
            Ty::Unit,
            vec![
                Stmt::Decl {
                    ty: Ty::array(Ty::Int(IntTy::U8)),
                    name: "values".into(),
                    name_span: Span::new(0, 0),
                    init: Some(expr(
                        ExprKind::AllocArray {
                            elem: Ty::Int(IntTy::U8),
                            len: Box::new(expr(ExprKind::IntLit(1), Ty::Int(IntTy::U64))),
                            init: Box::new(expr(ExprKind::IntLit(0), Ty::Int(IntTy::U8))),
                        },
                        Ty::array(Ty::Int(IntTy::U8)),
                    )),
                    mutable: false,
                },
                Stmt::Decl {
                    ty: Ty::Bool,
                    name: "value".into(),
                    name_span: Span::new(0, 0),
                    init: Some(load),
                    mutable: false,
                },
            ],
        );

        let error = lower_fn(&program, &function)
            .expect_err("SVM index loads produce concrete integer machine values");
        assert_eq!(
            error,
            "svm.array_index_result_type: array index result is annotated `bool`; expected `u8`"
        );
    }

    #[test]
    fn array_constructors_require_coherent_checked_annotations() {
        let program = empty_program();
        let ctx = LowerCtx::bare(&program);
        let u8_array = Ty::array(Ty::Int(IntTy::U8));
        let allocation = |len: Expr, init: Expr, ty: Option<Ty>| Expr {
            kind: ExprKind::AllocArray {
                elem: Ty::Int(IntTy::U8),
                len: Box::new(len),
                init: Box::new(init),
            },
            span: Span::new(0, 0),
            ty,
        };
        let length = || expr(ExprKind::IntLit(2), Ty::Int(IntTy::U64));
        let byte = || expr(ExprKind::IntLit(7), Ty::Int(IntTy::U8));

        let valid = allocation(length(), byte(), Some(u8_array.clone()));
        validate_expr_payloads(&ctx, &valid).expect("coherent integer allocation preflight");
        assert_eq!(
            lower_expr(&ctx, &valid).unwrap(),
            "(.allocArray (.intLit .u64 2) (.intLit .u8 7))"
        );

        let malformed = [
            (
                allocation(length(), byte(), Some(Ty::array(Ty::Int(IntTy::I32)))),
                "svm.array_alloc_result_type:",
            ),
            (
                allocation(length(), byte(), None),
                "svm.array_alloc_result_type:",
            ),
            (
                allocation(
                    expr(ExprKind::BoolLit(false), Ty::Bool),
                    byte(),
                    Some(u8_array.clone()),
                ),
                "svm.sink_type:",
            ),
            (
                allocation(
                    length(),
                    expr(ExprKind::IntLit(7), Ty::Int(IntTy::I32)),
                    Some(u8_array.clone()),
                ),
                "svm.sink_type:",
            ),
        ];
        for (value, diagnostic) in &malformed {
            let preflight = validate_expr_payloads(&ctx, value)
                .expect_err("malformed allocation must fail SVM preflight");
            assert!(preflight.starts_with(*diagnostic), "{preflight}");
            let lowering = lower_expr(&ctx, value)
                .expect_err("direct allocation lowering must re-check cached types");
            assert!(lowering.starts_with(*diagnostic), "{lowering}");
        }

        let literal = expr(
            ExprKind::ArrayLit(vec![byte(), expr(ExprKind::IntLit(8), Ty::Int(IntTy::U8))]),
            u8_array.clone(),
        );
        validate_expr_payloads(&ctx, &literal).expect("coherent integer literal preflight");
        assert_eq!(
            lower_expr(&ctx, &literal).unwrap_err(),
            "array literals are outside the SVM core subset (use alloc_array)"
        );

        let wrong_literal_element = expr(
            ExprKind::ArrayLit(vec![expr(ExprKind::IntLit(1), Ty::Int(IntTy::I32))]),
            u8_array,
        );
        for error in [
            validate_expr_payloads(&ctx, &wrong_literal_element).unwrap_err(),
            lower_expr(&ctx, &wrong_literal_element).unwrap_err(),
        ] {
            assert!(error.starts_with("svm.sink_type:"), "{error}");
        }
    }

    #[test]
    fn array_integer_operands_reject_forged_boolean_annotations() {
        let program = empty_program();
        let array_ty = Ty::array(Ty::Int(IntTy::U8));
        let forged_bool = |ty| expr(ExprKind::BoolLit(true), ty);
        let length = || expr(ExprKind::IntLit(1), Ty::Int(IntTy::U64));
        let byte = || expr(ExprKind::IntLit(0), Ty::Int(IntTy::U8));
        let allocation = |len: Expr, init: Expr| {
            expr(
                ExprKind::AllocArray {
                    elem: Ty::Int(IntTy::U8),
                    len: Box::new(len),
                    init: Box::new(init),
                },
                array_ty.clone(),
            )
        };

        let mut ctx = LowerCtx::bare(&program);
        ctx.insert_local("bytes", array_ty.clone(), true, true)
            .unwrap();
        let malformed_exprs = [
            (
                allocation(forged_bool(Ty::Int(IntTy::U64)), byte()),
                "alloc_array length",
            ),
            (
                allocation(length(), forged_bool(Ty::Int(IntTy::U8))),
                "alloc_array initializer",
            ),
            (
                expr(
                    ExprKind::ArrayLit(vec![forged_bool(Ty::Int(IntTy::U8))]),
                    array_ty,
                ),
                "array literal element 1",
            ),
            (
                expr(
                    ExprKind::Index {
                        array: "bytes".into(),
                        array_span: Span::new(0, 0),
                        index: Box::new(forged_bool(Ty::Int(IntTy::U64))),
                    },
                    Ty::Int(IntTy::U8),
                ),
                "array index operand",
            ),
        ];
        for (malformed, context) in &malformed_exprs {
            for error in [
                validate_expr_payloads(&ctx, malformed).unwrap_err(),
                lower_expr(&ctx, malformed).unwrap_err(),
            ] {
                assert!(error.starts_with("svm.sink_type:"), "{error}");
                assert!(error.contains(context), "{error}");
            }
        }

        let malformed_stores = [
            (
                Stmt::Store {
                    array: "bytes".into(),
                    array_span: Span::new(0, 0),
                    index: forged_bool(Ty::Int(IntTy::U64)),
                    value: byte(),
                },
                "array store index",
            ),
            (
                Stmt::Store {
                    array: "bytes".into(),
                    array_span: Span::new(0, 0),
                    index: length(),
                    value: forged_bool(Ty::Int(IntTy::U8)),
                },
                "array store value",
            ),
        ];
        for (malformed, context) in &malformed_stores {
            let mut preflight_ctx = ctx.clone();
            let preflight =
                validate_stmt_payloads(&mut preflight_ctx, std::slice::from_ref(malformed))
                    .unwrap_err();
            let mut lowering_ctx = ctx.clone();
            let direct = lower_stmt_erasing(&mut lowering_ctx, malformed).unwrap_err();
            for error in [preflight, direct] {
                assert!(error.starts_with("svm.sink_type:"), "{error}");
                assert!(error.contains(context), "{error}");
            }
        }
    }

    #[test]
    fn boolean_array_operands_require_exact_boolean_types() {
        let program = empty_program();
        let array_ty = Ty::array(Ty::Bool);
        let mut ctx = LowerCtx::bare(&program);
        ctx.insert_local("bits", array_ty.clone(), true, true)
            .unwrap();
        let length = || expr(ExprKind::IntLit(2), Ty::Int(IntTy::U64));
        let boolean = || expr(ExprKind::BoolLit(false), Ty::Bool);

        let allocation = expr(
            ExprKind::AllocArray {
                elem: Ty::Bool,
                len: Box::new(length()),
                init: Box::new(boolean()),
            },
            array_ty.clone(),
        );
        validate_alloc_array(
            &ctx,
            &allocation,
            Ty::Bool,
            match &allocation.kind {
                ExprKind::AllocArray { len, .. } => len,
                _ => unreachable!(),
            },
            match &allocation.kind {
                ExprKind::AllocArray { init, .. } => init,
                _ => unreachable!(),
            },
        )
        .expect("coherent Boolean allocation");

        let bad_allocation = expr(
            ExprKind::AllocArray {
                elem: Ty::Bool,
                len: Box::new(length()),
                init: Box::new(expr(ExprKind::IntLit(0), Ty::Int(IntTy::I32))),
            },
            array_ty,
        );
        let ExprKind::AllocArray { len, init, .. } = &bad_allocation.kind else {
            unreachable!()
        };
        let error = validate_alloc_array(&ctx, &bad_allocation, Ty::Bool, len, init)
            .expect_err("Boolean allocations cannot inherit integer initializers");
        assert!(error.starts_with("svm.sink_type:"), "{error}");

        let index = expr(
            ExprKind::Index {
                array: "bits".into(),
                array_span: Span::new(0, 0),
                index: Box::new(expr(ExprKind::IntLit(1), Ty::Int(IntTy::U64))),
            },
            Ty::Bool,
        );
        assert_eq!(
            lower_expr(&ctx, &index).unwrap(),
            "(.index \"bits\" (.intLit .u64 1))"
        );
        let wrong_index = Expr {
            ty: Some(Ty::Int(IntTy::U8)),
            ..index.clone()
        };
        let error = validate_expr_payloads(&ctx, &wrong_index)
            .expect_err("Boolean array reads cannot be forged into integers");
        assert!(error.starts_with("svm.array_index_result_type:"), "{error}");

        let store = Stmt::Store {
            array: "bits".into(),
            array_span: Span::new(0, 0),
            index: expr(ExprKind::IntLit(0), Ty::Int(IntTy::U64)),
            value: expr(ExprKind::BoolLit(true), Ty::Bool),
        };
        assert_eq!(
            lower_stmt_erasing(&mut ctx, &store).unwrap(),
            Some("(.store \"bits\" (.intLit .u64 0) (.boolLit true))".into())
        );
        let wrong_store = Stmt::Store {
            array: "bits".into(),
            array_span: Span::new(0, 0),
            index: expr(ExprKind::IntLit(0), Ty::Int(IntTy::U64)),
            value: expr(ExprKind::IntLit(1), Ty::Int(IntTy::U8)),
        };
        let error = lower_stmt_erasing(&mut ctx, &wrong_store)
            .expect_err("Boolean array stores require Boolean values");
        assert!(error.starts_with("svm.sink_type:"), "{error}");
    }

    #[test]
    fn boolean_literal_evaluates_trapping_elements_before_allocation() {
        let program = empty_program();
        let array_ty = Ty::array(Ty::Bool);
        let mut ctx = LowerCtx::bare(&program);
        ctx.insert_local("source", array_ty.clone(), false, true)
            .unwrap();
        let trapping_read = expr(
            ExprKind::Index {
                array: "source".into(),
                array_span: Span::new(0, 0),
                index: Box::new(expr(ExprKind::IntLit(7), Ty::Int(IntTy::U64))),
            },
            Ty::Bool,
        );
        let literal = expr(ExprKind::ArrayLit(vec![trapping_read]), array_ty.clone());
        let lowered = lower_fresh_bool_array_bind(&ctx, "copy", array_ty, &literal).unwrap();
        let element = lowered
            .find("(.assign \"_bool_lit_copy_0\" (.index \"source\"")
            .expect("element read must be materialized");
        let allocation = lowered
            .find("(.assign \"copy\" (.allocArray")
            .expect("literal allocation must be materialized");
        assert!(
            element < allocation,
            "a trapping literal element must execute before allocation: {lowered}"
        );
    }

    #[test]
    fn named_array_operations_resolve_their_checked_local_type() {
        let program = empty_program();
        let array_ty = Ty::array(Ty::Int(IntTy::U8));
        let mut ctx = LowerCtx::bare(&program);
        ctx.insert_local("bytes", array_ty, true, true).unwrap();
        let index_operand = || expr(ExprKind::IntLit(0), Ty::Int(IntTy::U64));
        let index = |array: &str, operand: Expr, ty: Option<Ty>| Expr {
            kind: ExprKind::Index {
                array: array.into(),
                array_span: Span::new(0, 0),
                index: Box::new(operand),
            },
            span: Span::new(0, 0),
            ty,
        };

        let valid_index = index("bytes", index_operand(), Some(Ty::Int(IntTy::U8)));
        validate_expr_payloads(&ctx, &valid_index).expect("coherent integer index preflight");
        assert_eq!(
            lower_expr(&ctx, &valid_index).unwrap(),
            "(.index \"bytes\" (.intLit .u64 0))"
        );

        let malformed_indices = [
            (
                index("bytes", index_operand(), Some(Ty::Int(IntTy::I32))),
                "svm.array_index_result_type:",
            ),
            (
                index(
                    "bytes",
                    expr(ExprKind::IntLit(0), Ty::Int(IntTy::I32)),
                    Some(Ty::Int(IntTy::U8)),
                ),
                "svm.sink_type:",
            ),
            (
                index("missing", index_operand(), Some(Ty::Int(IntTy::U8))),
                "svm.local_type:",
            ),
        ];
        for (value, diagnostic) in &malformed_indices {
            let preflight = validate_expr_payloads(&ctx, value)
                .expect_err("malformed index must fail SVM preflight");
            assert!(preflight.starts_with(*diagnostic), "{preflight}");
            let lowering = lower_expr(&ctx, value)
                .expect_err("direct index lowering must resolve the array place");
            assert!(lowering.starts_with(*diagnostic), "{lowering}");
        }

        let valid_len = expr(
            ExprKind::Len {
                array: "bytes".into(),
            },
            Ty::Int(IntTy::U64),
        );
        validate_expr_payloads(&ctx, &valid_len).expect("coherent integer length preflight");
        assert_eq!(lower_expr(&ctx, &valid_len).unwrap(), "(.len \"bytes\")");
        let wrong_len = expr(
            ExprKind::Len {
                array: "bytes".into(),
            },
            Ty::Int(IntTy::I32),
        );
        for error in [
            validate_expr_payloads(&ctx, &wrong_len).unwrap_err(),
            lower_expr(&ctx, &wrong_len).unwrap_err(),
        ] {
            assert!(error.starts_with("svm.array_len_result_type:"), "{error}");
        }
    }

    #[test]
    fn array_stores_and_bindings_recheck_destination_payloads() {
        let program = empty_program();
        let array_ty = Ty::array(Ty::Int(IntTy::U8));
        let allocation = expr(
            ExprKind::AllocArray {
                elem: Ty::Int(IntTy::U8),
                len: Box::new(expr(ExprKind::IntLit(2), Ty::Int(IntTy::U64))),
                init: Box::new(expr(ExprKind::IntLit(0), Ty::Int(IntTy::U8))),
            },
            array_ty.clone(),
        );
        let store = |index: Expr, value: Expr| Stmt::Store {
            array: "bytes".into(),
            array_span: Span::new(0, 0),
            index,
            value,
        };
        let valid_store = store(
            expr(ExprKind::IntLit(0), Ty::Int(IntTy::U64)),
            expr(ExprKind::IntLit(9), Ty::Int(IntTy::U8)),
        );
        let valid_function = checked_fn(
            Ty::Int(IntTy::U64),
            vec![
                Stmt::Decl {
                    ty: array_ty.clone(),
                    name: "bytes".into(),
                    name_span: Span::new(0, 0),
                    init: Some(allocation.clone()),
                    mutable: true,
                },
                valid_store.clone(),
                Stmt::Return {
                    value: Some(expr(
                        ExprKind::Len {
                            array: "bytes".into(),
                        },
                        Ty::Int(IntTy::U64),
                    )),
                    span: Span::new(0, 0),
                },
            ],
        );
        lower_fn(&program, &valid_function).expect("existing integer-array lowering remains valid");
        let mut ctx = LowerCtx::bare(&program);
        ctx.insert_local("bytes", array_ty.clone(), true, true)
            .unwrap();
        assert_eq!(
            lower_stmt_erasing(&mut ctx, &valid_store).unwrap(),
            Some("(.store \"bytes\" (.intLit .u64 0) (.intLit .u8 9))".into())
        );

        let bad_index = store(
            expr(ExprKind::IntLit(0), Ty::Int(IntTy::I32)),
            expr(ExprKind::IntLit(9), Ty::Int(IntTy::U8)),
        );
        let bad_value = store(
            expr(ExprKind::IntLit(0), Ty::Int(IntTy::U64)),
            expr(ExprKind::IntLit(9), Ty::Int(IntTy::I32)),
        );
        for (statement, diagnostic) in [
            (&bad_index, "svm.sink_type:"),
            (&bad_value, "svm.sink_type:"),
        ] {
            let mut preflight_ctx = ctx.clone();
            let preflight =
                validate_stmt_payloads(&mut preflight_ctx, std::slice::from_ref(statement))
                    .expect_err("malformed store must fail SVM preflight");
            assert!(preflight.starts_with(diagnostic), "{preflight}");
            let mut lowering_ctx = ctx.clone();
            let lowering = lower_stmt_erasing(&mut lowering_ctx, statement)
                .expect_err("direct store lowering must re-check operands");
            assert!(lowering.starts_with(diagnostic), "{lowering}");
        }

        let mismatched_binding = checked_fn(
            Ty::Unit,
            vec![Stmt::Decl {
                ty: array_ty.clone(),
                name: "bytes".into(),
                name_span: Span::new(0, 0),
                init: Some(expr(
                    ExprKind::AllocArray {
                        elem: Ty::Int(IntTy::I32),
                        len: Box::new(expr(ExprKind::IntLit(2), Ty::Int(IntTy::U64))),
                        init: Box::new(expr(ExprKind::IntLit(0), Ty::Int(IntTy::I32))),
                    },
                    Ty::array(Ty::Int(IntTy::I32)),
                )),
                mutable: false,
            }],
        );
        let error = lower_fn(&program, &mismatched_binding)
            .expect_err("array declaration and initializer must agree exactly");
        assert!(error.starts_with("svm.sink_type:"), "{error}");

        let array_return = |returned_ty: Ty| {
            checked_fn(
                array_ty.clone(),
                vec![
                    Stmt::Decl {
                        ty: array_ty.clone(),
                        name: "bytes".into(),
                        name_span: Span::new(0, 0),
                        init: Some(allocation.clone()),
                        mutable: false,
                    },
                    Stmt::Return {
                        value: Some(expr(ExprKind::Var("bytes".into()), returned_ty)),
                        span: Span::new(0, 0),
                    },
                ],
            )
        };
        lower_fn(&program, &array_return(array_ty.clone()))
            .expect("coherent integer-array return remains lowerable");
        let wrong_return = array_return(Ty::array(Ty::Int(IntTy::I32)));
        let error = lower_fn(&program, &wrong_return)
            .expect_err("array result annotations must match the function return type");
        assert!(error.starts_with("svm.local_type:"), "{error}");
    }

    #[test]
    fn array_sinks_reject_forged_scalar_array_crossings() {
        let program = empty_program();
        let array_ty = Ty::array(Ty::Int(IntTy::U8));
        let allocation = || {
            expr(
                ExprKind::AllocArray {
                    elem: Ty::Int(IntTy::U8),
                    len: Box::new(expr(ExprKind::IntLit(1), Ty::Int(IntTy::U64))),
                    init: Box::new(expr(ExprKind::IntLit(0), Ty::Int(IntTy::U8))),
                },
                array_ty.clone(),
            )
        };
        let rejects = |function: &Fn| {
            let preflight = lower_fn(&program, function)
                .expect_err("a forged scalar/array sink must fail preflight");
            assert!(preflight.starts_with("svm.sink_type:"), "{preflight}");
            let mut ctx = LowerCtx::for_function(&program, function).unwrap();
            let direct = lower_block(&mut ctx, &function.body)
                .expect_err("direct lowering must re-check scalar/array sinks");
            assert!(direct.starts_with("svm.sink_type:"), "{direct}");
        };

        rejects(&checked_fn(
            Ty::Unit,
            vec![Stmt::Decl {
                ty: Ty::Int(IntTy::I32),
                name: "scalar".into(),
                name_span: Span::new(0, 0),
                init: Some(allocation()),
                mutable: false,
            }],
        ));
        rejects(&checked_fn(
            Ty::Unit,
            vec![
                Stmt::Decl {
                    ty: Ty::Int(IntTy::I32),
                    name: "scalar".into(),
                    name_span: Span::new(0, 0),
                    init: Some(expr(ExprKind::IntLit(0), Ty::Int(IntTy::I32))),
                    mutable: true,
                },
                Stmt::Assign {
                    name: "scalar".into(),
                    name_span: Span::new(0, 0),
                    value: allocation(),
                },
            ],
        ));
        rejects(&checked_fn(
            Ty::Int(IntTy::I32),
            vec![Stmt::Return {
                value: Some(allocation()),
                span: Span::new(0, 0),
            }],
        ));
        let forged_array_var = checked_fn(
            Ty::Unit,
            vec![
                Stmt::Decl {
                    ty: array_ty.clone(),
                    name: "bytes".into(),
                    name_span: Span::new(0, 0),
                    init: Some(allocation()),
                    mutable: false,
                },
                Stmt::Decl {
                    ty: Ty::Int(IntTy::I32),
                    name: "scalar".into(),
                    name_span: Span::new(0, 0),
                    init: Some(expr(ExprKind::Var("bytes".into()), Ty::Int(IntTy::I32))),
                    mutable: false,
                },
            ],
        );
        let preflight = lower_fn(&program, &forged_array_var)
            .expect_err("a forged array variable annotation must fail preflight");
        assert!(preflight.starts_with("svm.local_type:"), "{preflight}");
        let mut ctx = LowerCtx::for_function(&program, &forged_array_var).unwrap();
        let direct = lower_block(&mut ctx, &forged_array_var.body)
            .expect_err("direct lowering must resolve the variable annotation");
        assert!(direct.starts_with("svm.sink_type:"), "{direct}");
    }

    #[test]
    fn array_places_follow_source_order_and_scopes() {
        let program = empty_program();
        let array_ty = Ty::array(Ty::Int(IntTy::U8));
        let allocation = || {
            expr(
                ExprKind::AllocArray {
                    elem: Ty::Int(IntTy::U8),
                    len: Box::new(expr(ExprKind::IntLit(1), Ty::Int(IntTy::U64))),
                    init: Box::new(expr(ExprKind::IntLit(0), Ty::Int(IntTy::U8))),
                },
                array_ty.clone(),
            )
        };
        let length_decl = |name: &str, array: &str| Stmt::Decl {
            ty: Ty::Int(IntTy::U64),
            name: name.into(),
            name_span: Span::new(0, 0),
            init: Some(expr(
                ExprKind::Len {
                    array: array.into(),
                },
                Ty::Int(IntTy::U64),
            )),
            mutable: false,
        };
        let array_decl = |name: &str| Stmt::Decl {
            ty: array_ty.clone(),
            name: name.into(),
            name_span: Span::new(0, 0),
            init: Some(allocation()),
            mutable: false,
        };
        let rejects = |function: &Fn| {
            let preflight = lower_fn(&program, function)
                .expect_err("a future or out-of-scope array place must be rejected");
            assert!(preflight.starts_with("svm.local_type:"), "{preflight}");
            let mut ctx = LowerCtx::for_function(&program, function).unwrap();
            let direct = lower_block(&mut ctx, &function.body)
                .expect_err("direct lowering must preserve array place scope");
            assert!(direct.starts_with("svm.local_type:"), "{direct}");
        };

        rejects(&checked_fn(
            Ty::Unit,
            vec![length_decl("n", "later"), array_decl("later")],
        ));
        rejects(&checked_fn(
            Ty::Unit,
            vec![Stmt::If {
                cond: expr(ExprKind::BoolLit(true), Ty::Bool),
                then_block: vec![array_decl("branch_bytes")],
                else_block: Some(vec![length_decl("n", "branch_bytes")]),
            }],
        ));
        rejects(&checked_fn(
            Ty::Unit,
            vec![
                Stmt::If {
                    cond: expr(ExprKind::BoolLit(true), Ty::Bool),
                    then_block: vec![array_decl("branch_bytes")],
                    else_block: None,
                },
                length_decl("n", "branch_bytes"),
            ],
        ));
        rejects(&checked_fn(
            Ty::Unit,
            vec![
                array_decl("outer"),
                Stmt::Expose {
                    kw_span: Span::new(0, 0),
                    array: "outer".into(),
                    array_span: Span::new(0, 0),
                    mutable: false,
                    ptr: "ptr".into(),
                    ptr_span: Span::new(0, 0),
                    res: "mem".into(),
                    res_span: Span::new(0, 0),
                    body: vec![array_decl("loan_local")],
                },
                length_decl("n", "loan_local"),
            ],
        ));
    }

    #[test]
    fn local_names_remain_reserved_across_sibling_scopes() {
        let program = empty_program();
        let scalar = |name: &str| Stmt::Decl {
            ty: Ty::Int(IntTy::I32),
            name: name.into(),
            name_span: Span::new(0, 0),
            init: Some(expr(ExprKind::IntLit(0), Ty::Int(IntTy::I32))),
            mutable: false,
        };
        let function = checked_fn(
            Ty::Unit,
            vec![Stmt::If {
                cond: expr(ExprKind::BoolLit(true), Ty::Bool),
                then_block: vec![scalar("duplicate")],
                else_block: Some(vec![scalar("duplicate")]),
            }],
        );

        let error = lower_fn(&program, &function)
            .expect_err("function-wide unique names include sibling scopes");
        assert!(error.starts_with("svm.local_type: duplicate"), "{error}");
        let mut ctx = LowerCtx::for_function(&program, &function).unwrap();
        let direct = lower_block(&mut ctx, &function.body)
            .expect_err("direct lowering must reserve sibling-scope names");
        assert!(direct.starts_with("svm.local_type: duplicate"), "{direct}");
    }

    #[test]
    fn unsafe_array_local_remains_in_the_enclosing_scope() {
        let program = empty_program();
        let array_ty = Ty::array(Ty::Int(IntTy::U8));
        let allocation = expr(
            ExprKind::AllocArray {
                elem: Ty::Int(IntTy::U8),
                len: Box::new(expr(ExprKind::IntLit(1), Ty::Int(IntTy::U64))),
                init: Box::new(expr(ExprKind::IntLit(0), Ty::Int(IntTy::U8))),
            },
            array_ty.clone(),
        );
        let function = checked_fn(
            Ty::Unit,
            vec![
                Stmt::Unsafe {
                    kw_span: Span::new(0, 0),
                    body: vec![Stmt::Decl {
                        ty: array_ty,
                        name: "bytes".into(),
                        name_span: Span::new(0, 0),
                        init: Some(allocation),
                        mutable: false,
                    }],
                },
                Stmt::Decl {
                    ty: Ty::Int(IntTy::U64),
                    name: "n".into(),
                    name_span: Span::new(0, 0),
                    init: Some(expr(
                        ExprKind::Len {
                            array: "bytes".into(),
                        },
                        Ty::Int(IntTy::U64),
                    )),
                    mutable: false,
                },
            ],
        );

        lower_fn(&program, &function)
            .expect("unsafe is a marker, so its valid array local remains active afterward");
    }

    #[test]
    fn branch_and_exposure_flow_preserve_definite_initialization() {
        let program = empty_program();
        let scalar_decl = || Stmt::Decl {
            ty: Ty::Int(IntTy::I32),
            name: "value".into(),
            name_span: Span::new(0, 0),
            init: None,
            mutable: true,
        };
        let assign = |value| Stmt::Assign {
            name: "value".into(),
            name_span: Span::new(0, 0),
            value: expr(ExprKind::IntLit(value), Ty::Int(IntTy::I32)),
        };
        let return_value = || Stmt::Return {
            value: Some(expr(ExprKind::Var("value".into()), Ty::Int(IntTy::I32))),
            span: Span::new(0, 0),
        };
        let branch = |else_block| Stmt::If {
            cond: expr(ExprKind::BoolLit(true), Ty::Bool),
            then_block: vec![assign(1)],
            else_block,
        };

        lower_fn(
            &program,
            &checked_fn(
                Ty::Int(IntTy::I32),
                vec![scalar_decl(), branch(Some(vec![assign(2)])), return_value()],
            ),
        )
        .expect("both fallthrough arms initialize the outer scalar");

        lower_fn(
            &program,
            &checked_fn(
                Ty::Int(IntTy::I32),
                vec![
                    scalar_decl(),
                    Stmt::If {
                        cond: expr(ExprKind::BoolLit(true), Ty::Bool),
                        then_block: vec![Stmt::Return {
                            value: Some(expr(ExprKind::IntLit(7), Ty::Int(IntTy::I32))),
                            span: Span::new(0, 0),
                        }],
                        else_block: Some(vec![assign(2)]),
                    },
                    return_value(),
                ],
            ),
        )
        .expect("only the arm reaching the merge must initialize the scalar");

        let one_arm = checked_fn(
            Ty::Int(IntTy::I32),
            vec![scalar_decl(), branch(None), return_value()],
        );
        assert!(
            lower_fn(&program, &one_arm)
                .expect_err("an implicit fallthrough arm preserves uninitialized state")
                .contains("uninitialized")
        );

        let array_ty = Ty::array(Ty::Int(IntTy::U8));
        let allocation = expr(
            ExprKind::AllocArray {
                elem: Ty::Int(IntTy::U8),
                len: Box::new(expr(ExprKind::IntLit(1), Ty::Int(IntTy::U64))),
                init: Box::new(expr(ExprKind::IntLit(0), Ty::Int(IntTy::U8))),
            },
            array_ty.clone(),
        );
        let expose = Stmt::Expose {
            kw_span: Span::new(0, 0),
            array: "bytes".into(),
            array_span: Span::new(0, 0),
            mutable: false,
            ptr: "ptr".into(),
            ptr_span: Span::new(0, 0),
            res: "mem".into(),
            res_span: Span::new(0, 0),
            body: vec![assign(3)],
        };
        lower_fn(
            &program,
            &checked_fn(
                Ty::Int(IntTy::I32),
                vec![
                    scalar_decl(),
                    Stmt::Decl {
                        ty: array_ty,
                        name: "bytes".into(),
                        name_span: Span::new(0, 0),
                        init: Some(allocation),
                        mutable: false,
                    },
                    expose,
                    return_value(),
                ],
            ),
        )
        .expect("an exposure body executes exactly once and initializes outer locals");
    }

    #[test]
    fn exposure_rejects_nested_return_before_generated_cleanup() {
        let program = empty_program();
        let array_ty = Ty::array(Ty::Int(IntTy::U8));
        let function = checked_fn(
            Ty::Int(IntTy::I32),
            vec![
                Stmt::Decl {
                    ty: array_ty.clone(),
                    name: "bytes".into(),
                    name_span: Span::new(0, 0),
                    init: Some(expr(
                        ExprKind::AllocArray {
                            elem: Ty::Int(IntTy::U8),
                            len: Box::new(expr(ExprKind::IntLit(1), Ty::Int(IntTy::U64))),
                            init: Box::new(expr(ExprKind::IntLit(0), Ty::Int(IntTy::U8))),
                        },
                        array_ty,
                    )),
                    mutable: false,
                },
                Stmt::Expose {
                    kw_span: Span::new(0, 0),
                    array: "bytes".into(),
                    array_span: Span::new(0, 0),
                    mutable: false,
                    ptr: "ptr".into(),
                    ptr_span: Span::new(0, 0),
                    res: "mem".into(),
                    res_span: Span::new(0, 0),
                    body: vec![Stmt::Unsafe {
                        kw_span: Span::new(0, 0),
                        body: vec![Stmt::Return {
                            value: Some(expr(ExprKind::IntLit(1), Ty::Int(IntTy::I32))),
                            span: Span::new(0, 0),
                        }],
                    }],
                },
            ],
        );
        assert!(
            lower_fn(&program, &function)
                .expect_err("return cannot bypass exposure copyback/free")
                .starts_with("svm.expose_return:")
        );
    }

    #[test]
    fn nested_scalar_vars_follow_source_order() {
        let program = empty_program();
        let array_ty = Ty::array(Ty::Int(IntTy::U8));
        let function = checked_fn(
            Ty::Unit,
            vec![
                Stmt::Decl {
                    ty: array_ty.clone(),
                    name: "bytes".into(),
                    name_span: Span::new(0, 0),
                    init: Some(expr(
                        ExprKind::AllocArray {
                            elem: Ty::Int(IntTy::U8),
                            len: Box::new(expr(ExprKind::Var("later".into()), Ty::Int(IntTy::U64))),
                            init: Box::new(expr(ExprKind::IntLit(0), Ty::Int(IntTy::U8))),
                        },
                        array_ty,
                    )),
                    mutable: false,
                },
                Stmt::Decl {
                    ty: Ty::Int(IntTy::U64),
                    name: "later".into(),
                    name_span: Span::new(0, 0),
                    init: Some(expr(ExprKind::IntLit(1), Ty::Int(IntTy::U64))),
                    mutable: false,
                },
            ],
        );
        for error in [
            lower_fn(&program, &function).unwrap_err(),
            lower_block(
                &mut LowerCtx::for_function(&program, &function).unwrap(),
                &function.body,
            )
            .unwrap_err(),
        ] {
            assert!(error.starts_with("svm.local_type:"), "{error}");
        }
    }

    #[test]
    fn sealed_operation_arity_scope_and_result_types_fail_closed() {
        let program = empty_program();
        let empty_raw = expr(
            ExprKind::RawOp {
                op: RawOp::Store8,
                op_span: Span::new(0, 0),
                args: Vec::new(),
            },
            Ty::Unit,
        );
        let empty_device = expr(
            ExprKind::DeviceOp {
                op: DeviceOp::UartWrite,
                op_span: Span::new(0, 0),
                args: Vec::new(),
            },
            Ty::Unit,
        );
        for malformed in [empty_raw, empty_device] {
            let function = checked_fn(Ty::Unit, vec![Stmt::ExprStmt(malformed)]);
            lower_fn(&program, &function).expect_err("empty sealed call must not panic");
            lower_block(
                &mut LowerCtx::for_function(&program, &function).unwrap(),
                &function.body,
            )
            .expect_err("direct empty sealed call lowering must not panic");
        }

        let forged_profile = expr(
            ExprKind::ResOp {
                op: ResOp::TestUart,
                op_span: Span::new(0, 0),
                args: vec![expr(ExprKind::IntLit(0), Ty::Int(IntTy::U64))],
            },
            Ty::Unit,
        );
        let function = checked_fn(Ty::Unit, vec![Stmt::ExprStmt(forged_profile)]);
        for error in [
            lower_fn(&program, &function).unwrap_err(),
            lower_block(
                &mut LowerCtx::for_function(&program, &function).unwrap(),
                &function.body,
            )
            .unwrap_err(),
        ] {
            assert!(error.starts_with("svm.sink_type:"), "{error}");
        }

        let forged_release = checked_fn(
            Ty::Unit,
            vec![
                Stmt::StaticAlloc {
                    kw_span: Span::new(0, 0),
                    size: expr(ExprKind::IntLit(8), Ty::Int(IntTy::U64)),
                    ptr: "ptr".into(),
                    ptr_span: Span::new(0, 0),
                    res: "mem".into(),
                    res_span: Span::new(0, 0),
                },
                Stmt::Decl {
                    ty: Ty::Res(ResKind::SystemDealloc),
                    name: "release".into(),
                    name_span: Span::new(0, 0),
                    init: Some(expr(
                        ExprKind::ResOp {
                            op: ResOp::AllocatorCreate,
                            op_span: Span::new(0, 0),
                            args: vec![Expr {
                                kind: ExprKind::Var("mem".into()),
                                span: Span::new(0, 0),
                                ty: None,
                            }],
                        },
                        Ty::Res(ResKind::SystemDealloc),
                    )),
                    mutable: false,
                },
            ],
        );
        assert!(
            lower_fn(&program, &forged_release)
                .expect_err("allocator_create cannot forge release authority")
                .starts_with("svm.sink_type:")
        );
    }

    #[test]
    fn erased_resource_op_accepts_unannotated_resource_place() {
        let program = empty_program();
        let mut ctx = LowerCtx::bare(&program);
        ctx.insert_local("mem", Ty::Res(ResKind::RawSpan), true, true)
            .unwrap();
        let mem = Expr {
            kind: ExprKind::Var("mem".into()),
            span: Span::new(0, 0),
            // Resource variables take the checker's early-return path, so a
            // successfully checked operand intentionally has no cached type.
            ty: None,
        };
        ensure_erased_resource_operands_inert(&ctx, ResOp::AllocatorCreate, &[mem])
            .expect("allocator_create(resource_place) is runtime-inert");
    }

    #[test]
    fn erased_resource_op_rejects_effectful_operand() {
        let span = expr(
            ExprKind::Borrow {
                array: "mem".into(),
                field: None,
                mutable: true,
            },
            Ty::borrow(Mutability::Mut, Ty::Res(ResKind::RawSpan)),
        );
        let one = expr(ExprKind::IntLit(1), Ty::Int(IntTy::U64));
        let zero = expr(ExprKind::IntLit(0), Ty::Int(IntTy::U64));
        let division = expr(
            ExprKind::Binary {
                op: BinOp::Div,
                op_span: Span::new(0, 0),
                lhs: Box::new(one),
                rhs: Box::new(zero),
            },
            Ty::Int(IntTy::U64),
        );

        let program = empty_program();
        let mut ctx = LowerCtx::bare(&program);
        ctx.insert_local("mem", Ty::Res(ResKind::RawSpan), true, true)
            .unwrap();
        let error = lower_resource_op_stmt(&ctx, ResOp::SplitOff, &[span, division])
            .expect_err("split_off(&mut mem, 1 / 0) must not disappear");
        assert!(error.contains("`split_off` operand 2"), "{error}");
    }
}
