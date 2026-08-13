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

use crate::ast::*;
use crate::interp::{MmioEvent, ObservedRun, RtVal};
use std::collections::{HashMap, HashSet};

#[derive(Clone, Copy)]
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
            return_ty: Some(function.ret),
        };
        for parameter in &function.params {
            ctx.insert_local(&parameter.name, parameter.ty, false, true)?;
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
        self.locals.get(name).copied()
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
        if matches!(param.ty, Ty::AffineOption(_)) {
            return Err(affine_option_unsupported(
                param.ty,
                &format!("parameter `{}`", param.name),
            ));
        }
        validate_ty_payload(param.ty, &format!("parameter `{}`", param.name))?;
        if bool_array_ty(param.ty) {
            return Err(format!(
                "svm.bool_array_position_unsupported: parameter `{}` is Boolean-array-typed; Boolean arrays are owned locals only",
                param.name
            ));
        }
        if matches!(param.ty, Ty::Option(_)) {
            return Err(format!(
                "svm.option_position_unsupported: parameter `{}` is option-typed; \
                 ordinary options are returns and locals only",
                param.name
            ));
        }
    }
    if matches!(f.ret, Ty::AffineOption(_)) {
        return Err(affine_option_unsupported(
            f.ret,
            &format!("return type of `{}`", f.name),
        ));
    }
    validate_ty_payload(f.ret, &format!("return type of `{}`", f.name))?;
    if bool_array_ty(f.ret) {
        return Err(format!(
            "svm.bool_array_position_unsupported: `{}` returns a Boolean array; Boolean arrays are owned locals only",
            f.name
        ));
    }
    if f.ret.is_resource() {
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

fn validate_ty_payload(ty: Ty, context: &str) -> Result<(), String> {
    match ty {
        Ty::AffineOption(_) => Err(affine_option_unsupported(ty, context)),
        Ty::Array(payload, _) => validate_array_payload(payload, context),
        Ty::Option(payload) => validate_option_payload(payload, context),
        Ty::Param(_) | Ty::Int(IntTy::TParam(_)) | Ty::Raw(IntTy::TParam(_)) => Err(format!(
            "svm.type_parameter_unsupported: {context} contains an unresolved type parameter"
        )),
        _ => Ok(()),
    }
}

fn affine_option_unsupported(ty: Ty, context: &str) -> String {
    debug_assert!(matches!(ty, Ty::AffineOption(_)));
    format!(
        "svm.affine_option_unsupported: {context} has type `{}`; affine options require atomic ownership semantics that are not yet modeled by the formal SVM",
        ty.name()
    )
}

fn affine_option_take_unsupported(option: &str) -> String {
    format!(
        "svm.affine_option_unsupported: `.take` of affine option local `{option}` requires an atomic ownership transition that is not yet modeled by the formal SVM"
    )
}

fn validate_array_payload(payload: ValueTy, context: &str) -> Result<(), String> {
    match payload {
        ValueTy::Int(integer) if !matches!(integer, IntTy::TParam(_)) => Ok(()),
        ValueTy::Bool => Ok(()),
        _ => Err(format!(
            "svm.aggregate_payload_unsupported: {context} has array payload `{}`; \
             the SVM currently lowers only concrete integer and Boolean payloads",
            payload.name()
        )),
    }
}

fn array_element_ty(payload: ValueTy, context: &str) -> Result<Ty, String> {
    validate_array_payload(payload, context)?;
    match payload {
        ValueTy::Int(integer) if !matches!(integer, IntTy::TParam(_)) => Ok(Ty::Int(integer)),
        ValueTy::Bool => Ok(Ty::Bool),
        _ => unreachable!("validate_array_payload accepted an unsupported payload"),
    }
}

fn bool_array_ty(ty: Ty) -> bool {
    matches!(ty, Ty::Array(ValueTy::Bool, _))
}

fn owned_bool_array_ty(ty: Ty) -> bool {
    matches!(ty, Ty::Array(ValueTy::Bool, Mutability::Owned))
}

fn require_expr_annotation(
    expr: &Expr,
    expected: Ty,
    diagnostic: &str,
    context: &str,
) -> Result<(), String> {
    match expr.ty {
        Some(actual) if actual == expected => Ok(()),
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

fn resolve_array(
    ctx: &LowerCtx<'_>,
    array: &str,
    operation: &str,
) -> Result<(ValueTy, Mutability, bool), String> {
    let binding = ctx.initialized_local(array, operation)?;
    let Ty::Array(payload, mutability) = binding.ty else {
        return Err(format!(
            "svm.array_place_type: {operation} names `{array}` of type `{}`; expected an array",
            binding.ty.name()
        ));
    };
    validate_array_payload(payload, &format!("{operation} of `{array}`"))?;
    Ok((payload, mutability, binding.mutable))
}

fn validate_array_index(
    ctx: &LowerCtx<'_>,
    expr: &Expr,
    array: &str,
    index: &Expr,
) -> Result<(), String> {
    let (payload, _, _) = resolve_array(ctx, array, "array index")?;
    let element = array_element_ty(payload, "array index result")?;
    require_expr_annotation(
        expr,
        element,
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
    elem: ValueTy,
    len: &Expr,
    init: &Expr,
) -> Result<(), String> {
    let element = array_element_ty(elem, "alloc_array")?;
    require_expr_annotation(
        expr,
        Ty::Array(elem, Mutability::Owned),
        "svm.array_alloc_result_type",
        "alloc_array result",
    )?;
    validate_sink_type(ctx, Ty::Int(IntTy::U64), len, "alloc_array length")?;
    validate_sink_type(ctx, element, init, "alloc_array initializer")?;
    validate_expr_payloads(ctx, len)?;
    validate_expr_payloads(ctx, init)
}

fn validate_array_literal_len(payload: ValueTy, len: usize) -> Result<(), String> {
    if payload == ValueTy::Bool && len > 50_000_000 {
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
    let payload = match expr.ty {
        Some(Ty::Array(payload, Mutability::Owned)) => payload,
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
    let element = array_element_ty(payload, "array literal")?;
    validate_array_literal_len(payload, elements.len())?;
    for (index, value) in elements.iter().enumerate() {
        validate_sink_type(
            ctx,
            element,
            value,
            &format!("array literal element {}", index + 1),
        )?;
        validate_expr_payloads(ctx, value)?;
    }
    Ok(())
}

/// Boolean arrays have no call ABI or general first-class transport in G1.5.
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
    if !owned_bool_array_ty(declared_ty) {
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
            validate_alloc_array(ctx, initializer, *elem, len, value)?;
        }
        ExprKind::ArrayLit(elements) => validate_array_literal(ctx, initializer, elements)?,
        ExprKind::OptTake { option, .. } => {
            return Err(affine_option_take_unsupported(option));
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
    if mutability == Mutability::Shared || (mutability == Mutability::Owned && !declared_mutable) {
        return Err(format!(
            "svm.array_store_place: array store targets non-writable `{array}` of type `{}`",
            Ty::Array(payload, mutability).name()
        ));
    }
    validate_sink_type(ctx, Ty::Int(IntTy::U64), index, "array store index")?;
    validate_sink_type(
        ctx,
        array_element_ty(payload, "array store value")?,
        value,
        "array store value",
    )?;
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
    Ok(function.ret)
}

/// Recover the type supplied by the expression's checked shape instead of
/// trusting its cached annotation as a second, forgeable source of truth.
fn semantic_expr_ty(
    ctx: &LowerCtx<'_>,
    expr: &Expr,
    expected: Ty,
    context: &str,
) -> Result<Ty, String> {
    if let Some(ty @ Ty::AffineOption(_)) = expr.ty {
        return Err(affine_option_unsupported(ty, context));
    }
    let semantic = match &expr.kind {
        ExprKind::Var(name) => {
            let ty = ctx.initialized_local(name, context)?.ty;
            if bool_array_ty(ty) {
                return Err(format!(
                    "svm.bool_array_transport_unsupported: {context} moves Boolean array local `{name}`; Boolean arrays may only be accessed by index or length"
                ));
            }
            ty
        }
        ExprKind::AllocArray { elem, .. } => Ty::Array(*elem, Mutability::Owned),
        ExprKind::ArrayLit(_) => match expr.ty {
            Some(ty @ Ty::Array(_, Mutability::Owned)) => ty,
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
        },
        ExprKind::Call { callee, .. } => call_return_ty(ctx, callee)?,
        ExprKind::ResOp { op, args, .. } => semantic_res_op_ty(ctx, *op, args, expected)?,
        ExprKind::RawOp { op, args, .. } => validate_raw_op(ctx, *op, args)?,
        ExprKind::DeviceOp { op, args, .. } => validate_device_op(ctx, *op, args)?,
        ExprKind::IntLit(value) => match expr.ty {
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
        },
        ExprKind::BoolLit(_) => Ty::Bool,
        ExprKind::OptTake { option, .. } => {
            return Err(affine_option_take_unsupported(option));
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
                    operand.ty.unwrap_or(expected),
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
                    lhs.ty.unwrap_or(expected),
                    &format!("{context} left operand"),
                )?;
                let right = semantic_expr_ty(
                    ctx,
                    rhs,
                    rhs.ty.unwrap_or(left),
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
                arg.ty.unwrap_or(Ty::Int(*target)),
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
            array_element_ty(payload, "array index result")?
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
                SvmOptionRepr::Ordinary(payload) => ordinary_option_payload_ty(payload)?,
                SvmOptionRepr::RawRecord(record) => Ty::RawRecord(record),
            };
            validate_sink_type(ctx, payload, inner, &format!("{context} option payload"))?;
            expr.ty.expect("classified option result")
        }
        ExprKind::NoneE => {
            svm_option_repr(expr, "none")?;
            expr.ty.expect("classified option result")
        }
        ExprKind::IsSome { operand } | ExprKind::OptValue { operand } => {
            let operand_ty = semantic_expr_ty(
                ctx,
                operand,
                operand.ty.unwrap_or(Ty::Unit),
                &format!("{context} option operand"),
            )?;
            match (&expr.kind, operand_ty) {
                (ExprKind::IsSome { .. }, Ty::Option(_) | Ty::OptionRaw(_)) => Ty::Bool,
                (ExprKind::OptValue { .. }, Ty::Option(payload)) => {
                    ordinary_option_payload_ty(payload)?
                }
                (ExprKind::OptValue { .. }, Ty::OptionRaw(record)) => Ty::RawRecord(record),
                _ => {
                    return Err(format!(
                        "svm.option_accessor_operand: {context} operand is `{}`; expected an option",
                        operand_ty.name()
                    ));
                }
            }
        }
        _ => {
            if matches!(expr.ty, Some(Ty::Array(..))) {
                return Err(format!(
                    "svm.sink_type: {context} has an expression shape that cannot produce an array"
                ));
            }
            match expr.ty {
                Some(actual) => actual,
                None if expected.is_resource()
                    && matches!(
                        expr.kind,
                        ExprKind::SelfField { .. } | ExprKind::Borrow { .. }
                    ) =>
                {
                    expected
                }
                None => {
                    return Err(format!(
                        "svm.sink_type: {context} carries no checked result type"
                    ));
                }
            }
        }
    };
    if let Some(annotation) = expr.ty {
        if annotation != semantic {
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
    if bool_array_ty(binding.ty) {
        return Err(format!(
            "svm.bool_array_transport_unsupported: {operation} moves Boolean array local `{name}`; Boolean arrays may only be accessed by index or length"
        ));
    }
    match expr.ty {
        Some(annotation) if annotation != binding.ty => Err(format!(
            "svm.local_type: {operation} names `{name}` of type `{}` but is annotated `{}`",
            binding.ty.name(),
            annotation.name()
        )),
        None if !binding.ty.is_resource() => Err(format!(
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
    if expr.ty != Some(declared_field.ty) {
        return Err(format!(
            "svm.record_field_type: `{}.{field}` has type `{}` but is annotated `{}`",
            record.name,
            declared_field.ty.name(),
            expr.ty.map_or_else(|| "<missing>".into(), Ty::name)
        ));
    }
    Ok(declared_field.ty)
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
            field.ty,
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
    let actual = semantic_expr_ty(ctx, value, expected, context)?;
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
    if matches!(
        ctx.local(name).map(|binding| binding.ty),
        Some(Ty::Array(..))
    ) {
        return Err(format!(
            "svm.array_rebind_unsupported: checked array `{name}` is rebound; arrays may only be mutated by element store"
        ));
    }
    Ok(())
}

fn validate_return(ctx: &LowerCtx<'_>, value: &Expr) -> Result<(), String> {
    let Some(expected) = ctx.return_ty else {
        return Err("svm.sink_type: return lowering has no function result type".into());
    };
    if expected.is_resource() {
        return Err(
            "svm.resource_return_unsupported: erased authority has no SVM result representation"
                .into(),
        );
    }
    validate_sink_type(ctx, expected, value, "return value")
}

fn validate_array_exposure(ctx: &LowerCtx<'_>, array: &str, mutable: bool) -> Result<(), String> {
    let (payload, mutability, declared_mutable) = resolve_array(ctx, array, "array exposure")?;
    if payload != ValueTy::Int(IntTy::U8) {
        return Err(format!(
            "svm.array_expose_type: exposure names `{array}` of type `{}`; only byte arrays have SVM exposure semantics",
            Ty::Array(payload, mutability).name()
        ));
    }
    if mutable
        && (mutability == Mutability::Shared
            || (mutability == Mutability::Owned && !declared_mutable))
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

fn validate_option_payload(payload: ValueTy, context: &str) -> Result<(), String> {
    match payload {
        ValueTy::Int(integer) if !matches!(integer, IntTy::TParam(_)) => Ok(()),
        ValueTy::Bool => Ok(()),
        _ => Err(format!(
            "svm.aggregate_payload_unsupported: {context} has option payload `{}`; \
             the SVM currently lowers only concrete integer and Boolean option payloads",
            payload.name()
        )),
    }
}

#[derive(Clone, Copy)]
enum SvmOptionRepr {
    Ordinary(ValueTy),
    RawRecord(usize),
}

/// Classify an option constructor from its checked outer annotation.  The
/// Lean syntax is deliberately untyped, so accepting a missing or unrelated
/// annotation here would let a malformed public AST manufacture a value that
/// the source checker could never produce.
fn svm_option_repr(expr: &Expr, constructor: &str) -> Result<SvmOptionRepr, String> {
    match expr.ty {
        Some(Ty::Option(payload)) => {
            validate_option_payload(payload, &format!("`{constructor}` result"))?;
            Ok(SvmOptionRepr::Ordinary(payload))
        }
        Some(Ty::OptionRaw(record)) => Ok(SvmOptionRepr::RawRecord(record)),
        Some(ty @ Ty::AffineOption(_)) => Err(affine_option_unsupported(
            ty,
            &format!("`{constructor}` result"),
        )),
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

fn ordinary_option_payload_ty(payload: ValueTy) -> Result<Ty, String> {
    match payload {
        ValueTy::Int(integer) if !matches!(integer, IntTy::TParam(_)) => Ok(Ty::Int(integer)),
        ValueTy::Bool => Ok(Ty::Bool),
        _ => Err(format!(
            "svm.aggregate_payload_unsupported: option constructor has payload `{}`; \
             the SVM currently lowers only concrete integer and Boolean option payloads",
            payload.name()
        )),
    }
}

fn validate_some_constructor(expr: &Expr, inner: &Expr) -> Result<SvmOptionRepr, String> {
    let repr = svm_option_repr(expr, "some")?;
    let expected = match repr {
        SvmOptionRepr::Ordinary(payload) => ordinary_option_payload_ty(payload)?,
        SvmOptionRepr::RawRecord(record) => Ty::RawRecord(record),
    };
    match inner.ty {
        Some(actual) if actual == expected => Ok(repr),
        Some(actual) => Err(format!(
            "svm.option_constructor_payload: `some(...)` is annotated `{}` but its payload has \
             type `{}`; malformed checked AST",
            expr.ty.expect("classified option result").name(),
            actual.name()
        )),
        None => Err(format!(
            "svm.option_constructor_payload: `some(...)` payload carries no type; \
             expected `{}` from the result annotation",
            expected.name()
        )),
    }
}

fn validate_option_accessor(
    expr: &Expr,
    operand: &Expr,
    value: bool,
) -> Result<SvmOptionRepr, String> {
    let accessor = if value { ".value" } else { ".is_some" };
    let repr = match operand.ty {
        Some(Ty::Option(payload)) => {
            validate_option_payload(payload, "option accessor operand")?;
            SvmOptionRepr::Ordinary(payload)
        }
        Some(Ty::OptionRaw(record)) => SvmOptionRepr::RawRecord(record),
        Some(ty @ Ty::AffineOption(_)) => {
            return Err(affine_option_unsupported(
                ty,
                &format!("`{accessor}` operand"),
            ));
        }
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
            SvmOptionRepr::Ordinary(payload) => ordinary_option_payload_ty(payload)?,
            SvmOptionRepr::RawRecord(record) => Ty::RawRecord(record),
        }
    } else {
        Ty::Bool
    };
    match expr.ty {
        Some(actual) if actual == expected => Ok(repr),
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
            if matches!(parameter.ty, Ty::AffineOption(_)) {
                return Err(affine_option_unsupported(
                    parameter.ty,
                    &format!("{context} parameter `{}`", parameter.name),
                ));
            }
            if bool_array_ty(parameter.ty) {
                return Err(format!(
                    "svm.bool_array_position_unsupported: {context} parameter `{}` is Boolean-array-typed; Boolean arrays are owned locals only",
                    parameter.name
                ));
            }
            if let Ty::Option(payload) = parameter.ty {
                validate_option_payload(payload, context)?;
                return Err(format!(
                    "svm.option_position_unsupported: {context} parameter `{}` is option-typed; \
                     ordinary options are returns and locals only",
                    parameter.name
                ));
            }
        }
        if matches!(function.ret, Ty::AffineOption(_)) {
            return Err(affine_option_unsupported(
                function.ret,
                &format!("{context} return type"),
            ));
        }
        if bool_array_ty(function.ret) {
            return Err(format!(
                "svm.bool_array_position_unsupported: {context} returns a Boolean array; Boolean arrays are owned locals only"
            ));
        }
        if trait_member {
            if let Ty::Option(payload) = function.ret {
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
            if matches!(field.ty, Ty::AffineOption(_)) {
                return Err(affine_option_unsupported(
                    field.ty,
                    &format!("class `{}.{}` field", class.name, field.name),
                ));
            }
            if bool_array_ty(field.ty) {
                return Err(format!(
                    "svm.bool_array_position_unsupported: class `{}.{}` has a Boolean-array-typed field; Boolean arrays are owned locals only",
                    class.name, field.name
                ));
            }
            if let Ty::Option(payload) = field.ty {
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
            if matches!(field.ty, Ty::AffineOption(_)) {
                return Err(affine_option_unsupported(
                    field.ty,
                    &format!("record `{}.{}` field", record.name, field.name),
                ));
            }
            if bool_array_ty(field.ty) {
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
            let field_layout = match field.ty {
                Ty::Int(integer) if !matches!(integer, IntTy::TParam(_)) => integer.layout(),
                Ty::RawRecord(_) | Ty::OptionRaw(_) => StorageLayout { size: 8, align: 8 },
                unsupported => {
                    return Err(format!(
                        "svm.record_schema_type: record `{}.{}` has unsupported field type `{}`",
                        record.name,
                        field.name,
                        unsupported.name()
                    ));
                }
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
                if matches!(ty, Ty::AffineOption(_)) {
                    return Err(affine_option_unsupported(
                        *ty,
                        &format!("declaration `{name}`"),
                    ));
                }
                validate_ty_payload(*ty, &format!("declaration `{name}`"))?;
                if bool_array_ty(*ty) {
                    let Some(init) = init else {
                        return Err(format!(
                            "svm.bool_array_fresh_local: Boolean array local `{name}` must be initialized by a fresh literal or allocation"
                        ));
                    };
                    validate_fresh_bool_array_initializer(ctx, *ty, init, name)?;
                } else if let Some(init) = init {
                    validate_expr_payloads(ctx, init)?;
                    validate_sink_type(ctx, *ty, init, &format!("initializer of `{name}`"))?;
                }
                ctx.insert_local(name, *ty, *mutable, init.is_some())?;
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
                validate_expr_payloads(ctx, value)?;
                validate_sink_type(ctx, binding.ty, value, &format!("assignment to `{name}`"))?;
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
                if matches!(ty, Ty::AffineOption(_)) {
                    return Err(affine_option_unsupported(
                        *ty,
                        &format!("inferred declaration `{name}`"),
                    ));
                }
                validate_ty_payload(*ty, &format!("inferred declaration `{name}`"))?;
                if bool_array_ty(*ty) {
                    validate_fresh_bool_array_initializer(ctx, *ty, init, name)?;
                } else {
                    validate_expr_payloads(ctx, init)?;
                    validate_sink_type(ctx, *ty, init, &format!("initializer of `{name}`"))?;
                }
                ctx.insert_local(name, *ty, *mutable, true)?;
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
    match call.ty {
        Some(actual) if actual == function.ret => {}
        Some(actual) => {
            return Err(format!(
                "svm.call_result_type: call to `{callee}` is annotated `{}`; callee returns `{}`",
                actual.name(),
                function.ret.name()
            ));
        }
        None => {
            return Err(format!(
                "svm.call_result_type: call to `{callee}` carries no result type; callee returns `{}`",
                function.ret.name()
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
    if function.ret.is_resource()
        || function
            .params
            .iter()
            .any(|parameter| parameter.ty.is_resource())
    {
        return Err(format!(
            "svm.call_resource_unsupported: `{callee}` has resource parameters or result; erased authority has no SVM call ABI"
        ));
    }
    for (index, (arg, parameter)) in args.iter().zip(&function.params).enumerate() {
        validate_sink_type(
            ctx,
            parameter.ty,
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
    if let Some(ty) = expr.ty {
        validate_ty_payload(ty, "expression annotation")?;
        if bool_array_ty(ty) && !matches!(&expr.kind, ExprKind::OptTake { .. }) {
            return Err(
                "svm.bool_array_position_unsupported: a Boolean-array-valued expression is only supported as the initializer of a fresh owned local"
                    .into(),
            );
        }
    }

    match &expr.kind {
        ExprKind::Index { array, index, .. } => {
            validate_array_index(ctx, expr, array, index)?;
        }
        ExprKind::AllocArray { elem, len, init } => {
            validate_alloc_array(ctx, expr, *elem, len, init)?;
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
                expr.ty.unwrap_or(Ty::Int(*target)),
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
            semantic_expr_ty(ctx, expr, expr.ty.unwrap_or(Ty::Unit), "option constructor")?;
            validate_expr_payloads(ctx, operand)?;
        }
        ExprKind::NoneE => {
            svm_option_repr(expr, "none")?;
        }
        ExprKind::IsSome { operand } => {
            validate_option_accessor(expr, operand, false)?;
            semantic_expr_ty(ctx, expr, Ty::Bool, "option is_some accessor")?;
            validate_expr_payloads(ctx, operand)?;
        }
        ExprKind::OptValue { operand } => {
            validate_option_accessor(expr, operand, true)?;
            semantic_expr_ty(
                ctx,
                expr,
                expr.ty.unwrap_or(Ty::Unit),
                "option value accessor",
            )?;
            validate_expr_payloads(ctx, operand)?;
        }
        ExprKind::OptTake { option, .. } => {
            return Err(affine_option_take_unsupported(option));
        }
        ExprKind::Unary { operand, .. } => {
            semantic_expr_ty(ctx, expr, expr.ty.unwrap_or(Ty::Unit), "unary expression")?;
            validate_expr_payloads(ctx, operand)?;
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            semantic_expr_ty(ctx, expr, expr.ty.unwrap_or(Ty::Unit), "binary expression")?;
            validate_expr_payloads(ctx, lhs)?;
            validate_expr_payloads(ctx, rhs)?;
        }
        ExprKind::ResOp { args, .. } => {
            semantic_expr_ty(
                ctx,
                expr,
                expr.ty.unwrap_or(Ty::Unit),
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
                expr.ty.unwrap_or(Ty::Unit),
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
                expr.ty.unwrap_or(Ty::Unit),
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
        ExprKind::TraitCall { args, .. } | ExprKind::MethodCall { args, .. } => {
            for arg in args {
                validate_expr_payloads(ctx, arg)?;
            }
        }
        ExprKind::SelfFieldIndex { index, .. } | ExprKind::ClassFieldIndex { index, .. } => {
            validate_expr_payloads(ctx, index)?;
        }
        ExprKind::Var(name) => {
            validate_local_var(ctx, expr, name, "variable expression")?;
        }
        ExprKind::IntLit(_) => {
            semantic_expr_ty(ctx, expr, expr.ty.unwrap_or(Ty::Unit), "integer literal")?;
        }
        ExprKind::BoolLit(_) => {
            semantic_expr_ty(ctx, expr, expr.ty.unwrap_or(Ty::Unit), "Boolean literal")?;
        }
        ExprKind::Borrow { array, .. } => {
            if ctx
                .local(array)
                .is_some_and(|binding| bool_array_ty(binding.ty))
            {
                return Err(format!(
                    "svm.bool_array_borrow_unsupported: Boolean array local `{array}` cannot be borrowed or transported"
                ));
            }
        }
        ExprKind::SelfField { .. }
        | ExprKind::SelfFieldLen { .. }
        | ExprKind::ClassField { .. }
        | ExprKind::ClassFieldLen { .. } => {}
        ExprKind::RecordField { obj, field, .. } => {
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
        .find(|parameter| matches!(parameter.ty, Ty::AffineOption(_)))
    {
        return Err(affine_option_unsupported(
            parameter.ty,
            &format!("parameter `{}`", parameter.name),
        ));
    }
    if matches!(f.ret, Ty::AffineOption(_)) {
        return Err(affine_option_unsupported(
            f.ret,
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
/// body⟩)`. Parameters must be machine values — borrows are outside the
/// machine (arrays are owned values; `&mut` reflection back to the
/// caller has no machine analog yet).
pub fn lower_fn_entry(program: &Program, f: &Fn) -> Result<String, String> {
    validate_program_option_positions(program)?;
    let mut validation_ctx = LowerCtx::for_function(program, f)?;
    validate_fn_payloads(&mut validation_ctx, f)?;
    let mut lowering_ctx = LowerCtx::for_function(program, f)?;
    for p in &f.params {
        match p.ty {
            Ty::Int(_) | Ty::Bool => {}
            Ty::Record(ri) | Ty::RawRecord(ri) | Ty::OptionRaw(ri) => {
                lowering_ctx.record(ri)?;
            }
            _ => {
                return Err(format!(
                    "parameter `{}`: its type is outside the SVM core subset (borrows and resources are scoped out)",
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
        } if bool_array_ty(*ty) => {
            let Some(initializer) = init else {
                return Err(format!(
                    "svm.bool_array_fresh_local: Boolean array local `{name}` must be initialized by a fresh literal or allocation"
                ));
            };
            let lowered = lower_fresh_bool_array_bind(ctx, name, *ty, initializer)?;
            ctx.insert_local(name, *ty, *mutable, true)?;
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
            ctx.insert_local(name, *ty, *mutable, false)?;
            None
        }
        Stmt::Decl {
            name,
            ty,
            mutable,
            init: Some(e),
            ..
        } if ty.is_resource() => {
            validate_sink_type(ctx, *ty, e, &format!("initializer of `{name}`"))?;
            let lowered = lower_erased_resource_bind(ctx, name, e)?;
            ctx.insert_local(name, *ty, *mutable, true)?;
            lowered
        }
        Stmt::Decl {
            name,
            ty,
            mutable,
            init: Some(e),
            ..
        } => {
            validate_sink_type(ctx, *ty, e, &format!("initializer of `{name}`"))?;
            let lowered = lower_bind(ctx, name, e)?;
            ctx.insert_local(name, *ty, *mutable, true)?;
            Some(lowered)
        }
        Stmt::VarDecl {
            name,
            init,
            ty: Some(ty),
            mutable,
            ..
        } if bool_array_ty(*ty) => {
            let lowered = lower_fresh_bool_array_bind(ctx, name, *ty, init)?;
            ctx.insert_local(name, *ty, *mutable, true)?;
            Some(lowered)
        }
        Stmt::VarDecl {
            name,
            init,
            ty: Some(ty),
            mutable,
            ..
        } if ty.is_resource() => {
            validate_sink_type(ctx, *ty, init, &format!("initializer of `{name}`"))?;
            let lowered = lower_erased_resource_bind(ctx, name, init)?;
            ctx.insert_local(name, *ty, *mutable, true)?;
            lowered
        }
        Stmt::VarDecl {
            name,
            init,
            ty: Some(ty),
            mutable,
            ..
        } => {
            validate_sink_type(ctx, *ty, init, &format!("initializer of `{name}`"))?;
            let lowered = lower_bind(ctx, name, init)?;
            ctx.insert_local(name, *ty, *mutable, true)?;
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
            validate_sink_type(ctx, binding.ty, value, &format!("assignment to `{name}`"))?;
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
                if e.ty != Some(result) {
                    return Err(format!(
                        "svm.raw_result_type: `{}` produces `{}` but is annotated `{}`",
                        op.name(),
                        result.name(),
                        e.ty.map_or_else(|| "<missing>".into(), Ty::name)
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
                if e.ty != Some(result) {
                    return Err(format!(
                        "svm.device_result_type: `{}` produces `{}` but is annotated `{}`",
                        op.name(),
                        result.name(),
                        e.ty.map_or_else(|| "<missing>".into(), Ty::name)
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
                    e.ty.unwrap_or(Ty::Unit),
                    "sealed resource expression statement",
                )?;
                lower_resource_op_stmt(ctx, *op, args)?
            }
            ExprKind::OptTake { option, .. } => {
                return Err(affine_option_take_unsupported(option));
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
            if !binding.ty.is_resource() {
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
                Ty::ResRef(kind, source_mutability) => {
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
            Ty::ResRef(kind, requested)
        }
        ExprKind::Borrow { field: Some(_), .. } | ExprKind::SelfField { .. } => {
            return Err(format!(
                "svm.resource_operand_place: {operation} uses a resource field; class members are outside the SVM local environment"
            ));
        }
        ExprKind::OptTake { option, .. } => {
            return Err(affine_option_take_unsupported(option));
        }
        _ => {
            return Err(format!(
                "svm.resource_operand_place: {operation} requires a local resource variable or local resource borrow"
            ));
        }
    };
    if let Some(annotation) = expr.ty {
        if annotation != actual {
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

    let mutable_ref = |kind| Ty::ResRef(kind, Mutability::Mut);
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
            vec![mutable_ref(ResKind::AllocatorState), u64_ty, u64_ty]
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
            let Ty::ResRef(
                map_kind
                @ (ResKind::ResourceMapPointsToU64 | ResKind::ResourceMapPointsToRecord(_)),
                Mutability::Mut,
            ) = map_ty
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
        if expected.is_resource() {
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
            match map {
                Ty::ResRef(ResKind::ResourceMapPointsToU64, Mutability::Mut) => {
                    Ty::Res(ResKind::PointsToU64)
                }
                Ty::ResRef(ResKind::ResourceMapPointsToRecord(record), Mutability::Mut) => {
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
    if expected.is_resource() {
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
    let shared = |kind| Ty::ResRef(kind, Mutability::Shared);
    let mutable = |kind| Ty::ResRef(kind, Mutability::Mut);
    let owned = Ty::Res;
    let resource_kind = |index: usize| -> Option<ResKind> {
        resolved_resource_place_ty(
            ctx,
            &args[index],
            &format!("`{}` operand {}", op.name(), index + 1),
        )
        .ok()
        .and_then(|ty| match ty {
            Ty::Res(kind) | Ty::ResRef(kind, _) => Some(kind),
            _ => None,
        })
    };
    let leased = match op {
        RawOp::IntoCellU64 | RawOp::FromCellU64 => resource_kind(1),
        RawOp::CellInitU64 => resource_kind(2),
        RawOp::CellReadU64 | RawOp::CellTakeU64 | RawOp::CellDropU64 => resource_kind(1),
        _ => None,
    }
    .is_some_and(|kind| matches!(kind, ResKind::BlockLease | ResKind::LeasedPointsToU64));

    let signature = match op {
        RawOp::Offset => (vec![raw, u64_ty], raw),
        RawOp::Load8 => (vec![raw, shared(ResKind::RawSpan)], u8_ty),
        RawOp::Store8 => (vec![raw, u8_ty, mutable(ResKind::RawSpan)], Ty::Unit),
        RawOp::Copy => (
            vec![
                raw,
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
            vec![raw, u64_ty, u64_ty, mutable(ResKind::FreeHeader)],
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
            vec![Ty::ResRef(ResKind::Uart, Mutability::Mut)],
            Ty::Int(IntTy::U8),
        ),
        DeviceOp::UartWrite => (
            vec![
                Ty::Int(IntTy::U8),
                Ty::ResRef(ResKind::Uart, Mutability::Mut),
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
        let expected = expected[index];
        let inert = match &arg.kind {
            // Checked literals are in range and cannot trap.
            ExprKind::IntLit(_) | ExprKind::BoolLit(_) => true,
            // A scalar local read and a checked local resource place are both
            // side-effect-free. Resource variables deliberately may lack a
            // cached annotation, so resolve them through the active context.
            ExprKind::Var(_) if expected.is_resource() => {
                resolved_resource_place_ty(
                    ctx,
                    arg,
                    &format!("`{}` operand {}", op.name(), index + 1),
                )? == expected
            }
            ExprKind::Var(_) => true,
            ExprKind::Borrow { .. } if expected.is_resource() => {
                resolved_resource_place_ty(
                    ctx,
                    arg,
                    &format!("`{}` operand {}", op.name(), index + 1),
                )? == expected
            }
            ExprKind::OptTake { option, .. } => {
                return Err(affine_option_take_unsupported(option));
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
        ExprKind::OptTake { option, .. } => Err(affine_option_take_unsupported(option)),
        _ => Err("resource-valued expression is outside the SVM core subset".into()),
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
        ExprKind::OptTake { option, .. } => Err(affine_option_take_unsupported(option)),
        _ => unreachable!("fresh Boolean array validation accepted a transport"),
    }
}

/// `x = e;` — an assign, or (A-normalized, ADR 0005) a call when `e`
/// is exactly a call; calls nested deeper stay outside the subset.
fn lower_bind(ctx: &LowerCtx<'_>, name: &str, e: &Expr) -> Result<String, String> {
    match &e.kind {
        ExprKind::OptTake { option, .. } => Err(affine_option_take_unsupported(option)),
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
            if e.ty != Some(result) {
                return Err(format!(
                    "svm.raw_result_type: `{}` produces `{}` but is annotated `{}`",
                    op.name(),
                    result.name(),
                    e.ty.map_or_else(|| "<missing>".into(), Ty::name)
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
    let lowered: Result<Vec<String>, String> =
        args.iter().map(|arg| lower_expr(ctx, arg)).collect();
    let d = match dst {
        Some(x) => format!("(some \"{x}\")"),
        None => "none".into(),
    };
    Ok(format!(
        "(.call {d} \"{callee}\" [{}])",
        lowered?.join(", ")
    ))
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
            if e.ty != Some(result) {
                return Err(format!(
                    "svm.device_result_type: `{}` produces `{}` but is annotated `{}`",
                    op.name(),
                    result.name(),
                    e.ty.map_or_else(|| "<missing>".into(), Ty::name)
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
            if e.ty != Some(result) {
                return Err(format!(
                    "svm.raw_result_type: `{}` produces `{}` but is annotated `{}`",
                    op.name(),
                    result.name(),
                    e.ty.map_or_else(|| "<missing>".into(), Ty::name)
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
        ExprKind::SomeE(inner) => match validate_some_constructor(e, inner)? {
            SvmOptionRepr::RawRecord(record) => {
                ctx.record(record)?;
                format!("(.ptrSomeE {})", lower_expr(ctx, inner)?)
            }
            SvmOptionRepr::Ordinary(_) => {
                format!("(.someE {})", lower_expr(ctx, inner)?)
            }
        },
        ExprKind::NoneE => match svm_option_repr(e, "none")? {
            SvmOptionRepr::RawRecord(record) => {
                ctx.record(record)?;
                "(.ptrNoneE)".into()
            }
            SvmOptionRepr::Ordinary(_) => "(.noneE)".into(),
        },
        ExprKind::IsSome { operand } => match validate_option_accessor(e, operand, false)? {
            SvmOptionRepr::Ordinary(_) => {
                format!("(.optIsSome {})", lower_expr(ctx, operand)?)
            }
            SvmOptionRepr::RawRecord(record) => {
                ctx.record(record)?;
                format!("(.ptrIsSome {})", lower_expr(ctx, operand)?)
            }
        },
        ExprKind::OptValue { operand } => match validate_option_accessor(e, operand, true)? {
            SvmOptionRepr::Ordinary(_) => {
                format!("(.optValue {})", lower_expr(ctx, operand)?)
            }
            SvmOptionRepr::RawRecord(record) => {
                ctx.record(record)?;
                format!("(.ptrValue {})", lower_expr(ctx, operand)?)
            }
        },
        ExprKind::OptTake { option, .. } => {
            return Err(affine_option_take_unsupported(option));
        }
        ExprKind::RecordField { obj, field, .. } => {
            format!("(.recordField (.var \"{obj}\") \"{field}\")")
        }
        ExprKind::AllocArray { elem, len, init } => {
            validate_alloc_array(ctx, e, *elem, len, init)?;
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

fn render_rt_val(program: &Program, value: &RtVal) -> String {
    match value {
        RtVal::Unit => "unit".into(),
        RtVal::Int(n) => format!("int {n}"),
        RtVal::Bool(b) => format!("bool {b}"),
        RtVal::Arr(a) => format!(
            "arr [{}]",
            a.borrow()
                .iter()
                .map(|n| n.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        ),
        RtVal::Ptr(a, o) => format!("ptr {a}+{o}"),
        RtVal::Opt { value: None, .. } => "opt none".into(),
        RtVal::Opt {
            value: Some(value), ..
        } => match value.as_ref() {
            // Preserve the established integer-option wire spelling while
            // adding an unambiguous Boolean spelling for G1.2.
            RtVal::Int(n) => format!("opt some {n}"),
            RtVal::Bool(b) => format!("opt some {b}"),
            value => format!("opt some {}", render_rt_val(program, value)),
        },
        RtVal::AffineOptBoolArray(_) => "unclassified affine Boolean-array option".into(),
        RtVal::PtrOpt(None) => "ptrOpt none".into(),
        RtVal::PtrOpt(Some((a, o))) => format!("ptrOpt some {a}+{o}"),
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
            ValueTy::Record(0),
            ValueTy::Param(TypeParamId::from_legacy(0)),
            ValueTy::Int(IntTy::TParam(0)),
        ];

        for payload in unsupported {
            let function = checked_fn(Ty::Option(payload), Vec::new());
            let error = lower_fn(&program, &function)
                .expect_err("an unmodeled option must not inherit recursive SVM lowering");
            assert!(
                error.starts_with("svm.aggregate_payload_unsupported:"),
                "{payload:?}: {error}"
            );
        }
    }

    #[test]
    fn lowering_rejects_affine_options_before_copy_option_classification() {
        let program = empty_program();
        let affine_bool = Ty::AffineOption(AffineOptionTy::Array(ValueTy::Bool));
        let affine_integer = Ty::AffineOption(AffineOptionTy::Array(ValueTy::Int(IntTy::I32)));

        for ty in [affine_bool, affine_integer] {
            let error = lower_fn(&program, &checked_fn(ty, Vec::new()))
                .expect_err("an affine option must not inherit ordinary option lowering");
            assert!(
                error.starts_with("svm.affine_option_unsupported:"),
                "{ty:?}: {error}"
            );
        }

        let mut parameterized = checked_fn(Ty::Unit, Vec::new());
        parameterized.params.push(Param {
            name: "pending".into(),
            ty: affine_bool,
            span: Span::new(0, 0),
            consumes: false,
        });
        let error = lower_fn(&program, &parameterized)
            .expect_err("the zero-argument harness gate must retain the affine diagnostic");
        assert!(
            error.starts_with("svm.affine_option_unsupported:"),
            "{error}"
        );

        let local = checked_fn(
            Ty::Unit,
            vec![Stmt::Decl {
                ty: affine_bool,
                name: "pending".into(),
                name_span: Span::new(0, 0),
                init: Some(expr(ExprKind::NoneE, affine_bool)),
                mutable: true,
            }],
        );
        let error = lower_fn(&program, &local)
            .expect_err("an affine-option local must remain outside the formal SVM");
        assert!(
            error.starts_with("svm.affine_option_unsupported:"),
            "{error}"
        );

        let mut ctx = LowerCtx::bare(&program);
        ctx.insert_local("pending", affine_bool, true, true)
            .unwrap();
        let accessor = expr(
            ExprKind::IsSome {
                operand: Box::new(expr(ExprKind::Var("pending".into()), affine_bool)),
            },
            Ty::Bool,
        );
        let error = validate_expr_payloads(&ctx, &accessor)
            .expect_err("a forged accessor must not classify an affine option as copyable");
        assert!(
            error.starts_with("svm.affine_option_unsupported:"),
            "{error}"
        );

        let take = expr(
            ExprKind::OptTake {
                option: "pending".into(),
                option_span: Span::new(0, 0),
            },
            Ty::Array(ValueTy::Bool, Mutability::Owned),
        );
        let expected = "svm.affine_option_unsupported: `.take` of affine option local `pending` requires an atomic ownership transition that is not yet modeled by the formal SVM";
        assert_eq!(
            validate_expr_payloads(&ctx, &take)
                .expect_err("affine take must not inherit general array lowering"),
            expected
        );
        assert_eq!(
            validate_fresh_bool_array_initializer(
                &ctx,
                Ty::Array(ValueTy::Bool, Mutability::Owned),
                &take,
                "bytes",
            )
            .expect_err("affine take must not inherit fresh-array lowering"),
            expected
        );
        assert_eq!(
            lower_expr(&ctx, &take).expect_err("affine take has no formal SVM expression"),
            expected
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
        let bool_option = Ty::Option(ValueTy::Bool);
        let mut ctx = LowerCtx::bare(&program);
        ctx.insert_local("choice", bool_option, false, true)
            .unwrap();

        let some_false = expr(
            ExprKind::SomeE(Box::new(expr(ExprKind::BoolLit(false), Ty::Bool))),
            bool_option,
        );
        assert_eq!(
            lower_expr(&ctx, &some_false).unwrap(),
            "(.someE (.boolLit false))"
        );
        assert_eq!(
            lower_expr(&ctx, &expr(ExprKind::NoneE, bool_option)).unwrap(),
            "(.noneE)"
        );

        let option_var = || expr(ExprKind::Var("choice".into()), bool_option);
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
        let bool_option = Ty::Option(ValueTy::Bool);

        let wrong_payload = expr(
            ExprKind::SomeE(Box::new(expr(ExprKind::IntLit(1), Ty::Int(IntTy::I32)))),
            bool_option,
        );
        let nested_payload = expr(
            ExprKind::SomeE(Box::new(expr(
                ExprKind::SomeE(Box::new(expr(ExprKind::BoolLit(false), Ty::Bool))),
                bool_option,
            ))),
            bool_option,
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
            bool_option,
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
            bool_option,
        );
        let valid_int = expr(
            ExprKind::SomeE(Box::new(expr(ExprKind::IntLit(7), Ty::Int(IntTy::I32)))),
            Ty::Option(ValueTy::Int(IntTy::I32)),
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

        let unsupported = expr(ExprKind::NoneE, Ty::Option(ValueTy::Record(0)));
        let error = validate_expr_payloads(&ctx, &unsupported)
            .expect_err("record option payload must remain outside G1.2");
        assert!(
            error.starts_with("svm.aggregate_payload_unsupported:"),
            "{error}"
        );
    }

    #[test]
    fn option_accessors_require_coherent_checked_annotations() {
        let program = empty_program();
        let bool_option = Ty::Option(ValueTy::Bool);
        let int_option = Ty::Option(ValueTy::Int(IntTy::I32));
        let mut ctx = LowerCtx::bare(&program);
        ctx.insert_local("choice", bool_option, false, true)
            .unwrap();
        ctx.insert_local("number", int_option, false, true).unwrap();
        ctx.insert_local("pointer", Ty::OptionRaw(0), false, true)
            .unwrap();
        let bool_operand = || expr(ExprKind::Var("choice".into()), bool_option);
        let int_operand = || expr(ExprKind::Var("number".into()), int_option);

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
            payload: ValueTy::Bool,
            value: None,
        };
        let false_value = RtVal::Opt {
            payload: ValueTy::Bool,
            value: Some(Box::new(RtVal::Bool(false))),
        };
        let true_value = RtVal::Opt {
            payload: ValueTy::Bool,
            value: Some(Box::new(RtVal::Bool(true))),
        };
        let affine_value = RtVal::AffineOptBoolArray(None);

        assert_eq!(render_rt_val(&program, &absent), "opt none");
        assert_eq!(render_rt_val(&program, &false_value), "opt some false");
        assert_eq!(render_rt_val(&program, &true_value), "opt some true");
        assert_eq!(
            render_rt_val(&program, &affine_value),
            "unclassified affine Boolean-array option"
        );
    }

    #[test]
    fn lowering_rejects_option_parameters_independently() {
        let program = empty_program();
        let mut function = checked_fn(Ty::Bool, Vec::new());
        function.params.push(Param {
            name: "choice".into(),
            ty: Ty::Option(ValueTy::Bool),
            span: Span::new(0, 0),
            consumes: false,
        });

        let error = lower_fn_entry(&program, &function)
            .expect_err("G1.2 does not introduce an option parameter ABI");
        assert!(
            error.starts_with("svm.option_position_unsupported:"),
            "{error}"
        );
    }

    #[test]
    fn lowering_rejects_boolean_arrays_outside_fresh_owned_locals() {
        let program = empty_program();
        let array_ty = Ty::Array(ValueTy::Bool, Mutability::Owned);

        let mut parameter = checked_fn(Ty::Bool, Vec::new());
        parameter.params.push(Param {
            name: "bits".into(),
            ty: array_ty,
            span: Span::new(0, 0),
            consumes: false,
        });
        let error = lower_fn_entry(&program, &parameter)
            .expect_err("Boolean arrays have no SVM parameter ABI");
        assert!(
            error.starts_with("svm.bool_array_position_unsupported:"),
            "{error}"
        );

        let returned = checked_fn(array_ty, Vec::new());
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
        let mut function = checked_fn(Ty::Option(ValueTy::Bool), Vec::new());
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
        let mut choose = checked_fn(Ty::Option(ValueTy::Bool), Vec::new());
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

        let valid = call(vec![selector()], Some(Ty::Option(ValueTy::Bool)));
        validate_expr_payloads(&ctx, &valid).expect("checked option-returning call");
        assert_eq!(
            lower_call(&ctx, &Some("choice".into()), &valid).unwrap(),
            "(.call (some \"choice\") \"choose\" [(.intLit .i32 0)])"
        );

        let wrong_result = call(vec![selector()], Some(Ty::Int(IntTy::I32)));
        let missing_result = call(vec![selector()], None);
        let wrong_arity = call(Vec::new(), Some(Ty::Option(ValueTy::Bool)));
        let wrong_argument = call(
            vec![expr(ExprKind::BoolLit(false), Ty::Bool)],
            Some(Ty::Option(ValueTy::Bool)),
        );
        let missing_argument = call(
            vec![Expr {
                kind: ExprKind::IntLit(0),
                span: Span::new(0, 0),
                ty: None,
            }],
            Some(Ty::Option(ValueTy::Bool)),
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
                ty: Ty::Option(ValueTy::Bool),
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
            .expect_err("G1.2 does not introduce option-valued class storage");
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
            methods: vec![checked_fn(Ty::Option(ValueTy::Bool), Vec::new())],
            span: Span::new(0, 0),
        });
        let trait_error = validate_program_option_positions(&trait_program)
            .expect_err("G1.2 does not widen trait result semantics");
        assert!(
            trait_error.starts_with("svm.option_position_unsupported:"),
            "{trait_error}"
        );
    }

    #[test]
    fn lowering_rejects_externs_before_they_can_become_empty_bodies() {
        let program = empty_program();
        let mut function = checked_fn(Ty::Option(ValueTy::Bool), Vec::new());
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
        let array_ty = Ty::Array(ValueTy::Bool, Mutability::Owned);
        let allocation = expr(
            ExprKind::AllocArray {
                elem: ValueTy::Bool,
                len: Box::new(expr(ExprKind::IntLit(3), Ty::Int(IntTy::U64))),
                init: Box::new(expr(ExprKind::BoolLit(true), Ty::Bool)),
            },
            array_ty,
        );
        assert_eq!(
            lower_fresh_bool_array_bind(&ctx, "allocated", array_ty, &allocation).unwrap(),
            "(.assign \"allocated\" (.allocArray (.intLit .u64 3) (.boolLit true)))"
        );

        let literal = expr(
            ExprKind::ArrayLit(vec![
                expr(ExprKind::BoolLit(true), Ty::Bool),
                expr(ExprKind::BoolLit(false), Ty::Bool),
            ]),
            array_ty,
        );
        assert_eq!(
            lower_fresh_bool_array_bind(&ctx, "literal", array_ty, &literal).unwrap(),
            "(.assign \"_bool_lit_literal_0\" (.boolLit true)), \
             (.assign \"_bool_lit_literal_1\" (.boolLit false)), \
             (.assign \"literal\" (.allocArray (.intLit .u64 2) (.boolLit false))), \
             (.store \"literal\" (.intLit .u64 0) (.var \"_bool_lit_literal_0\")), \
             (.store \"literal\" (.intLit .u64 1) (.var \"_bool_lit_literal_1\"))"
        );
        let empty = expr(ExprKind::ArrayLit(Vec::new()), array_ty);
        assert_eq!(
            lower_fresh_bool_array_bind(&ctx, "empty", array_ty, &empty).unwrap(),
            "(.assign \"empty\" (.allocArray (.intLit .u64 0) (.boolLit false)))"
        );

        let error = validate_array_literal_len(ValueTy::Bool, 50_000_001)
            .expect_err("literal expansion must remain inside the formal allocation cap");
        assert!(error.starts_with("svm.array_literal_capacity:"), "{error}");
        validate_array_literal_len(ValueTy::Bool, 50_000_000)
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
    fn boolean_arrays_reject_uninitialized_alias_rebind_borrow_and_exposure() {
        let program = empty_program();
        let array_ty = Ty::Array(ValueTy::Bool, Mutability::Owned);
        let literal = || {
            expr(
                ExprKind::ArrayLit(vec![expr(ExprKind::BoolLit(true), Ty::Bool)]),
                array_ty,
            )
        };
        let declaration = |name: &str, mutable: bool| Stmt::Decl {
            ty: array_ty,
            name: name.into(),
            name_span: Span::new(0, 0),
            init: Some(literal()),
            mutable,
        };

        let uninitialized = checked_fn(
            Ty::Unit,
            vec![Stmt::Decl {
                ty: array_ty,
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
                    ty: array_ty,
                    name: "alias".into(),
                    name_span: Span::new(0, 0),
                    init: Some(expr(ExprKind::Var("source".into()), array_ty)),
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

        let mut ctx = LowerCtx::bare(&program);
        ctx.insert_local("bits", array_ty, true, true).unwrap();
        let borrow = Expr {
            kind: ExprKind::Borrow {
                array: "bits".into(),
                field: None,
                mutable: false,
            },
            span: Span::new(0, 0),
            ty: None,
        };
        let error = validate_expr_payloads(&ctx, &borrow)
            .expect_err("Boolean array locals cannot be borrowed");
        assert!(
            error.starts_with("svm.bool_array_borrow_unsupported:"),
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
    fn lowering_checks_alloc_array_element_even_if_annotation_is_integer() {
        let program = empty_program();
        let allocation = expr(
            ExprKind::AllocArray {
                elem: ValueTy::Record(0),
                len: Box::new(expr(ExprKind::IntLit(1), Ty::Int(IntTy::U64))),
                init: Box::new(expr(ExprKind::IntLit(0), Ty::Int(IntTy::U8))),
            },
            Ty::Array(ValueTy::Int(IntTy::U8), Mutability::Owned),
        );
        let function = checked_fn(
            Ty::Unit,
            vec![Stmt::Decl {
                ty: Ty::Array(ValueTy::Int(IntTy::U8), Mutability::Owned),
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
            "svm.aggregate_payload_unsupported: alloc_array has array payload `record`; \
             the SVM currently lowers only concrete integer and Boolean payloads"
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
                    ty: Ty::Array(ValueTy::Int(IntTy::U8), Mutability::Owned),
                    name: "values".into(),
                    name_span: Span::new(0, 0),
                    init: Some(expr(
                        ExprKind::AllocArray {
                            elem: ValueTy::Int(IntTy::U8),
                            len: Box::new(expr(ExprKind::IntLit(1), Ty::Int(IntTy::U64))),
                            init: Box::new(expr(ExprKind::IntLit(0), Ty::Int(IntTy::U8))),
                        },
                        Ty::Array(ValueTy::Int(IntTy::U8), Mutability::Owned),
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
        let u8_array = Ty::Array(ValueTy::Int(IntTy::U8), Mutability::Owned);
        let allocation = |len: Expr, init: Expr, ty: Option<Ty>| Expr {
            kind: ExprKind::AllocArray {
                elem: ValueTy::Int(IntTy::U8),
                len: Box::new(len),
                init: Box::new(init),
            },
            span: Span::new(0, 0),
            ty,
        };
        let length = || expr(ExprKind::IntLit(2), Ty::Int(IntTy::U64));
        let byte = || expr(ExprKind::IntLit(7), Ty::Int(IntTy::U8));

        let valid = allocation(length(), byte(), Some(u8_array));
        validate_expr_payloads(&ctx, &valid).expect("coherent integer allocation preflight");
        assert_eq!(
            lower_expr(&ctx, &valid).unwrap(),
            "(.allocArray (.intLit .u64 2) (.intLit .u8 7))"
        );

        let malformed = [
            (
                allocation(
                    length(),
                    byte(),
                    Some(Ty::Array(ValueTy::Int(IntTy::I32), Mutability::Owned)),
                ),
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
                    Some(u8_array),
                ),
                "svm.sink_type:",
            ),
            (
                allocation(
                    length(),
                    expr(ExprKind::IntLit(7), Ty::Int(IntTy::I32)),
                    Some(u8_array),
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
            u8_array,
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
        let array_ty = Ty::Array(ValueTy::Int(IntTy::U8), Mutability::Owned);
        let forged_bool = |ty| expr(ExprKind::BoolLit(true), ty);
        let length = || expr(ExprKind::IntLit(1), Ty::Int(IntTy::U64));
        let byte = || expr(ExprKind::IntLit(0), Ty::Int(IntTy::U8));
        let allocation = |len: Expr, init: Expr| {
            expr(
                ExprKind::AllocArray {
                    elem: ValueTy::Int(IntTy::U8),
                    len: Box::new(len),
                    init: Box::new(init),
                },
                array_ty,
            )
        };

        let mut ctx = LowerCtx::bare(&program);
        ctx.insert_local("bytes", array_ty, true, true).unwrap();
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
        let array_ty = Ty::Array(ValueTy::Bool, Mutability::Owned);
        let mut ctx = LowerCtx::bare(&program);
        ctx.insert_local("bits", array_ty, true, true).unwrap();
        let length = || expr(ExprKind::IntLit(2), Ty::Int(IntTy::U64));
        let boolean = || expr(ExprKind::BoolLit(false), Ty::Bool);

        let allocation = expr(
            ExprKind::AllocArray {
                elem: ValueTy::Bool,
                len: Box::new(length()),
                init: Box::new(boolean()),
            },
            array_ty,
        );
        validate_alloc_array(
            &ctx,
            &allocation,
            ValueTy::Bool,
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
                elem: ValueTy::Bool,
                len: Box::new(length()),
                init: Box::new(expr(ExprKind::IntLit(0), Ty::Int(IntTy::I32))),
            },
            array_ty,
        );
        let ExprKind::AllocArray { len, init, .. } = &bad_allocation.kind else {
            unreachable!()
        };
        let error = validate_alloc_array(&ctx, &bad_allocation, ValueTy::Bool, len, init)
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
        let array_ty = Ty::Array(ValueTy::Bool, Mutability::Owned);
        let mut ctx = LowerCtx::bare(&program);
        ctx.insert_local("source", array_ty, false, true).unwrap();
        let trapping_read = expr(
            ExprKind::Index {
                array: "source".into(),
                array_span: Span::new(0, 0),
                index: Box::new(expr(ExprKind::IntLit(7), Ty::Int(IntTy::U64))),
            },
            Ty::Bool,
        );
        let literal = expr(ExprKind::ArrayLit(vec![trapping_read]), array_ty);
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
        let array_ty = Ty::Array(ValueTy::Int(IntTy::U8), Mutability::Owned);
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
        let array_ty = Ty::Array(ValueTy::Int(IntTy::U8), Mutability::Owned);
        let allocation = expr(
            ExprKind::AllocArray {
                elem: ValueTy::Int(IntTy::U8),
                len: Box::new(expr(ExprKind::IntLit(2), Ty::Int(IntTy::U64))),
                init: Box::new(expr(ExprKind::IntLit(0), Ty::Int(IntTy::U8))),
            },
            array_ty,
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
                    ty: array_ty,
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
        ctx.insert_local("bytes", array_ty, true, true).unwrap();
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
                ty: array_ty,
                name: "bytes".into(),
                name_span: Span::new(0, 0),
                init: Some(expr(
                    ExprKind::AllocArray {
                        elem: ValueTy::Int(IntTy::I32),
                        len: Box::new(expr(ExprKind::IntLit(2), Ty::Int(IntTy::U64))),
                        init: Box::new(expr(ExprKind::IntLit(0), Ty::Int(IntTy::I32))),
                    },
                    Ty::Array(ValueTy::Int(IntTy::I32), Mutability::Owned),
                )),
                mutable: false,
            }],
        );
        let error = lower_fn(&program, &mismatched_binding)
            .expect_err("array declaration and initializer must agree exactly");
        assert!(error.starts_with("svm.sink_type:"), "{error}");

        let array_return = |returned_ty: Ty| {
            checked_fn(
                array_ty,
                vec![
                    Stmt::Decl {
                        ty: array_ty,
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
        lower_fn(&program, &array_return(array_ty))
            .expect("coherent integer-array return remains lowerable");
        let wrong_return = array_return(Ty::Array(ValueTy::Int(IntTy::I32), Mutability::Owned));
        let error = lower_fn(&program, &wrong_return)
            .expect_err("array result annotations must match the function return type");
        assert!(error.starts_with("svm.local_type:"), "{error}");
    }

    #[test]
    fn array_sinks_reject_forged_scalar_array_crossings() {
        let program = empty_program();
        let array_ty = Ty::Array(ValueTy::Int(IntTy::U8), Mutability::Owned);
        let allocation = || {
            expr(
                ExprKind::AllocArray {
                    elem: ValueTy::Int(IntTy::U8),
                    len: Box::new(expr(ExprKind::IntLit(1), Ty::Int(IntTy::U64))),
                    init: Box::new(expr(ExprKind::IntLit(0), Ty::Int(IntTy::U8))),
                },
                array_ty,
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
                    ty: array_ty,
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
        let array_ty = Ty::Array(ValueTy::Int(IntTy::U8), Mutability::Owned);
        let allocation = || {
            expr(
                ExprKind::AllocArray {
                    elem: ValueTy::Int(IntTy::U8),
                    len: Box::new(expr(ExprKind::IntLit(1), Ty::Int(IntTy::U64))),
                    init: Box::new(expr(ExprKind::IntLit(0), Ty::Int(IntTy::U8))),
                },
                array_ty,
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
            ty: array_ty,
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
        let array_ty = Ty::Array(ValueTy::Int(IntTy::U8), Mutability::Owned);
        let allocation = expr(
            ExprKind::AllocArray {
                elem: ValueTy::Int(IntTy::U8),
                len: Box::new(expr(ExprKind::IntLit(1), Ty::Int(IntTy::U64))),
                init: Box::new(expr(ExprKind::IntLit(0), Ty::Int(IntTy::U8))),
            },
            array_ty,
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

        let array_ty = Ty::Array(ValueTy::Int(IntTy::U8), Mutability::Owned);
        let allocation = expr(
            ExprKind::AllocArray {
                elem: ValueTy::Int(IntTy::U8),
                len: Box::new(expr(ExprKind::IntLit(1), Ty::Int(IntTy::U64))),
                init: Box::new(expr(ExprKind::IntLit(0), Ty::Int(IntTy::U8))),
            },
            array_ty,
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
        let array_ty = Ty::Array(ValueTy::Int(IntTy::U8), Mutability::Owned);
        let function = checked_fn(
            Ty::Int(IntTy::I32),
            vec![
                Stmt::Decl {
                    ty: array_ty,
                    name: "bytes".into(),
                    name_span: Span::new(0, 0),
                    init: Some(expr(
                        ExprKind::AllocArray {
                            elem: ValueTy::Int(IntTy::U8),
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
        let array_ty = Ty::Array(ValueTy::Int(IntTy::U8), Mutability::Owned);
        let function = checked_fn(
            Ty::Unit,
            vec![
                Stmt::Decl {
                    ty: array_ty,
                    name: "bytes".into(),
                    name_span: Span::new(0, 0),
                    init: Some(expr(
                        ExprKind::AllocArray {
                            elem: ValueTy::Int(IntTy::U8),
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
            Ty::ResRef(ResKind::RawSpan, Mutability::Mut),
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
