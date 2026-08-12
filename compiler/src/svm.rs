//! The compiler side of the SVM differential harness: lower a checked
//! function body in the machine's core subset to a Lean `List Stmt`
//! term over `lean/Sable/SVM.lean`, and canonicalize `interp.rs`
//! outcomes into the harness's wire format — which must match
//! `Config.render` on the Lean side character for character.
//!
//! Lowering is deliberately strict: anything outside the formalized
//! subset — class members, option-valued parameters/storage, array literals,
//! loop invariants — is a hard error, never a silent skip, so the harness
//! cannot compare less than it claims to. The mandatory loop `variant`
//! is the one asymmetry: erased here (ghost, design §4) but monitored
//! by the interpreter, so a diff program's variants must hold.

use crate::ast::*;
use crate::interp::{MmioEvent, ObservedRun, RtVal};
use std::collections::HashMap;

#[derive(Clone, Copy)]
struct LocalBinding {
    ty: Ty,
    mutable: bool,
}

/// Program metadata needed while lowering checked, index-bearing AST nodes.
/// Keeping this context explicit ensures record tags and layouts come from
/// the same checked program whose function body we lower.
struct LowerCtx<'a> {
    program: &'a Program,
    locals: HashMap<String, LocalBinding>,
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
            return_ty: None,
        }
    }

    /// Recover the checked local environment before emitting the untyped Lean
    /// syntax. Array expressions carry only a source name, so their element
    /// type cannot be validated from the expression node alone.
    fn for_function(program: &'a Program, function: &Fn) -> Result<LowerCtx<'a>, String> {
        let mut ctx = LowerCtx {
            program,
            locals: HashMap::new(),
            return_ty: Some(function.ret),
        };
        for parameter in &function.params {
            ctx.insert_local(&parameter.name, parameter.ty, false)?;
        }
        ctx.collect_stmt_locals(&function.body)?;
        Ok(ctx)
    }

    fn insert_local(&mut self, name: &str, ty: Ty, mutable: bool) -> Result<(), String> {
        if self
            .locals
            .insert(name.to_string(), LocalBinding { ty, mutable })
            .is_some()
        {
            return Err(format!(
                "svm.local_type: duplicate checked local `{name}`; local types are ambiguous"
            ));
        }
        Ok(())
    }

    fn collect_stmt_locals(&mut self, stmts: &[Stmt]) -> Result<(), String> {
        for stmt in stmts {
            match stmt {
                Stmt::Decl {
                    name, ty, mutable, ..
                } => self.insert_local(name, *ty, *mutable)?,
                Stmt::VarDecl {
                    name,
                    ty: Some(ty),
                    mutable,
                    ..
                } => self.insert_local(name, *ty, *mutable)?,
                Stmt::VarDecl { name, ty: None, .. } => {
                    return Err(format!(
                        "svm.local_type: inferred declaration `{name}` carries no checked type"
                    ));
                }
                Stmt::If {
                    then_block,
                    else_block,
                    ..
                } => {
                    self.collect_stmt_locals(then_block)?;
                    if let Some(else_block) = else_block {
                        self.collect_stmt_locals(else_block)?;
                    }
                }
                Stmt::While { body, .. } | Stmt::Unsafe { body, .. } => {
                    self.collect_stmt_locals(body)?;
                }
                Stmt::Expose { ptr, res, body, .. } => {
                    self.insert_local(ptr, Ty::Raw(IntTy::U8), false)?;
                    self.insert_local(res, Ty::Res(ResKind::RawSpan), false)?;
                    self.collect_stmt_locals(body)?;
                }
                Stmt::StaticAlloc { ptr, res, .. } => {
                    self.insert_local(ptr, Ty::Raw(IntTy::U8), false)?;
                    self.insert_local(res, Ty::Res(ResKind::RawSpan), false)?;
                }
                Stmt::SystemAlloc {
                    ptr, res, release, ..
                } => {
                    self.insert_local(ptr, Ty::Raw(IntTy::U8), false)?;
                    self.insert_local(res, Ty::Res(ResKind::RawSpan), false)?;
                    self.insert_local(release, Ty::Res(ResKind::SystemDealloc), false)?;
                }
                Stmt::Assign { .. }
                | Stmt::Return { .. }
                | Stmt::ExprStmt(_)
                | Stmt::Assert(_)
                | Stmt::FieldAssign { .. }
                | Stmt::FieldStore { .. }
                | Stmt::Store { .. }
                | Stmt::SystemDealloc { .. } => {}
            }
        }
        Ok(())
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

/// Keep the G1.2 representation boundary explicit: arrays remain concrete-
/// integer-only, while ordinary options additionally admit `bool`.  The Lean
/// constructors are intentionally untyped, so every checked payload must be
/// classified here instead of inheriting lowering by accident.
fn validate_fn_payloads(ctx: &LowerCtx<'_>, f: &Fn) -> Result<(), String> {
    if !f.type_params.is_empty() {
        return Err(format!(
            "svm.type_parameter_unsupported: `{}` is still a generic declaration",
            f.name
        ));
    }
    for param in &f.params {
        validate_ty_payload(param.ty, &format!("parameter `{}`", param.name))?;
        if matches!(param.ty, Ty::Option(_)) {
            return Err(format!(
                "svm.option_position_unsupported: parameter `{}` is option-typed; \
                 ordinary options are returns and locals only",
                param.name
            ));
        }
    }
    validate_ty_payload(f.ret, &format!("return type of `{}`", f.name))?;
    if f.extern_info.is_some() {
        return Err(format!(
            "`{}` is an audited extern: the machine has no semantics for a foreign call",
            f.name
        ));
    }
    validate_stmt_payloads(ctx, &f.body)
}

fn validate_ty_payload(ty: Ty, context: &str) -> Result<(), String> {
    match ty {
        Ty::Array(payload, _) => validate_array_payload(payload, context),
        Ty::Option(payload) => validate_option_payload(payload, context),
        Ty::Param(_) | Ty::Int(IntTy::TParam(_)) | Ty::Raw(IntTy::TParam(_)) => Err(format!(
            "svm.type_parameter_unsupported: {context} contains an unresolved type parameter"
        )),
        _ => Ok(()),
    }
}

fn validate_array_payload(payload: ValueTy, context: &str) -> Result<(), String> {
    match payload {
        ValueTy::Int(integer) if !matches!(integer, IntTy::TParam(_)) => Ok(()),
        _ => Err(format!(
            "svm.aggregate_payload_unsupported: {context} has array payload `{}`; \
             the SVM currently lowers only concrete integer payloads",
            payload.name()
        )),
    }
}

fn integer_array_element_ty(payload: ValueTy, context: &str) -> Result<Ty, String> {
    validate_array_payload(payload, context)?;
    match payload {
        ValueTy::Int(integer) if !matches!(integer, IntTy::TParam(_)) => Ok(Ty::Int(integer)),
        _ => unreachable!("validate_array_payload accepted a non-integer payload"),
    }
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

fn resolve_integer_array(
    ctx: &LowerCtx<'_>,
    array: &str,
    operation: &str,
) -> Result<(ValueTy, Mutability, bool), String> {
    let Some(binding) = ctx.local(array) else {
        return Err(format!(
            "svm.array_place_type: {operation} names unknown array `{array}`"
        ));
    };
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
    let (payload, _, _) = resolve_integer_array(ctx, array, "array index")?;
    let element = integer_array_element_ty(payload, "array index result")?;
    require_expr_annotation(
        expr,
        element,
        "svm.array_index_result_type",
        "array index result",
    )?;
    require_expr_annotation(
        index,
        Ty::Int(IntTy::U64),
        "svm.array_index_operand_type",
        "array index operand",
    )?;
    validate_expr_payloads(ctx, index)
}

fn validate_array_len(ctx: &LowerCtx<'_>, expr: &Expr, array: &str) -> Result<(), String> {
    resolve_integer_array(ctx, array, "array length")?;
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
    let element = integer_array_element_ty(elem, "alloc_array")?;
    require_expr_annotation(
        expr,
        Ty::Array(elem, Mutability::Owned),
        "svm.array_alloc_result_type",
        "alloc_array result",
    )?;
    require_expr_annotation(
        len,
        Ty::Int(IntTy::U64),
        "svm.array_alloc_length_type",
        "alloc_array length",
    )?;
    require_expr_annotation(
        init,
        element,
        "svm.array_alloc_init_type",
        "alloc_array initializer",
    )?;
    validate_expr_payloads(ctx, len)?;
    validate_expr_payloads(ctx, init)
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
                "svm.array_literal_result_type: array literal is annotated `{}`; expected an owned integer array",
                actual.name()
            ));
        }
        None => {
            return Err(
                "svm.array_literal_result_type: array literal carries no checked type; expected an owned integer array"
                    .into(),
            );
        }
    };
    let element = integer_array_element_ty(payload, "array literal")?;
    for (index, value) in elements.iter().enumerate() {
        require_expr_annotation(
            value,
            element,
            "svm.array_literal_element_type",
            &format!("array literal element {}", index + 1),
        )?;
        validate_expr_payloads(ctx, value)?;
    }
    Ok(())
}

fn validate_array_store(
    ctx: &LowerCtx<'_>,
    array: &str,
    index: &Expr,
    value: &Expr,
) -> Result<(), String> {
    let (payload, mutability, declared_mutable) = resolve_integer_array(ctx, array, "array store")?;
    if mutability == Mutability::Shared || (mutability == Mutability::Owned && !declared_mutable) {
        return Err(format!(
            "svm.array_store_place: array store targets non-writable `{array}` of type `{}`",
            Ty::Array(payload, mutability).name()
        ));
    }
    require_expr_annotation(
        index,
        Ty::Int(IntTy::U64),
        "svm.array_store_index_type",
        "array store index",
    )?;
    require_expr_annotation(
        value,
        integer_array_element_ty(payload, "array store value")?,
        "svm.array_store_value_type",
        "array store value",
    )?;
    validate_expr_payloads(ctx, index)?;
    validate_expr_payloads(ctx, value)
}

fn validate_array_binding(ty: Ty, name: &str, init: &Expr) -> Result<(), String> {
    if !matches!(ty, Ty::Array(..)) {
        return Ok(());
    }
    require_expr_annotation(
        init,
        ty,
        "svm.array_binding_type",
        &format!("initializer of array `{name}`"),
    )
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

fn validate_array_return(ctx: &LowerCtx<'_>, value: &Expr) -> Result<(), String> {
    if let Some(expected @ Ty::Array(..)) = ctx.return_ty {
        require_expr_annotation(
            value,
            expected,
            "svm.array_return_type",
            "array return value",
        )?;
    }
    Ok(())
}

fn validate_array_exposure(ctx: &LowerCtx<'_>, array: &str, mutable: bool) -> Result<(), String> {
    let (payload, mutability, declared_mutable) =
        resolve_integer_array(ctx, array, "array exposure")?;
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
            if let Ty::Option(payload) = parameter.ty {
                validate_option_payload(payload, context)?;
                return Err(format!(
                    "svm.option_position_unsupported: {context} parameter `{}` is option-typed; \
                     ordinary options are returns and locals only",
                    parameter.name
                ));
            }
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
        for field in &record.fields {
            if let Ty::Option(payload) = field.ty {
                validate_option_payload(payload, &format!("record `{}`", record.name))?;
                return Err(format!(
                    "svm.option_position_unsupported: record `{}.{}` has an option-typed field; \
                     option-valued fields are not in the SVM model",
                    record.name, field.name
                ));
            }
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

fn validate_stmt_payloads(ctx: &LowerCtx<'_>, stmts: &[Stmt]) -> Result<(), String> {
    for stmt in stmts {
        match stmt {
            Stmt::Decl { ty, init, name, .. } => {
                validate_ty_payload(*ty, &format!("declaration `{name}`"))?;
                if let Some(init) = init {
                    validate_array_binding(*ty, name, init)?;
                    validate_expr_payloads(ctx, init)?;
                }
            }
            Stmt::Assign { name, value, .. } => {
                validate_array_rebind(ctx, name)?;
                validate_expr_payloads(ctx, value)?;
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
                validate_stmt_payloads(ctx, then_block)?;
                if let Some(else_block) = else_block {
                    validate_stmt_payloads(ctx, else_block)?;
                }
            }
            Stmt::Return { value, .. } => {
                if let Some(value) = value {
                    validate_array_return(ctx, value)?;
                    validate_expr_payloads(ctx, value)?;
                }
            }
            Stmt::Assert(_) => {}
            Stmt::VarDecl { name, init, ty, .. } => {
                if let Some(ty) = ty {
                    validate_ty_payload(*ty, &format!("inferred declaration `{name}`"))?;
                    validate_array_binding(*ty, name, init)?;
                }
                validate_expr_payloads(ctx, init)?;
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
                validate_stmt_payloads(ctx, body)?;
            }
            Stmt::Unsafe { body, .. } => {
                validate_stmt_payloads(ctx, body)?;
            }
            Stmt::Expose {
                array,
                mutable,
                body,
                ..
            } => {
                validate_array_exposure(ctx, array, *mutable)?;
                validate_stmt_payloads(ctx, body)?;
            }
            Stmt::StaticAlloc { size, .. } | Stmt::SystemAlloc { size, .. } => {
                validate_expr_payloads(ctx, size)?;
            }
            Stmt::SystemDealloc {
                ptr, res, release, ..
            } => {
                validate_expr_payloads(ctx, ptr)?;
                validate_expr_payloads(ctx, res)?;
                validate_expr_payloads(ctx, release)?;
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
    for (index, (arg, parameter)) in args.iter().zip(&function.params).enumerate() {
        // Resource authority is erased from the machine. A checked resource
        // place intentionally may have no cached expression type; when one is
        // present it must still agree with the formal slot.
        let erased_resource_place = parameter.ty.is_resource()
            && arg.ty.is_none()
            && matches!(
                arg.kind,
                ExprKind::Var(_) | ExprKind::SelfField { .. } | ExprKind::Borrow { .. }
            );
        if erased_resource_place {
            continue;
        }
        match arg.ty {
            Some(actual) if actual == parameter.ty => {}
            Some(actual) => {
                return Err(format!(
                    "svm.call_argument_type: argument {} to `{callee}` is annotated `{}`; \
                     parameter `{}` has type `{}`",
                    index + 1,
                    actual.name(),
                    parameter.name,
                    parameter.ty.name()
                ));
            }
            None => {
                return Err(format!(
                    "svm.call_argument_type: argument {} to `{callee}` carries no type; \
                     parameter `{}` has type `{}`",
                    index + 1,
                    parameter.name,
                    parameter.ty.name()
                ));
            }
        }
    }
    Ok(())
}

fn validate_expr_payloads(ctx: &LowerCtx<'_>, expr: &Expr) -> Result<(), String> {
    if let Some(ty) = expr.ty {
        validate_ty_payload(ty, "expression annotation")?;
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
            validate_expr_payloads(ctx, operand)?;
        }
        ExprKind::NoneE => {
            svm_option_repr(expr, "none")?;
        }
        ExprKind::IsSome { operand } => {
            validate_option_accessor(expr, operand, false)?;
            validate_expr_payloads(ctx, operand)?;
        }
        ExprKind::OptValue { operand } => {
            validate_option_accessor(expr, operand, true)?;
            validate_expr_payloads(ctx, operand)?;
        }
        ExprKind::Unary { operand, .. } => validate_expr_payloads(ctx, operand)?,
        ExprKind::Binary { lhs, rhs, .. } => {
            validate_expr_payloads(ctx, lhs)?;
            validate_expr_payloads(ctx, rhs)?;
        }
        ExprKind::RawOp { args, .. }
        | ExprKind::DeviceOp { args, .. }
        | ExprKind::ResOp { args, .. }
        | ExprKind::TraitCall { args, .. }
        | ExprKind::MethodCall { args, .. }
        | ExprKind::RecordLit { args, .. } => {
            for arg in args {
                validate_expr_payloads(ctx, arg)?;
            }
        }
        ExprKind::SelfFieldIndex { index, .. } | ExprKind::ClassFieldIndex { index, .. } => {
            validate_expr_payloads(ctx, index)?;
        }
        ExprKind::IntLit(_)
        | ExprKind::BoolLit(_)
        | ExprKind::Var(_)
        | ExprKind::SelfField { .. }
        | ExprKind::SelfFieldLen { .. }
        | ExprKind::ClassField { .. }
        | ExprKind::RecordField { .. }
        | ExprKind::ClassFieldLen { .. }
        | ExprKind::Borrow { .. } => {}
    }
    Ok(())
}

/// Lower a zero-argument function's body to a Lean `List Stmt` term.
pub fn lower_fn(program: &Program, f: &Fn) -> Result<String, String> {
    if !f.params.is_empty() {
        return Err("differential subjects must take no parameters".into());
    }
    let ctx = LowerCtx::for_function(program, f)?;
    validate_program_option_positions(program)?;
    validate_fn_payloads(&ctx, f)?;
    lower_block(&ctx, &f.body)
}

/// Lower any function to a `Prog.ofList` entry: `("name", ⟨[params],
/// body⟩)`. Parameters must be machine values — borrows are outside the
/// machine (arrays are owned values; `&mut` reflection back to the
/// caller has no machine analog yet).
pub fn lower_fn_entry(program: &Program, f: &Fn) -> Result<String, String> {
    let ctx = LowerCtx::for_function(program, f)?;
    validate_program_option_positions(program)?;
    validate_fn_payloads(&ctx, f)?;
    for p in &f.params {
        match p.ty {
            Ty::Int(_) | Ty::Bool => {}
            Ty::Record(ri) | Ty::RawRecord(ri) | Ty::OptionRaw(ri) => {
                ctx.record(ri)?;
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
        lower_block(&ctx, &f.body)?
    ))
}

/// Fresh names for the statements an exposure expands into. A counter is
/// enough: lowering is single-threaded and one pass.
fn next_loan() -> usize {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static N: AtomicUsize = AtomicUsize::new(0);
    N.fetch_add(1, Ordering::Relaxed)
}

fn lower_block(ctx: &LowerCtx<'_>, stmts: &[Stmt]) -> Result<String, String> {
    lower_block_erasing(ctx, stmts, &[])
}

fn lower_block_erasing(
    ctx: &LowerCtx<'_>,
    stmts: &[Stmt],
    erased_resources: &[&str],
) -> Result<String, String> {
    let mut block_resources = erased_resources.to_vec();
    for stmt in stmts {
        match stmt {
            Stmt::Decl { ty, name, .. } if ty.is_resource() => {
                block_resources.push(name.as_str());
            }
            Stmt::VarDecl {
                name, ty: Some(ty), ..
            } if ty.is_resource() => {
                block_resources.push(name.as_str());
            }
            Stmt::StaticAlloc { res, .. } => block_resources.push(res.as_str()),
            Stmt::SystemAlloc { res, release, .. } => {
                block_resources.push(res.as_str());
                block_resources.push(release.as_str());
            }
            _ => {}
        }
    }
    let mut out = Vec::new();
    for s in stmts {
        if let Some(t) = lower_stmt_erasing(ctx, s, &block_resources)? {
            out.push(t);
        }
    }
    Ok(format!("[{}]", out.join(", ")))
}

fn lower_stmt_erasing(
    ctx: &LowerCtx<'_>,
    s: &Stmt,
    erased_resources: &[&str],
) -> Result<Option<String>, String> {
    Ok(match s {
        // A ⊥ slot: the machine conflates "undeclared" with ⊥, and
        // definite initialization guarantees assignment-before-read.
        Stmt::Decl { init: None, .. } => None,
        Stmt::Decl {
            name,
            ty,
            init: Some(e),
            ..
        } if ty.is_resource() => lower_erased_resource_bind(ctx, name, e)?,
        Stmt::Decl {
            name,
            ty,
            init: Some(e),
            ..
        } => {
            validate_array_binding(*ty, name, e)?;
            Some(lower_bind(ctx, name, e)?)
        }
        Stmt::VarDecl {
            name,
            init,
            ty: Some(ty),
            ..
        } if ty.is_resource() => lower_erased_resource_bind(ctx, name, init)?,
        Stmt::VarDecl {
            name,
            init,
            ty: Some(ty),
            ..
        } => {
            validate_array_binding(*ty, name, init)?;
            Some(lower_bind(ctx, name, init)?)
        }
        Stmt::VarDecl { name, ty: None, .. } => {
            return Err(format!(
                "svm.local_type: inferred declaration `{name}` carries no checked type"
            ));
        }
        // `unsafe { ... }` is a marker with no machine step of its own.
        Stmt::Unsafe { body, .. } => {
            let inner = lower_block_erasing(ctx, body, erased_resources)?;
            // Splice the body in place: the block does not scope.
            Some(
                inner
                    .trim_start_matches('[')
                    .trim_end_matches(']')
                    .to_string(),
            )
        }
        Stmt::StaticAlloc { size, ptr, .. } => {
            Some(format!("(.rawAlloc \"{ptr}\" {})", lower_expr(ctx, size)?))
        }
        Stmt::SystemAlloc { size, ptr, .. } => {
            Some(format!("(.rawAlloc \"{ptr}\" {})", lower_expr(ctx, size)?))
        }
        Stmt::SystemDealloc { ptr, .. } => Some(format!("(.rawFree {})", lower_expr(ctx, ptr)?)),
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
            let id = next_loan();
            let loan = format!("_loan{id}");
            let i = format!("_li{id}");
            let t = format!("_lb{id}");
            let n = format!("(.len \"{array}\")");
            let at = format!("(.ptrAdd (.var \"{loan}\") (.var \"{i}\"))");
            let mut inner_erased = erased_resources.to_vec();
            inner_erased.push(res);
            let inner = lower_block_erasing(ctx, body, &inner_erased)?;
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
        Stmt::Assign { name, value, .. } if erased_resources.contains(&name.as_str()) => {
            lower_erased_resource_bind(ctx, name, value)?
        }
        Stmt::Assign { name, value, .. } => {
            validate_array_rebind(ctx, name)?;
            Some(lower_bind(ctx, name, value)?)
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
            let els = match else_block {
                Some(b) => lower_block_erasing(ctx, b, erased_resources)?,
                None => "[]".into(),
            };
            Some(format!(
                "(.ite {} {} {})",
                lower_expr(ctx, cond)?,
                lower_block_erasing(ctx, then_block, erased_resources)?,
                els
            ))
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
            Some(format!(
                "(.while {} {})",
                lower_expr(ctx, cond)?,
                lower_block_erasing(ctx, body, erased_resources)?
            ))
        }
        Stmt::Return { value: Some(e), .. } => {
            validate_array_return(ctx, e)?;
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
            ExprKind::RawOp { op, args, .. } => Some(match op {
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
            }),
            ExprKind::DeviceOp { op, args, .. } => Some(match op {
                DeviceOp::UartWrite => {
                    format!("(.uartWrite {})", lower_expr(ctx, &args[0])?)
                }
                DeviceOp::UartStatus => {
                    return Err("`uart_status` produces a value".into());
                }
            }),
            ExprKind::Call { .. } => Some(lower_call(ctx, &None, e)?),
            ExprKind::ResOp { op, args, .. } => lower_resource_op_stmt(ctx, *op, args)?,
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
        ResOp::TestUart => Ok(Some(format!(
            "(.testUartProfile {})",
            lower_expr(ctx, &args[0])?
        ))),
        ResOp::TestWorld
        | ResOp::OpenFileOf
        | ResOp::ResourceMapEmpty
        | ResOp::ResourceMapTake
        | ResOp::ResourceMapPut => Err(format!(
            "`{}` has interpreter-visible runtime state but no SVM statement",
            op.name()
        )),
        _ => {
            ensure_erased_resource_operands_inert(op, args)?;
            Ok(None)
        }
    }
}

/// An authority-only operation has no SVM statement, but source operands are
/// still evaluated before its erased result is produced. Erase the operation
/// only when each operand is syntactically known to have no runtime effect and
/// no trap. Anything richer must either gain an explicit discard/effect
/// lowering or remain outside the differential subset; silently dropping it
/// would make the harness compare a different program.
fn ensure_erased_resource_operands_inert(op: ResOp, args: &[Expr]) -> Result<(), String> {
    for (index, arg) in args.iter().enumerate() {
        let inert = match &arg.kind {
            // Checked literals are in range and cannot trap.
            ExprKind::IntLit(_) | ExprKind::BoolLit(_) => true,
            // Reading or borrowing an erased authority place performs no
            // runtime access. Resource variables deliberately have no cached
            // `Expr::ty`: the checker returns as soon as it validates their
            // expected affine type. The sealed primitive's operand position is
            // therefore the authority for erasedness when that annotation is
            // absent; a present annotation must still agree. This positional
            // guard also keeps an ordinary machine value from being discarded.
            ExprKind::Var(_) | ExprKind::SelfField { .. } | ExprKind::Borrow { .. } => {
                resource_operand_position(op, index) && arg.ty.map_or(true, Ty::is_resource)
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
    Ok(())
}

/// The resource-typed operands of each compiler-sealed primitive. Unlike an
/// ordinary call, these positions cannot be changed by user declarations and
/// exactly mirror the type rules in `check::infer_expr`.
fn resource_operand_position(op: ResOp, index: usize) -> bool {
    match op {
        ResOp::Join
        | ResOp::AllocatorPut
        | ResOp::AllocatorPutFree
        | ResOp::AllocatorPutHeader
        | ResOp::FreeBlockJoin => index < 2,
        ResOp::ResourceMapPut => index == 0 || index == 2,
        ResOp::SplitOff
        | ResOp::OpenFileOf
        | ResOp::AllocatorCreate
        | ResOp::AllocatorDestroy
        | ResOp::AllocatorTake
        | ResOp::AllocatorTakeFree
        | ResOp::AllocatorTakeHeader
        | ResOp::AllocatorStepHeader
        | ResOp::FreeBlockSplit
        | ResOp::FreeBlockLease
        | ResOp::BlockLeaseFree
        | ResOp::ResourceMapTake => index == 0,
        ResOp::TestWorld | ResOp::TestUart | ResOp::ResourceMapEmpty => false,
    }
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
        _ => Err("resource-valued expression is outside the SVM core subset".into()),
    }
}

/// `x = e;` — an assign, or (A-normalized, ADR 0005) a call when `e`
/// is exactly a call; calls nested deeper stay outside the subset.
fn lower_bind(ctx: &LowerCtx<'_>, name: &str, e: &Expr) -> Result<String, String> {
    match &e.kind {
        ExprKind::Call { .. } => lower_call(ctx, &Some(name.to_string()), e),
        ExprKind::DeviceOp {
            op: DeviceOp::UartStatus,
            ..
        } => Ok(format!("(.uartStatus \"{name}\")")),
        ExprKind::DeviceOp {
            op: DeviceOp::UartWrite,
            ..
        } => Err("`uart_write` produces no value".into()),
        ExprKind::RecordLit { record, args, .. } => {
            let ri = match e.ty {
                Some(Ty::Record(ri)) => ri,
                _ => {
                    return Err(format!(
                        "record literal `{record}(...)` carries no record type (unchecked program?)"
                    ));
                }
            };
            let decl = ctx.record(ri)?;
            if decl.name != *record {
                return Err(format!(
                    "record literal names `{record}` but carries tag for `{}` (lowering bug?)",
                    decl.name
                ));
            }
            if decl.fields.len() != args.len() {
                return Err(format!(
                    "record literal `{record}` has {} arguments for {} fields (unchecked program?)",
                    args.len(),
                    decl.fields.len()
                ));
            }
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
        } => Ok(format!(
            "(.rawLoad8 \"{name}\" {})",
            lower_expr(ctx, &args[0])?
        )),
        ExprKind::RawOp { op, args, .. } => match op {
            // Resource destinations are erased; the role-changing machine
            // instruction is nevertheless observable in the heap.
            RawOp::IntoCellU64 => Ok(format!("(.rawIntoCellU64 {})", lower_expr(ctx, &args[0])?)),
            RawOp::FromCellU64 => Ok(format!("(.rawFromCellU64 {})", lower_expr(ctx, &args[0])?)),
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
        },
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
    Ok(match &e.kind {
        ExprKind::IntLit(n) => {
            format!("(.intLit {} {})", lean_ty(expr_int_ty(e)?)?, int_lit(*n))
        }
        ExprKind::BoolLit(b) => format!("(.boolLit {b})"),
        ExprKind::Var(x) => format!("(.var \"{x}\")"),
        ExprKind::DeviceOp { op, .. } => {
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
    fn lowering_supports_boolean_option_construction_and_accessors() {
        let program = empty_program();
        let ctx = LowerCtx::bare(&program);
        let bool_option = Ty::Option(ValueTy::Bool);

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
        let ctx = LowerCtx::bare(&program);
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
        let ctx = LowerCtx::bare(&program);
        let bool_option = Ty::Option(ValueTy::Bool);
        let int_option = Ty::Option(ValueTy::Int(IntTy::I32));
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

        assert_eq!(render_rt_val(&program, &absent), "opt none");
        assert_eq!(render_rt_val(&program, &false_value), "opt some false");
        assert_eq!(render_rt_val(&program, &true_value), "opt some true");
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
        let resource_ctx = LowerCtx::bare(&resource_program);
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
        validate_expr_payloads(&resource_ctx, &erased_resource_call)
            .expect("erased resource places intentionally need no cached value type");
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
    fn lowering_rejects_non_integer_array_declaration() {
        let program = empty_program();
        let function = checked_fn(
            Ty::Unit,
            vec![Stmt::Decl {
                ty: Ty::Array(ValueTy::Bool, Mutability::Owned),
                name: "values".into(),
                name_span: Span::new(0, 0),
                init: None,
                mutable: false,
            }],
        );

        let error = lower_fn(&program, &function)
            .expect_err("a Boolean array must not inherit integer SVM lowering");
        assert_eq!(
            error,
            "svm.aggregate_payload_unsupported: declaration `values` has array payload `bool`; \
             the SVM currently lowers only concrete integer payloads"
        );
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
             the SVM currently lowers only concrete integer payloads"
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
                    init: None,
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
                "svm.array_alloc_length_type:",
            ),
            (
                allocation(
                    length(),
                    expr(ExprKind::IntLit(7), Ty::Int(IntTy::I32)),
                    Some(u8_array),
                ),
                "svm.array_alloc_init_type:",
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
            assert!(
                error.starts_with("svm.array_literal_element_type:"),
                "{error}"
            );
        }
    }

    #[test]
    fn named_array_operations_resolve_their_checked_local_type() {
        let program = empty_program();
        let array_ty = Ty::Array(ValueTy::Int(IntTy::U8), Mutability::Owned);
        let function = checked_fn(
            Ty::Unit,
            vec![Stmt::Decl {
                ty: array_ty,
                name: "bytes".into(),
                name_span: Span::new(0, 0),
                init: None,
                mutable: true,
            }],
        );
        let ctx = LowerCtx::for_function(&program, &function).unwrap();
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
                "svm.array_index_operand_type:",
            ),
            (
                index("missing", index_operand(), Some(Ty::Int(IntTy::U8))),
                "svm.array_place_type:",
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
        let ctx = LowerCtx::for_function(&program, &valid_function).unwrap();
        assert_eq!(
            lower_stmt_erasing(&ctx, &valid_store, &[]).unwrap(),
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
            (&bad_index, "svm.array_store_index_type:"),
            (&bad_value, "svm.array_store_value_type:"),
        ] {
            let preflight = validate_stmt_payloads(&ctx, std::slice::from_ref(statement))
                .expect_err("malformed store must fail SVM preflight");
            assert!(preflight.starts_with(diagnostic), "{preflight}");
            let lowering = lower_stmt_erasing(&ctx, statement, &[])
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
        assert!(error.starts_with("svm.array_binding_type:"), "{error}");

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
        assert!(error.starts_with("svm.array_return_type:"), "{error}");
    }

    #[test]
    fn erased_resource_op_accepts_unannotated_resource_place() {
        let mem = Expr {
            kind: ExprKind::Var("mem".into()),
            span: Span::new(0, 0),
            // Resource variables take the checker's early-return path, so a
            // successfully checked operand intentionally has no cached type.
            ty: None,
        };
        ensure_erased_resource_operands_inert(ResOp::AllocatorCreate, &[mem])
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
        let error = lower_resource_op_stmt(
            &LowerCtx::bare(&program),
            ResOp::SplitOff,
            &[span, division],
        )
        .expect_err("split_off(&mut mem, 1 / 0) must not disappear");
        assert!(error.contains("`split_off` operand 2"), "{error}");
    }
}
