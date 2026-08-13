//! Strict textual LLVM IR lowering for the verified scalar, Boolean-option,
//! and bounded POD-record core (ADR 0058).
//!
//! This first slice handles scalar storage, calls, comparisons, and structured
//! control flow.  A construct is either lowered with its Sable meaning or
//! rejected with a source diagnostic; there is no silent fallback and no
//! unchecked arithmetic.

use crate::VerifiedProgram;
use crate::ast::{BinOp, Expr, ExprKind, Fn, IntTy, Program, RecordDecl, Stmt, Ty, UnOp, ValueTy};
use crate::diag::Diagnostic;
use crate::span::Span;
use std::collections::{BTreeSet, HashMap, HashSet};

pub type BackendError = Diagnostic;

#[derive(Debug, Clone, Default)]
pub struct EmitOptions {
    /// A root-module, zero-argument `i32`/unit function for which a C `main`
    /// bridge should be emitted.  Without an entry, every production function
    /// in the flattened checked program is considered.
    pub entry: Option<String>,
}

/// Lower the exact program authorized by Lean.  The opaque capability keeps a
/// production caller from substituting a freshly loaded or mutated AST.
pub fn emit_verified(
    verified: &VerifiedProgram,
    options: &EmitOptions,
) -> Result<String, Vec<BackendError>> {
    if let Some(name) = verified.info().deferred.first() {
        return Err(vec![diag(
            "backend.deferred",
            "LLVM lowering does not yet accept deferred obligations",
            Span::new(0, 0),
            format!("`{name}` is compiled as a runtime proof escape"),
        )]);
    }
    if let Some((name, reason)) = verified.info().assumed.first() {
        return Err(vec![diag(
            "backend.assumed",
            "LLVM lowering does not accept assumed obligations",
            Span::new(0, 0),
            format!("`{name}` is an audited axiom: {reason}"),
        )]);
    }
    let mut ir = emit_program(verified.program(), verified.root_span_end(), options)?;
    let insert_at = ir.find('\n').map_or(ir.len(), |index| index + 1);
    ir.insert_str(
        insert_at,
        &format!(
            "; Sable artifact: {}\n; Sable proof environment: {}\n",
            verified.artifact_name(),
            verified.proof_fingerprint()
        ),
    );
    Ok(ir)
}

fn emit_program(
    program: &Program,
    root_span_end: usize,
    options: &EmitOptions,
) -> Result<String, Vec<BackendError>> {
    let selected = select_functions(program, root_span_end, options)?;
    validate_acyclic(program, &selected)?;
    for &index in &selected {
        validate_function(program, &program.fns[index], root_span_end)?;
    }

    let selected_set: HashSet<usize> = selected.iter().copied().collect();
    let mut out = String::from(
        "; Sable textual LLVM IR v0\n; Generated from a Lean-verified program (ADR 0058).\n\n",
    );
    let mut definitions = String::new();
    let mut support = ModuleSupport::default();
    if options.entry.is_none() {
        // Whole-module mode promises not to silently omit a supported type
        // declaration. Entry mode remains closure-based and registers only
        // records actually used by selected functions.
        for record in 0..program.records.len() {
            support.require_record(record);
        }
    }
    for (index, function) in program.fns.iter().enumerate() {
        if selected_set.contains(&index) {
            FunctionEmitter::new(program, function, &mut support).emit(&mut definitions)?;
            definitions.push('\n');
        }
    }

    if let Some(entry) = &options.entry {
        let function = program
            .fns
            .iter()
            .find(|function| function.name == *entry)
            .expect("entry selection validated above");
        emit_main_bridge(function, &mut definitions);
    }
    support.emit(program, &mut out);
    out.push_str(&definitions);
    Ok(out)
}

fn select_functions(
    program: &Program,
    root_span_end: usize,
    options: &EmitOptions,
) -> Result<Vec<usize>, Vec<BackendError>> {
    let mut selected = HashSet::new();
    let mut work = Vec::new();

    if let Some(entry) = &options.entry {
        let Some(index) = program
            .fns
            .iter()
            .position(|function| function.name == *entry)
        else {
            return Err(vec![diag(
                "backend.entry_missing",
                "LLVM entry function was not found",
                Span::new(0, 0),
                format!("no checked function named `{entry}`"),
            )]);
        };
        let function = &program.fns[index];
        if function.name.starts_with("test_") {
            return Err(vec![diag(
                "backend.test_unsupported",
                "dynamic tests are not production entry points",
                function.name_span,
                "choose a non-test function",
            )]);
        }
        if function.name_span.start >= root_span_end {
            return Err(vec![diag(
                "backend.entry_imported",
                "LLVM entry must belong to the root module",
                function.name_span,
                "this function was imported",
            )]);
        }
        if !function.params.is_empty() {
            return Err(vec![diag(
                "backend.entry_signature",
                "LLVM entry must take no parameters",
                function.name_span,
                "remove the entry parameters or choose a wrapper",
            )]);
        }
        if !function.pres.is_empty() {
            return Err(vec![diag(
                "backend.entry_precondition",
                "LLVM entry may not require a precondition",
                function.name_span,
                "a process entry has no verified caller to establish it",
            )]);
        }
        if !matches!(function.ret, Ty::Unit | Ty::Int(IntTy::I32)) {
            return Err(vec![diag(
                "backend.entry_signature",
                "LLVM entry must return `()` or `i32`",
                function.name_span,
                "use a zero-argument wrapper with a supported return type",
            )]);
        }
        work.push(index);
    } else {
        validate_whole_program_surface(program, root_span_end)?;
        work.extend(
            program
                .fns
                .iter()
                .enumerate()
                .filter(|(_, function)| !function.name.starts_with("test_"))
                .map(|(index, _)| index),
        );
    }

    while let Some(index) = work.pop() {
        if !selected.insert(index) {
            continue;
        }
        let function = &program.fns[index];
        let mut calls = Vec::new();
        collect_calls_block(&function.body, &mut calls);
        for (callee, span) in calls {
            let Some(callee_index) = program
                .fns
                .iter()
                .position(|function| function.name == callee)
            else {
                return Err(vec![diag(
                    "backend.call_missing",
                    "LLVM lowering could not resolve a direct call",
                    span,
                    format!("no checked function named `{callee}`"),
                )]);
            };
            if program.fns[callee_index].name.starts_with("test_") {
                return Err(vec![diag(
                    "backend.test_unsupported",
                    "production code may not lower a dynamic test call",
                    span,
                    format!("`{callee}` is a test function"),
                )]);
            }
            work.push(callee_index);
        }
    }

    let mut ordered: Vec<usize> = selected.into_iter().collect();
    ordered.sort_unstable();
    Ok(ordered)
}

fn validate_whole_program_surface(
    program: &Program,
    root_span_end: usize,
) -> Result<(), Vec<BackendError>> {
    if let Some(template) = program.fn_templates.first() {
        return Err(vec![unsupported(
            template.name_span,
            format!(
                "generic function template `{}` has no concrete LLVM ABI",
                template.name
            ),
        )]);
    }
    if let Some(class) = program
        .classes
        .first()
        .or_else(|| program.class_templates.first())
    {
        return Err(vec![unsupported(
            class.name_span,
            format!("class `{}` is outside the scalar LLVM subset", class.name),
        )]);
    }
    for (record, declaration) in program.records.iter().enumerate() {
        require_record_value(
            program,
            root_span_end,
            record,
            declaration.name_span,
            "record declaration",
        )?;
    }
    if let Some(trait_decl) = program.traits.first() {
        return Err(vec![unsupported(
            trait_decl.name_span,
            format!(
                "trait `{}` is outside the scalar LLVM subset",
                trait_decl.name
            ),
        )]);
    }
    if let Some(implementation) = program.impls.first() {
        return Err(vec![unsupported(
            implementation.span,
            format!(
                "implementation of `{}` is outside the scalar LLVM subset",
                implementation.trait_name
            ),
        )]);
    }
    Ok(())
}

fn validate_acyclic(program: &Program, selected: &[usize]) -> Result<(), Vec<BackendError>> {
    fn visit(
        program: &Program,
        index: usize,
        selected: &HashSet<usize>,
        states: &mut [u8],
    ) -> Result<(), BackendError> {
        if states[index] == 1 {
            let function = &program.fns[index];
            return Err(diag(
                "backend.recursion_unsupported",
                "recursive calls are outside the first LLVM subset",
                function.name_span,
                format!("`{}` participates in a recursive call cycle", function.name),
            ));
        }
        if states[index] == 2 {
            return Ok(());
        }
        states[index] = 1;
        let mut calls = Vec::new();
        collect_calls_block(&program.fns[index].body, &mut calls);
        for (callee, _) in calls {
            if let Some(next) = program.fns.iter().position(|f| f.name == callee)
                && selected.contains(&next)
            {
                visit(program, next, selected, states)?;
            }
        }
        states[index] = 2;
        Ok(())
    }

    let selected_set: HashSet<usize> = selected.iter().copied().collect();
    let mut states = vec![0; program.fns.len()];
    for &index in selected {
        if let Err(error) = visit(program, index, &selected_set, &mut states) {
            return Err(vec![error]);
        }
    }
    Ok(())
}

fn validate_function(
    program: &Program,
    function: &Fn,
    root_span_end: usize,
) -> Result<(), Vec<BackendError>> {
    if !function.type_params.is_empty() || !function.type_bounds.is_empty() {
        return Err(vec![unsupported(
            function.name_span,
            format!(
                "function `{}` retains generic declaration metadata after monomorphization",
                function.name
            ),
        )]);
    }
    if function.extern_info.is_some() {
        return Err(vec![unsupported(
            function.name_span,
            format!(
                "audited extern `{}` has no native implementation",
                function.name
            ),
        )]);
    }
    for parameter in &function.params {
        require_parameter_value(
            program,
            root_span_end,
            parameter.ty,
            parameter.span,
            "function parameter",
        )?;
    }
    require_runtime_type(
        program,
        root_span_end,
        function.ret,
        function.name_span,
        "function return type",
    )?;
    validate_block(program, &function.body, root_span_end)
}

fn validate_block(
    program: &Program,
    statements: &[Stmt],
    root_span_end: usize,
) -> Result<(), Vec<BackendError>> {
    for statement in statements {
        match statement {
            Stmt::Decl {
                ty,
                name_span,
                init,
                ..
            } => {
                require_local_value(program, root_span_end, *ty, *name_span, "local variable")?;
                if let Some(value) = init {
                    validate_expr(program, value, root_span_end)?;
                }
            }
            Stmt::VarDecl {
                ty,
                name_span,
                init,
                ..
            } => {
                let Some(ty) = *ty else {
                    return Err(vec![unsupported(
                        *name_span,
                        "inferred local is missing its checked type",
                    )]);
                };
                require_local_value(program, root_span_end, ty, *name_span, "inferred local")?;
                validate_expr(program, init, root_span_end)?;
            }
            Stmt::Assign { value, .. }
            | Stmt::ExprStmt(value)
            | Stmt::Return {
                value: Some(value), ..
            } => validate_expr(program, value, root_span_end)?,
            Stmt::Return { value: None, .. } | Stmt::Assert(_) => {}
            Stmt::Unsafe { body, .. } => validate_block(program, body, root_span_end)?,
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                validate_bool_expr(program, cond, "`if` condition", root_span_end)?;
                validate_block(program, then_block, root_span_end)?;
                if let Some(else_block) = else_block {
                    validate_block(program, else_block, root_span_end)?;
                }
            }
            Stmt::While { cond, body, .. } => {
                validate_bool_expr(program, cond, "`while` condition", root_span_end)?;
                validate_block(program, body, root_span_end)?;
            }
            Stmt::FieldAssign { field_span, .. } | Stmt::FieldStore { field_span, .. } => {
                return Err(vec![unsupported(
                    *field_span,
                    "class field mutation is outside the scalar LLVM subset",
                )]);
            }
            Stmt::Store { array_span, .. } => {
                return Err(vec![unsupported(
                    *array_span,
                    "array mutation is outside the scalar LLVM subset",
                )]);
            }
            Stmt::StaticAlloc { kw_span, .. }
            | Stmt::SystemAlloc { kw_span, .. }
            | Stmt::SystemDealloc { kw_span, .. }
            | Stmt::Expose { kw_span, .. } => {
                return Err(vec![unsupported(
                    *kw_span,
                    "raw/resource storage is outside the scalar LLVM subset",
                )]);
            }
        }
    }
    Ok(())
}

fn validate_expr(
    program: &Program,
    expression: &Expr,
    root_span_end: usize,
) -> Result<(), Vec<BackendError>> {
    match &expression.kind {
        ExprKind::IntLit(_) => {
            let Some(Ty::Int(integer)) = expression.ty else {
                return Err(vec![unsupported(
                    expression.span,
                    "integer literal is missing its checked integer type",
                )]);
            };
            require_concrete_integer(integer, expression.span, "integer literal")
        }
        ExprKind::BoolLit(_) => require_expr_type(expression, Ty::Bool, "Boolean literal"),
        ExprKind::Var(_) => {
            let ty = expression.ty.ok_or_else(|| {
                vec![unsupported(
                    expression.span,
                    "expression is missing its checked type",
                )]
            })?;
            require_runtime_type(program, root_span_end, ty, expression.span, "expression")
        }
        ExprKind::Call {
            callee,
            type_args,
            args,
            ..
        } => {
            if !type_args.is_empty() {
                return Err(vec![unsupported(
                    expression.span,
                    format!("call to `{callee}` retains type arguments after monomorphization"),
                )]);
            }
            let Some(function) = program.fns.iter().find(|function| function.name == *callee)
            else {
                return Err(vec![unsupported(
                    expression.span,
                    format!("unresolved call to `{callee}`"),
                )]);
            };
            if function.extern_info.is_some() {
                return Err(vec![unsupported(
                    expression.span,
                    format!("call to audited extern `{callee}`"),
                )]);
            }
            if args.len() != function.params.len() {
                return Err(vec![unsupported(
                    expression.span,
                    format!(
                        "call to `{callee}` has {} argument(s), but its checked signature has {}",
                        args.len(),
                        function.params.len()
                    ),
                )]);
            }
            for (argument, parameter) in args.iter().zip(&function.params) {
                validate_expr(program, argument, root_span_end)?;
                require_expr_type(argument, parameter.ty, "call argument")?;
            }
            require_runtime_type(
                program,
                root_span_end,
                function.ret,
                expression.span,
                "call result",
            )?;
            require_expr_type(expression, function.ret, "call result")
        }
        ExprKind::Unary {
            op: UnOp::Not,
            operand,
        } => validate_bool_expr(program, operand, "logical-not operand", root_span_end),
        ExprKind::Unary {
            op: UnOp::Neg,
            operand,
        } => {
            validate_expr(program, operand, root_span_end)?;
            let Some(Ty::Int(integer)) = operand.ty else {
                return Err(vec![unsupported(
                    operand.span,
                    "unary-minus operand is not a checked integer",
                )]);
            };
            if !integer.signed() {
                return Err(vec![unsupported(
                    operand.span,
                    "unary-minus operand is not a checked signed integer",
                )]);
            }
            require_expr_type(expression, Ty::Int(integer), "unary-minus result")
        }
        ExprKind::Binary {
            op: BinOp::And | BinOp::Or,
            lhs,
            rhs,
            ..
        } => {
            validate_bool_expr(program, lhs, "short-circuit left operand", root_span_end)?;
            validate_bool_expr(program, rhs, "short-circuit right operand", root_span_end)?;
            require_expr_type(expression, Ty::Bool, "short-circuit result")
        }
        ExprKind::Binary {
            op: op @ (BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq | BinOp::Ne),
            lhs,
            rhs,
            ..
        } => {
            validate_expr(program, lhs, root_span_end)?;
            validate_expr(program, rhs, root_span_end)?;
            let Some(Ty::Int(lhs_ty)) = lhs.ty else {
                return Err(vec![unsupported(
                    lhs.span,
                    format!("left operand of `{}` is not a checked integer", op.symbol()),
                )]);
            };
            if rhs.ty != Some(Ty::Int(lhs_ty)) {
                return Err(vec![unsupported(
                    rhs.span,
                    format!(
                        "right operand of `{}` does not have checked type `{}`",
                        op.symbol(),
                        lhs_ty.name()
                    ),
                )]);
            }
            require_expr_type(expression, Ty::Bool, "comparison result")
        }
        ExprKind::Binary {
            op: op @ (BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem),
            lhs,
            rhs,
            ..
        } => {
            validate_expr(program, lhs, root_span_end)?;
            validate_expr(program, rhs, root_span_end)?;
            let Some(Ty::Int(integer)) = lhs.ty else {
                return Err(vec![unsupported(
                    lhs.span,
                    format!("left operand of `{}` is not a checked integer", op.symbol()),
                )]);
            };
            if rhs.ty != Some(Ty::Int(integer)) {
                return Err(vec![unsupported(
                    rhs.span,
                    format!(
                        "right operand of `{}` does not have checked type `{}`",
                        op.symbol(),
                        integer.name()
                    ),
                )]);
            }
            require_expr_type(expression, Ty::Int(integer), "arithmetic result")
        }
        ExprKind::Widen { target, arg } => {
            validate_expr(program, arg, root_span_end)?;
            require_concrete_integer(*target, expression.span, "widen target")?;
            let Some(Ty::Int(source)) = arg.ty else {
                return Err(vec![unsupported(
                    arg.span,
                    "widen operand is not a checked integer",
                )]);
            };
            if source.min() < target.min() || source.max() > target.max() {
                return Err(vec![unsupported(
                    expression.span,
                    format!(
                        "widen from `{}` to `{}` is not value-preserving",
                        source.name(),
                        target.name()
                    ),
                )]);
            }
            require_expr_type(expression, Ty::Int(*target), "widen result")
        }
        ExprKind::Narrow { target, arg } => {
            validate_expr(program, arg, root_span_end)?;
            require_concrete_integer(*target, expression.span, "narrow target")?;
            if !matches!(arg.ty, Some(Ty::Int(_))) {
                return Err(vec![unsupported(
                    arg.span,
                    "narrow operand is not a checked integer",
                )]);
            }
            require_expr_type(expression, Ty::Int(*target), "narrow result")
        }
        ExprKind::SomeE(inner) => {
            require_expr_type(
                expression,
                Ty::Option(ValueTy::Bool),
                "Boolean option construction",
            )?;
            validate_bool_expr(program, inner, "Boolean option payload", root_span_end)
        }
        ExprKind::NoneE => require_expr_type(
            expression,
            Ty::Option(ValueTy::Bool),
            "Boolean option construction",
        ),
        ExprKind::IsSome { operand } => {
            validate_expr(program, operand, root_span_end)?;
            require_expr_type(
                operand,
                Ty::Option(ValueTy::Bool),
                "option accessor operand",
            )?;
            require_expr_type(expression, Ty::Bool, "`.is_some` result")
        }
        ExprKind::OptValue { operand } => {
            validate_expr(program, operand, root_span_end)?;
            require_expr_type(
                operand,
                Ty::Option(ValueTy::Bool),
                "option accessor operand",
            )?;
            require_expr_type(expression, Ty::Bool, "Boolean option payload")
        }
        ExprKind::RecordLit { record, args, .. } => {
            let Some(Ty::Record(record_index)) = expression.ty else {
                return Err(vec![unsupported(
                    expression.span,
                    "POD record construction is missing its checked nominal type",
                )]);
            };
            require_record_value(
                program,
                root_span_end,
                record_index,
                expression.span,
                "record construction",
            )?;
            let declaration = &program.records[record_index];
            if declaration.name != *record {
                return Err(vec![unsupported(
                    expression.span,
                    format!(
                        "record construction names `{record}` but carries checked type `{}`",
                        declaration.name
                    ),
                )]);
            }
            if args.len() != declaration.fields.len() {
                return Err(vec![unsupported(
                    expression.span,
                    format!(
                        "record `{record}` construction has {} field value(s), but the declaration has {}",
                        args.len(),
                        declaration.fields.len()
                    ),
                )]);
            }
            for (argument, field) in args.iter().zip(&declaration.fields) {
                validate_expr(program, argument, root_span_end)?;
                require_expr_type(argument, field.ty, "record field initializer")?;
            }
            Ok(())
        }
        ExprKind::RecordField { .. } => {
            let Some(Ty::Int(integer)) = expression.ty else {
                return Err(vec![unsupported(
                    expression.span,
                    "G1.4a record projection must have a concrete integer field type",
                )]);
            };
            require_concrete_integer(integer, expression.span, "record field projection")
        }
        _ => Err(vec![unsupported(
            expression.span,
            "expression is outside the scalar/Boolean-option/POD-record LLVM subset",
        )]),
    }
}

fn validate_bool_expr(
    program: &Program,
    expression: &Expr,
    role: &str,
    root_span_end: usize,
) -> Result<(), Vec<BackendError>> {
    validate_expr(program, expression, root_span_end)?;
    require_expr_type(expression, Ty::Bool, role)
}

fn require_expr_type(expression: &Expr, expected: Ty, role: &str) -> Result<(), Vec<BackendError>> {
    if expression.ty == Some(expected) {
        Ok(())
    } else {
        Err(vec![unsupported(
            expression.span,
            format!("{role} is missing checked type `{}`", expected.name()),
        )])
    }
}

/// Authorize one nominal record for G1.4a's *value* representation.  The
/// declaration's `#[layout]` and `#[offset]` metadata describes abstract raw
/// typed storage (ADR 0054); it is intentionally irrelevant to this internal
/// LLVM aggregate. Pointer-bearing records wait for a provenance-preserving
/// native pointer representation, and imported records wait for module ABI
/// identity rather than inheriting a flattened-program index by accident.
fn require_record_value(
    program: &Program,
    root_span_end: usize,
    record: usize,
    span: Span,
    role: &str,
) -> Result<(), Vec<BackendError>> {
    let Some(declaration) = program.records.get(record) else {
        return Err(vec![unsupported(
            span,
            format!("{role} carries record index {record}, outside the checked program"),
        )]);
    };
    if declaration.name_span.start >= root_span_end {
        return Err(vec![unsupported(
            span,
            format!(
                "{role} uses imported record `{}`; G1.4a has no cross-module record ABI",
                declaration.name
            ),
        )]);
    }
    for field in &declaration.fields {
        if !matches!(field.ty, Ty::Int(integer) if !matches!(integer, IntTy::TParam(_))) {
            return Err(vec![unsupported(
                field.span,
                format!(
                    "record `{}.{}` has field type `{}`; G1.4a lowers integer-only POD values",
                    declaration.name,
                    field.name,
                    field.ty.name()
                ),
            )]);
        }
    }
    Ok(())
}

fn require_runtime_type(
    program: &Program,
    root_span_end: usize,
    ty: Ty,
    span: Span,
    role: &str,
) -> Result<(), Vec<BackendError>> {
    match ty {
        Ty::Int(integer) if !matches!(integer, IntTy::TParam(_)) => Ok(()),
        Ty::Bool | Ty::Unit | Ty::Option(ValueTy::Bool) => Ok(()),
        Ty::Record(record) => require_record_value(program, root_span_end, record, span, role),
        _ => Err(vec![unsupported(
            span,
            format!(
                "{role} type `{}` has no supported LLVM runtime representation",
                ty.name()
            ),
        )]),
    }
}

fn require_local_value(
    program: &Program,
    root_span_end: usize,
    ty: Ty,
    span: Span,
    role: &str,
) -> Result<(), Vec<BackendError>> {
    match ty {
        Ty::Int(integer) if !matches!(integer, IntTy::TParam(_)) => Ok(()),
        Ty::Bool | Ty::Option(ValueTy::Bool) => Ok(()),
        Ty::Record(record) => require_record_value(program, root_span_end, record, span, role),
        _ => Err(vec![unsupported(
            span,
            format!(
                "{role} type `{}` has no supported LLVM local representation",
                ty.name()
            ),
        )]),
    }
}

fn require_parameter_value(
    program: &Program,
    root_span_end: usize,
    ty: Ty,
    span: Span,
    role: &str,
) -> Result<(), Vec<BackendError>> {
    match ty {
        Ty::Int(integer) if !matches!(integer, IntTy::TParam(_)) => Ok(()),
        Ty::Bool => Ok(()),
        Ty::Record(record) => require_record_value(program, root_span_end, record, span, role),
        _ => Err(vec![unsupported(
            span,
            format!(
                "{role} type `{}` has no first-slice LLVM value representation",
                ty.name()
            ),
        )]),
    }
}

fn require_concrete_integer(
    integer: IntTy,
    span: Span,
    role: &str,
) -> Result<(), Vec<BackendError>> {
    if matches!(integer, IntTy::TParam(_)) {
        Err(vec![unsupported(
            span,
            format!("{role} still contains an unmonomorphized integer type parameter"),
        )])
    } else {
        Ok(())
    }
}

// Trap kinds are part of the versioned `__sable_rt_trap_v1` hook.  Keep them
// explicit rather than deriving them from AST discriminants: the AST is an
// internal Rust detail, while embedding runtimes may inspect these numbers.
const TRAP_ADD_OVERFLOW: u32 = 1;
const TRAP_SUB_OVERFLOW: u32 = 2;
const TRAP_MUL_OVERFLOW: u32 = 3;
const TRAP_NEG_OVERFLOW: u32 = 4;
const TRAP_DIV_ZERO: u32 = 5;
const TRAP_DIV_OVERFLOW: u32 = 6;
const TRAP_NARROW_RANGE: u32 = 7;
const TRAP_OPTION_NONE: u32 = 8;

/// Internal aggregate representation for the first non-integer option slice.
/// This is deliberately not a C ABI promise: byte fields make the layout
/// unambiguous inside generated LLVM while ordinary Sable `bool` remains i1.
const LLVM_OPTION_BOOL: &str = "%sable.option.bool";

/// Nominal identity is the checked program's record tag, the same identity
/// carried by interpreter/SVM values. Numeric names are deterministic and
/// LLVM-safe without making source spelling or flattened indices a linkable
/// ABI: every generated function and type remains module-internal.
fn llvm_record_ty(record: usize) -> String {
    format!("%sable.record.{record}")
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum OverflowIntrinsic {
    SignedAdd(u32),
    UnsignedAdd(u32),
    SignedSub(u32),
    UnsignedSub(u32),
    SignedMul(u32),
    UnsignedMul(u32),
}

impl OverflowIntrinsic {
    fn for_binary(operator: BinOp, integer: IntTy) -> Self {
        match (operator, integer.signed()) {
            (BinOp::Add, true) => Self::SignedAdd(integer.bits()),
            (BinOp::Add, false) => Self::UnsignedAdd(integer.bits()),
            (BinOp::Sub, true) => Self::SignedSub(integer.bits()),
            (BinOp::Sub, false) => Self::UnsignedSub(integer.bits()),
            (BinOp::Mul, true) => Self::SignedMul(integer.bits()),
            (BinOp::Mul, false) => Self::UnsignedMul(integer.bits()),
            _ => unreachable!("overflow intrinsic requested for non-overflowing operator"),
        }
    }

    fn signed_sub(integer: IntTy) -> Self {
        debug_assert!(integer.signed());
        Self::SignedSub(integer.bits())
    }

    fn stem(self) -> &'static str {
        match self {
            Self::SignedAdd(_) => "sadd",
            Self::UnsignedAdd(_) => "uadd",
            Self::SignedSub(_) => "ssub",
            Self::UnsignedSub(_) => "usub",
            Self::SignedMul(_) => "smul",
            Self::UnsignedMul(_) => "umul",
        }
    }

    fn bits(self) -> u32 {
        match self {
            Self::SignedAdd(bits)
            | Self::UnsignedAdd(bits)
            | Self::SignedSub(bits)
            | Self::UnsignedSub(bits)
            | Self::SignedMul(bits)
            | Self::UnsignedMul(bits) => bits,
        }
    }

    fn name(self) -> String {
        format!("llvm.{}.with.overflow.i{}", self.stem(), self.bits())
    }

    fn declaration(self) -> String {
        let bits = self.bits();
        format!(
            "declare {{ i{bits}, i1 }} @{}(i{bits}, i{bits})",
            self.name()
        )
    }
}

#[derive(Default)]
struct ModuleSupport {
    overflow_intrinsics: BTreeSet<OverflowIntrinsic>,
    needs_trap: bool,
    needs_option_bool: bool,
    records: BTreeSet<usize>,
}

impl ModuleSupport {
    fn require_overflow(&mut self, intrinsic: OverflowIntrinsic) {
        self.overflow_intrinsics.insert(intrinsic);
        self.needs_trap = true;
    }

    fn require_trap(&mut self) {
        self.needs_trap = true;
    }

    fn require_option_bool(&mut self) {
        self.needs_option_bool = true;
    }

    fn require_record(&mut self, record: usize) {
        self.records.insert(record);
    }

    fn emit_record_type(record: usize, declaration: &RecordDecl, out: &mut String) {
        let fields = declaration
            .fields
            .iter()
            .map(|field| llvm_ty(field.ty))
            .collect::<Vec<_>>()
            .join(", ");
        // This is an ordinary-value carrier only. It does not encode the
        // source record's explicit raw-storage offsets, padding, or pointer
        // geometry and therefore grants no CRepr/BitwiseRepr promise.
        out.push_str(&format!(
            "; internal semantic value for record `{}`; not its raw-cell layout\n",
            declaration.name
        ));
        let body = if fields.is_empty() {
            "{}".to_string()
        } else {
            format!("{{ {fields} }}")
        };
        out.push_str(&format!("{} = type {body}\n\n", llvm_record_ty(record)));
    }

    fn emit(&self, program: &Program, out: &mut String) {
        if self.needs_option_bool {
            out.push_str(LLVM_OPTION_BOOL);
            out.push_str(" = type { i8, i8 }\n\n");
        }
        for record in &self.records {
            Self::emit_record_type(*record, &program.records[*record], out);
        }
        for intrinsic in &self.overflow_intrinsics {
            out.push_str(&intrinsic.declaration());
            out.push('\n');
        }
        if self.needs_trap {
            if !self.overflow_intrinsics.is_empty() {
                out.push('\n');
            }
            out.push_str(
                "; __sable_rt_trap_v1 kinds: 1 add, 2 sub, 3 mul, 4 neg, \
                 5 div/rem zero, 6 signed div overflow, 7 narrow range, \
                 8 option value of none\n\
                 ; type_info bytes: result/destination, lhs/source, rhs; \
                 type codes u8..u64,i8..i64 = 1..8\n\
                 declare void @llvm.trap() cold noreturn nounwind\n\n\
                 define weak void @__sable_rt_trap_v1(i32 %kind, i32 %type_info, \
                 i64 %lhs_bits, i64 %rhs_bits) nounwind {\n\
                 entry:\n\
                   ret void\n\
                 }\n\n\
                 define internal void @__sable_rt_fail_v1(i32 %kind, i32 %type_info, \
                 i64 %lhs_bits, i64 %rhs_bits) cold noreturn nounwind {\n\
                 entry:\n\
                   call void @__sable_rt_trap_v1(i32 %kind, i32 %type_info, \
                 i64 %lhs_bits, i64 %rhs_bits)\n\
                   call void @llvm.trap()\n\
                   unreachable\n\
                 }\n\n",
            );
        } else if !self.overflow_intrinsics.is_empty() {
            out.push('\n');
        }
    }
}

struct Local {
    ty: Ty,
    slot: String,
}

struct Value {
    ty: Ty,
    operand: Option<String>,
}

struct FunctionEmitter<'a, 'support> {
    program: &'a Program,
    function: &'a Fn,
    support: &'support mut ModuleSupport,
    locals: HashMap<String, Local>,
    next_local: usize,
    next_temp: usize,
    next_block: usize,
    lines: Vec<String>,
    /// Name of the block currently accepting instructions.  `None` means
    /// that its terminator has been emitted; a sibling or merge may still be
    /// started afterwards.
    current_block: Option<String>,
}

impl<'a, 'support> FunctionEmitter<'a, 'support> {
    fn new(program: &'a Program, function: &'a Fn, support: &'support mut ModuleSupport) -> Self {
        Self {
            program,
            function,
            support,
            locals: HashMap::new(),
            next_local: 0,
            next_temp: 0,
            next_block: 0,
            lines: Vec::new(),
            current_block: Some("entry".into()),
        }
    }

    fn emit(mut self, out: &mut String) -> Result<(), Vec<BackendError>> {
        self.require_type_support(self.function.ret);
        let parameter_types = self
            .function
            .params
            .iter()
            .map(|parameter| parameter.ty)
            .collect::<Vec<_>>();
        for ty in parameter_types {
            self.require_type_support(ty);
        }
        let parameters = self
            .function
            .params
            .iter()
            .enumerate()
            .map(|(index, parameter)| format!("{} %p{index}", llvm_ty(parameter.ty)))
            .collect::<Vec<_>>()
            .join(", ");
        out.push_str(&format!(
            "define internal {} @{}({parameters}) {{\nentry:\n",
            llvm_ty(self.function.ret),
            mangle(self.function)
        ));

        // LLVM permits allocas elsewhere, but keeping every stack slot in the
        // entry block gives branch-local Sable declarations one deterministic
        // representation without moving their initializer effects.
        let parameters = self
            .function
            .params
            .iter()
            .map(|parameter| (parameter.name.clone(), parameter.ty))
            .collect::<Vec<_>>();
        let mut declarations = Vec::new();
        collect_local_declarations(&self.function.body, &mut declarations);
        for (name, ty) in parameters.iter().chain(declarations.iter()) {
            self.require_type_support(*ty);
            let slot = self.new_slot();
            self.instruction(format!("{slot} = alloca {}", llvm_ty(*ty)));
            self.locals.insert(name.clone(), Local { ty: *ty, slot });
        }
        for (index, (name, ty)) in parameters.iter().enumerate() {
            let slot = self
                .locals
                .get(name)
                .expect("parameter slot was preallocated")
                .slot
                .clone();
            self.instruction(format!("store {} %p{index}, ptr {slot}", llvm_ty(*ty)));
        }

        self.emit_block(&self.function.body)?;
        if self.current_block.is_some() {
            if self.function.ret == Ty::Unit {
                self.terminate("ret void");
            } else {
                return Err(vec![diag(
                    "backend.invalid_fallthrough",
                    "non-unit function reaches the end during LLVM lowering",
                    self.function.name_span,
                    format!(
                        "checked function `{}` has a reachable path without a return",
                        self.function.name
                    ),
                )]);
            }
        }
        for line in &self.lines {
            out.push_str(line);
            out.push('\n');
        }
        out.push_str("}\n");
        Ok(())
    }

    fn require_type_support(&mut self, ty: Ty) {
        match ty {
            Ty::Option(ValueTy::Bool) => self.support.require_option_bool(),
            Ty::Record(record) => self.support.require_record(record),
            _ => {}
        }
    }

    fn emit_block(&mut self, statements: &[Stmt]) -> Result<(), Vec<BackendError>> {
        for statement in statements {
            if self.current_block.is_none() {
                break;
            }
            match statement {
                Stmt::Decl { ty, name, init, .. } => {
                    self.emit_decl(name, *ty, init.as_ref())?;
                }
                Stmt::VarDecl { name, init, ty, .. } => {
                    self.emit_decl(name, ty.expect("validated inferred type"), Some(init))?;
                }
                Stmt::Assign {
                    name,
                    name_span,
                    value,
                } => {
                    let emitted = self.emit_expr(value)?;
                    let Some(local) = self.locals.get(name) else {
                        return Err(vec![unsupported(
                            *name_span,
                            format!("LLVM local `{name}` was not declared"),
                        )]);
                    };
                    let ty = local.ty;
                    let slot = local.slot.clone();
                    self.instruction(format!(
                        "store {} {}, ptr {}",
                        llvm_ty(ty),
                        emitted.operand.expect("assignment value is non-unit"),
                        slot
                    ));
                }
                Stmt::ExprStmt(expression) => {
                    self.emit_expr(expression)?;
                }
                Stmt::Return { value, .. } => {
                    if let Some(value) = value {
                        let emitted = self.emit_expr(value)?;
                        if emitted.ty != self.function.ret {
                            return Err(vec![unsupported(
                                value.span,
                                format!(
                                    "return has checked type `{}` but function `{}` returns `{}`",
                                    emitted.ty.name(),
                                    self.function.name,
                                    self.function.ret.name()
                                ),
                            )]);
                        }
                        if emitted.ty == Ty::Unit {
                            // A unit-returning call is still effectful.  Its
                            // absent LLVM operand is consumed by `ret void`,
                            // rather than being unwrapped as a scalar.
                            self.terminate("ret void");
                        } else {
                            self.terminate(format!(
                                "ret {} {}",
                                llvm_ty(emitted.ty),
                                emitted.operand.expect("non-unit return value")
                            ));
                        }
                    } else {
                        if self.function.ret != Ty::Unit {
                            return Err(vec![unsupported(
                                self.function.name_span,
                                format!(
                                    "value-less return in non-unit function `{}`",
                                    self.function.name
                                ),
                            )]);
                        }
                        self.terminate("ret void");
                    }
                }
                Stmt::Assert(_) => {}
                Stmt::Unsafe { body, .. } => self.emit_block(body)?,
                Stmt::If {
                    cond,
                    then_block,
                    else_block,
                } => self.emit_if(cond, then_block, else_block.as_deref())?,
                Stmt::While { cond, body, .. } => self.emit_while(cond, body)?,
                _ => unreachable!("validated before lowering"),
            }
        }
        Ok(())
    }

    fn emit_decl(
        &mut self,
        name: &str,
        ty: Ty,
        init: Option<&Expr>,
    ) -> Result<(), Vec<BackendError>> {
        let Some(local) = self.locals.get(name) else {
            return Err(vec![unsupported(
                self.function.name_span,
                format!("LLVM local `{name}` has no preallocated slot"),
            )]);
        };
        let slot = local.slot.clone();
        if let Some(init) = init {
            let value = self.emit_expr(init)?;
            self.instruction(format!(
                "store {} {}, ptr {slot}",
                llvm_ty(ty),
                value.operand.expect("local initializer is non-unit")
            ));
        }
        Ok(())
    }

    fn emit_if(
        &mut self,
        condition: &Expr,
        then_block: &[Stmt],
        else_block: Option<&[Stmt]>,
    ) -> Result<(), Vec<BackendError>> {
        let condition = self.emit_expr(condition)?;
        let then_label = self.new_label("if.then");
        let merge_label = self.new_label("if.end");
        let false_label = else_block
            .map(|_| self.new_label("if.else"))
            .unwrap_or_else(|| merge_label.clone());
        self.terminate(format!(
            "br i1 {}, label %{then_label}, label %{false_label}",
            condition.operand.expect("validated boolean condition")
        ));

        self.start_block(then_label);
        self.emit_block(then_block)?;
        let then_reaches_merge = self.current_block.is_some();
        if then_reaches_merge {
            self.terminate(format!("br label %{merge_label}"));
        }

        let else_reaches_merge = if let Some(else_block) = else_block {
            self.start_block(false_label);
            self.emit_block(else_block)?;
            let reaches = self.current_block.is_some();
            if reaches {
                self.terminate(format!("br label %{merge_label}"));
            }
            reaches
        } else {
            // The condition's false edge targets the merge directly.
            true
        };

        if then_reaches_merge || else_reaches_merge {
            self.start_block(merge_label);
        }
        Ok(())
    }

    fn emit_while(&mut self, condition: &Expr, body: &[Stmt]) -> Result<(), Vec<BackendError>> {
        let header_label = self.new_label("while.head");
        self.terminate(format!("br label %{header_label}"));
        self.start_block(header_label.clone());

        // The condition is deliberately emitted in the header, not in the
        // preheader: calls and short-circuit RHS effects happen on every
        // iteration, exactly as they do in Sable.
        let condition = self.emit_expr(condition)?;
        let body_label = self.new_label("while.body");
        let exit_label = self.new_label("while.end");
        self.terminate(format!(
            "br i1 {}, label %{body_label}, label %{exit_label}",
            condition.operand.expect("validated boolean condition")
        ));

        self.start_block(body_label);
        self.emit_block(body)?;
        if self.current_block.is_some() {
            self.terminate(format!("br label %{header_label}"));
        }

        // The header's false edge always reaches this block, even when every
        // body path returns.
        self.start_block(exit_label);
        Ok(())
    }

    fn emit_expr(&mut self, expression: &Expr) -> Result<Value, Vec<BackendError>> {
        match &expression.kind {
            ExprKind::IntLit(value) => Ok(Value {
                ty: expression.ty.expect("validated literal type"),
                operand: Some(value.to_string()),
            }),
            ExprKind::BoolLit(value) => Ok(Value {
                ty: Ty::Bool,
                operand: Some(if *value { "1" } else { "0" }.into()),
            }),
            ExprKind::Var(name) => {
                let Some(local) = self.locals.get(name) else {
                    return Err(vec![unsupported(
                        expression.span,
                        format!("LLVM local `{name}` was not declared"),
                    )]);
                };
                let ty = local.ty;
                let slot = local.slot.clone();
                let temp = self.new_temp();
                self.instruction(format!("{temp} = load {}, ptr {slot}", llvm_ty(ty)));
                Ok(Value {
                    ty,
                    operand: Some(temp),
                })
            }
            ExprKind::RecordLit { record, args, .. } => {
                let Ty::Record(record_index) = expression
                    .ty
                    .expect("validated record construction has a nominal type")
                else {
                    unreachable!("validated record construction type")
                };
                self.support.require_record(record_index);
                let declaration = self.program.records[record_index].clone();
                debug_assert_eq!(declaration.name.as_str(), record.as_str());

                // All G1.4a fields are integers, so zero is a valid defined
                // seed. Every declared field is then overwritten in source
                // order; evaluating each argument before the next preserves
                // Sable's left-to-right call/trap order.
                let record_ty = llvm_record_ty(record_index);
                let mut aggregate = "zeroinitializer".to_string();
                for (index, (argument, field)) in args.iter().zip(&declaration.fields).enumerate() {
                    let value = self.emit_expr(argument)?;
                    let next = self.new_temp();
                    self.instruction(format!(
                        "{next} = insertvalue {record_ty} {aggregate}, {} {}, {index}",
                        llvm_ty(field.ty),
                        value.operand.expect("validated record field value")
                    ));
                    aggregate = next;
                }
                Ok(Value {
                    ty: Ty::Record(record_index),
                    operand: Some(aggregate),
                })
            }
            ExprKind::RecordField {
                obj,
                obj_span,
                field,
            } => {
                let Some(local) = self.locals.get(obj) else {
                    return Err(vec![unsupported(
                        *obj_span,
                        format!("LLVM record local `{obj}` was not declared"),
                    )]);
                };
                let (record_index, slot) = match local.ty {
                    Ty::Record(record_index) => (record_index, local.slot.clone()),
                    other => {
                        return Err(vec![unsupported(
                            *obj_span,
                            format!(
                                "record projection base `{obj}` has checked LLVM type `{}`",
                                other.name()
                            ),
                        )]);
                    }
                };
                self.support.require_record(record_index);
                let declaration = self.program.records[record_index].clone();
                let Some((field_index, declaration_field)) = declaration
                    .fields
                    .iter()
                    .enumerate()
                    .find(|(_, declaration_field)| declaration_field.name == *field)
                    .map(|(index, field)| (index, field.clone()))
                else {
                    return Err(vec![unsupported(
                        expression.span,
                        format!("record `{}` has no field `{field}`", declaration.name),
                    )]);
                };
                if expression.ty != Some(declaration_field.ty) {
                    return Err(vec![unsupported(
                        expression.span,
                        format!(
                            "record `{}.{field}` is annotated `{}` instead of `{}`",
                            declaration.name,
                            expression.ty.map_or_else(|| "<missing>".into(), Ty::name),
                            declaration_field.ty.name()
                        ),
                    )]);
                }
                let record_ty = llvm_record_ty(record_index);
                let aggregate = self.new_temp();
                self.instruction(format!("{aggregate} = load {record_ty}, ptr {slot}"));
                let value = self.new_temp();
                self.instruction(format!(
                    "{value} = extractvalue {record_ty} {aggregate}, {field_index}"
                ));
                Ok(Value {
                    ty: declaration_field.ty,
                    operand: Some(value),
                })
            }
            ExprKind::SomeE(inner) => {
                self.support.require_option_bool();
                let value = self.emit_expr(inner)?;
                let payload = self.new_temp();
                self.instruction(format!(
                    "{payload} = zext i1 {} to i8",
                    value.operand.expect("validated Boolean option payload")
                ));
                let tagged = self.new_temp();
                self.instruction(format!(
                    "{tagged} = insertvalue {LLVM_OPTION_BOOL} zeroinitializer, i8 1, 0"
                ));
                let result = self.new_temp();
                self.instruction(format!(
                    "{result} = insertvalue {LLVM_OPTION_BOOL} {tagged}, i8 {payload}, 1"
                ));
                Ok(Value {
                    ty: Ty::Option(ValueTy::Bool),
                    operand: Some(result),
                })
            }
            ExprKind::NoneE => {
                self.support.require_option_bool();
                Ok(Value {
                    ty: Ty::Option(ValueTy::Bool),
                    operand: Some("zeroinitializer".into()),
                })
            }
            ExprKind::IsSome { operand } => {
                self.support.require_option_bool();
                let option = self.emit_expr(operand)?;
                let option = option
                    .operand
                    .expect("validated Boolean option accessor operand");
                let tag = self.new_temp();
                self.instruction(format!(
                    "{tag} = extractvalue {LLVM_OPTION_BOOL} {option}, 0"
                ));
                let present = self.new_temp();
                self.instruction(format!("{present} = icmp ne i8 {tag}, 0"));
                Ok(Value {
                    ty: Ty::Bool,
                    operand: Some(present),
                })
            }
            ExprKind::OptValue { operand } => {
                self.support.require_option_bool();
                let option = self.emit_expr(operand)?;
                let option = option
                    .operand
                    .expect("validated Boolean option accessor operand");
                let tag = self.new_temp();
                self.instruction(format!(
                    "{tag} = extractvalue {LLVM_OPTION_BOOL} {option}, 0"
                ));
                let absent = self.new_temp();
                self.instruction(format!("{absent} = icmp eq i8 {tag}, 0"));
                self.emit_untyped_trap_guard(&absent, TRAP_OPTION_NONE);

                // Extract only on the success edge. Besides pinning the
                // source evaluation order, this keeps the partial operation's
                // runtime guard visibly dominant in unoptimized IR.
                let payload = self.new_temp();
                self.instruction(format!(
                    "{payload} = extractvalue {LLVM_OPTION_BOOL} {option}, 1"
                ));
                let result = self.new_temp();
                self.instruction(format!("{result} = trunc i8 {payload} to i1"));
                Ok(Value {
                    ty: Ty::Bool,
                    operand: Some(result),
                })
            }
            ExprKind::Unary {
                op: UnOp::Not,
                operand,
            } => {
                let operand = self.emit_expr(operand)?;
                let temp = self.new_temp();
                self.instruction(format!(
                    "{temp} = xor i1 {}, true",
                    operand.operand.expect("boolean operand")
                ));
                Ok(Value {
                    ty: Ty::Bool,
                    operand: Some(temp),
                })
            }
            ExprKind::Unary {
                op: UnOp::Neg,
                operand,
            } => {
                let operand = self.emit_expr(operand)?;
                let Ty::Int(integer) = operand.ty else {
                    unreachable!("validated unary-minus operand")
                };
                self.emit_checked_neg(
                    integer,
                    operand.operand.expect("integer unary-minus operand"),
                )
            }
            ExprKind::Call { callee, args, .. } => {
                let function = self
                    .program
                    .fns
                    .iter()
                    .find(|function| function.name == *callee)
                    .expect("validated callee");
                let mut lowered = Vec::with_capacity(args.len());
                for argument in args {
                    let value = self.emit_expr(argument)?;
                    lowered.push(format!(
                        "{} {}",
                        llvm_ty(value.ty),
                        value.operand.expect("call arguments are non-unit")
                    ));
                }
                let call = format!(
                    "call {} @{}({})",
                    llvm_ty(function.ret),
                    mangle(function),
                    lowered.join(", ")
                );
                if function.ret == Ty::Unit {
                    self.instruction(call);
                    Ok(Value {
                        ty: Ty::Unit,
                        operand: None,
                    })
                } else {
                    let temp = self.new_temp();
                    self.instruction(format!("{temp} = {call}"));
                    Ok(Value {
                        ty: function.ret,
                        operand: Some(temp),
                    })
                }
            }
            ExprKind::Binary {
                op: op @ (BinOp::And | BinOp::Or),
                lhs,
                rhs,
                ..
            } => self.emit_short_circuit(*op, lhs, rhs),
            ExprKind::Binary {
                op: op @ (BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq | BinOp::Ne),
                lhs,
                rhs,
                ..
            } => {
                let lhs = self.emit_expr(lhs)?;
                let rhs = self.emit_expr(rhs)?;
                let Ty::Int(integer) = lhs.ty else {
                    unreachable!("validated comparison operand")
                };
                let predicate = match op {
                    BinOp::Eq => "eq",
                    BinOp::Ne => "ne",
                    BinOp::Lt if integer.signed() => "slt",
                    BinOp::Le if integer.signed() => "sle",
                    BinOp::Gt if integer.signed() => "sgt",
                    BinOp::Ge if integer.signed() => "sge",
                    BinOp::Lt => "ult",
                    BinOp::Le => "ule",
                    BinOp::Gt => "ugt",
                    BinOp::Ge => "uge",
                    _ => unreachable!("comparison operator validated above"),
                };
                let temp = self.new_temp();
                self.instruction(format!(
                    "{temp} = icmp {predicate} {} {}, {}",
                    llvm_ty(lhs.ty),
                    lhs.operand.expect("integer comparison lhs"),
                    rhs.operand.expect("integer comparison rhs")
                ));
                Ok(Value {
                    ty: Ty::Bool,
                    operand: Some(temp),
                })
            }
            ExprKind::Binary {
                op: op @ (BinOp::Add | BinOp::Sub | BinOp::Mul),
                lhs,
                rhs,
                ..
            } => {
                // Evaluation order is observable through calls and traps:
                // finish the left expression before beginning the right.
                let lhs = self.emit_expr(lhs)?;
                let rhs = self.emit_expr(rhs)?;
                let Ty::Int(integer) = lhs.ty else {
                    unreachable!("validated arithmetic operand")
                };
                self.emit_checked_binary(
                    *op,
                    integer,
                    lhs.operand.expect("integer arithmetic lhs"),
                    rhs.operand.expect("integer arithmetic rhs"),
                )
            }
            ExprKind::Binary {
                op: op @ (BinOp::Div | BinOp::Rem),
                lhs,
                rhs,
                ..
            } => {
                let lhs = self.emit_expr(lhs)?;
                let rhs = self.emit_expr(rhs)?;
                let Ty::Int(integer) = lhs.ty else {
                    unreachable!("validated division operand")
                };
                self.emit_div_rem(
                    *op,
                    integer,
                    lhs.operand.expect("integer division lhs"),
                    rhs.operand.expect("integer division rhs"),
                )
            }
            ExprKind::Widen { target, arg } => {
                let value = self.emit_expr(arg)?;
                let Ty::Int(source) = value.ty else {
                    unreachable!("validated widen operand")
                };
                let operand = value.operand.expect("integer widen operand");
                if source.bits() == target.bits() {
                    Ok(Value {
                        ty: Ty::Int(*target),
                        operand: Some(operand),
                    })
                } else {
                    let temp = self.new_temp();
                    let extension = if source.signed() { "sext" } else { "zext" };
                    self.instruction(format!(
                        "{temp} = {extension} {} {operand} to {}",
                        llvm_ty(Ty::Int(source)),
                        llvm_ty(Ty::Int(*target))
                    ));
                    Ok(Value {
                        ty: Ty::Int(*target),
                        operand: Some(temp),
                    })
                }
            }
            ExprKind::Narrow { target, arg } => {
                let value = self.emit_expr(arg)?;
                let Ty::Int(source) = value.ty else {
                    unreachable!("validated narrow operand")
                };
                self.emit_narrow(
                    source,
                    *target,
                    value.operand.expect("integer narrow operand"),
                )
            }
            _ => unreachable!("validated before lowering"),
        }
    }

    fn emit_checked_binary(
        &mut self,
        operator: BinOp,
        integer: IntTy,
        lhs: String,
        rhs: String,
    ) -> Result<Value, Vec<BackendError>> {
        let intrinsic = OverflowIntrinsic::for_binary(operator, integer);
        self.support.require_overflow(intrinsic);
        let llvm_integer = llvm_ty(Ty::Int(integer));
        let pair = self.new_temp();
        self.instruction(format!(
            "{pair} = call {{ {llvm_integer}, i1 }} @{}({llvm_integer} {lhs}, \
             {llvm_integer} {rhs})",
            intrinsic.name()
        ));
        let result = self.new_temp();
        self.instruction(format!(
            "{result} = extractvalue {{ {llvm_integer}, i1 }} {pair}, 0"
        ));
        let overflow = self.new_temp();
        self.instruction(format!(
            "{overflow} = extractvalue {{ {llvm_integer}, i1 }} {pair}, 1"
        ));
        let kind = match operator {
            BinOp::Add => TRAP_ADD_OVERFLOW,
            BinOp::Sub => TRAP_SUB_OVERFLOW,
            BinOp::Mul => TRAP_MUL_OVERFLOW,
            _ => unreachable!("checked binary operator"),
        };
        self.emit_trap_guard(
            &overflow,
            kind,
            integer,
            integer,
            &lhs,
            Some((integer, rhs.as_str())),
        );
        Ok(Value {
            ty: Ty::Int(integer),
            operand: Some(result),
        })
    }

    fn emit_checked_neg(
        &mut self,
        integer: IntTy,
        operand: String,
    ) -> Result<Value, Vec<BackendError>> {
        let intrinsic = OverflowIntrinsic::signed_sub(integer);
        self.support.require_overflow(intrinsic);
        let llvm_integer = llvm_ty(Ty::Int(integer));
        let pair = self.new_temp();
        self.instruction(format!(
            "{pair} = call {{ {llvm_integer}, i1 }} @{}({llvm_integer} 0, \
             {llvm_integer} {operand})",
            intrinsic.name()
        ));
        let result = self.new_temp();
        self.instruction(format!(
            "{result} = extractvalue {{ {llvm_integer}, i1 }} {pair}, 0"
        ));
        let overflow = self.new_temp();
        self.instruction(format!(
            "{overflow} = extractvalue {{ {llvm_integer}, i1 }} {pair}, 1"
        ));
        self.emit_trap_guard(
            &overflow,
            TRAP_NEG_OVERFLOW,
            integer,
            integer,
            &operand,
            None,
        );
        Ok(Value {
            ty: Ty::Int(integer),
            operand: Some(result),
        })
    }

    fn emit_div_rem(
        &mut self,
        operator: BinOp,
        integer: IntTy,
        lhs: String,
        rhs: String,
    ) -> Result<Value, Vec<BackendError>> {
        self.support.require_trap();
        let llvm_integer = llvm_ty(Ty::Int(integer));

        // LLVM division by zero is immediate undefined behavior.  This guard
        // dominates every `*div`/`*rem` instruction emitted below.
        let is_zero = self.new_temp();
        self.instruction(format!("{is_zero} = icmp eq {llvm_integer} {rhs}, 0"));
        self.emit_trap_guard(
            &is_zero,
            TRAP_DIV_ZERO,
            integer,
            integer,
            &lhs,
            Some((integer, rhs.as_str())),
        );

        if !integer.signed() {
            let result = self.new_temp();
            let instruction = if operator == BinOp::Div {
                "udiv"
            } else {
                "urem"
            };
            self.instruction(format!(
                "{result} = {instruction} {llvm_integer} {lhs}, {rhs}"
            ));
            return Ok(Value {
                ty: Ty::Int(integer),
                operand: Some(result),
            });
        }

        let is_min = self.new_temp();
        self.instruction(format!(
            "{is_min} = icmp eq {llvm_integer} {lhs}, {}",
            integer.min()
        ));
        let is_negative_one = self.new_temp();
        self.instruction(format!(
            "{is_negative_one} = icmp eq {llvm_integer} {rhs}, -1"
        ));
        let is_min_over_negative_one = self.new_temp();
        self.instruction(format!(
            "{is_min_over_negative_one} = and i1 {is_min}, {is_negative_one}"
        ));

        if operator == BinOp::Div {
            // LLVM's `sdiv min, -1` is poison/undefined even without flags;
            // Sable gives that quotient a checked overflow trap.
            self.emit_trap_guard(
                &is_min_over_negative_one,
                TRAP_DIV_OVERFLOW,
                integer,
                integer,
                &lhs,
                Some((integer, rhs.as_str())),
            );
            let quotient = self.new_temp();
            self.instruction(format!("{quotient} = sdiv {llvm_integer} {lhs}, {rhs}"));
            let remainder = self.new_temp();
            self.instruction(format!("{remainder} = srem {llvm_integer} {lhs}, {rhs}"));
            let quotient = self.emit_euclidean_quotient(integer, quotient, remainder, &rhs);
            Ok(Value {
                ty: Ty::Int(integer),
                operand: Some(quotient),
            })
        } else {
            // Sable's `min % -1` is zero.  LLVM makes even `srem min, -1`
            // undefined, so route that pair around the instruction and merge
            // the language-defined zero with the ordinary truncating result.
            let special_label = self.new_label("rem.min-neg-one");
            let normal_label = self.new_label("rem.normal");
            let merge_label = self.new_label("rem.merge");
            self.terminate(format!(
                "br i1 {is_min_over_negative_one}, label %{special_label}, label %{normal_label}"
            ));

            self.start_block(normal_label);
            let remainder = self.new_temp();
            self.instruction(format!("{remainder} = srem {llvm_integer} {lhs}, {rhs}"));
            let normal_predecessor = self.current_label().to_owned();
            self.terminate(format!("br label %{merge_label}"));

            self.start_block(special_label);
            let special_predecessor = self.current_label().to_owned();
            self.terminate(format!("br label %{merge_label}"));

            self.start_block(merge_label);
            let merged = self.new_temp();
            self.instruction(format!(
                "{merged} = phi {llvm_integer} [ {remainder}, %{normal_predecessor} ], \
                 [ 0, %{special_predecessor} ]"
            ));
            let remainder = self.emit_euclidean_remainder(integer, merged, &rhs);
            Ok(Value {
                ty: Ty::Int(integer),
                operand: Some(remainder),
            })
        }
    }

    fn emit_euclidean_quotient(
        &mut self,
        integer: IntTy,
        quotient: String,
        remainder: String,
        divisor: &str,
    ) -> String {
        let llvm_integer = llvm_ty(Ty::Int(integer));
        let remainder_negative = self.new_temp();
        self.instruction(format!(
            "{remainder_negative} = icmp slt {llvm_integer} {remainder}, 0"
        ));
        let divisor_negative = self.new_temp();
        self.instruction(format!(
            "{divisor_negative} = icmp slt {llvm_integer} {divisor}, 0"
        ));

        // These internal corrections are mathematically in range whenever a
        // negative truncating remainder exists.  Plain unflagged LLVM add/sub
        // is total modular arithmetic, so even the unselected candidate
        // cannot introduce poison.
        let incremented = self.new_temp();
        self.instruction(format!("{incremented} = add {llvm_integer} {quotient}, 1"));
        let decremented = self.new_temp();
        self.instruction(format!("{decremented} = sub {llvm_integer} {quotient}, 1"));
        let correction = self.new_temp();
        self.instruction(format!(
            "{correction} = select i1 {divisor_negative}, {llvm_integer} {incremented}, \
             {llvm_integer} {decremented}"
        ));
        let result = self.new_temp();
        self.instruction(format!(
            "{result} = select i1 {remainder_negative}, {llvm_integer} {correction}, \
             {llvm_integer} {quotient}"
        ));
        result
    }

    fn emit_euclidean_remainder(
        &mut self,
        integer: IntTy,
        remainder: String,
        divisor: &str,
    ) -> String {
        let llvm_integer = llvm_ty(Ty::Int(integer));
        let remainder_negative = self.new_temp();
        self.instruction(format!(
            "{remainder_negative} = icmp slt {llvm_integer} {remainder}, 0"
        ));
        let divisor_negative = self.new_temp();
        self.instruction(format!(
            "{divisor_negative} = icmp slt {llvm_integer} {divisor}, 0"
        ));
        let add_divisor = self.new_temp();
        self.instruction(format!(
            "{add_divisor} = add {llvm_integer} {remainder}, {divisor}"
        ));
        let subtract_divisor = self.new_temp();
        self.instruction(format!(
            "{subtract_divisor} = sub {llvm_integer} {remainder}, {divisor}"
        ));
        let correction = self.new_temp();
        self.instruction(format!(
            "{correction} = select i1 {divisor_negative}, {llvm_integer} {subtract_divisor}, \
             {llvm_integer} {add_divisor}"
        ));
        let result = self.new_temp();
        self.instruction(format!(
            "{result} = select i1 {remainder_negative}, {llvm_integer} {correction}, \
             {llvm_integer} {remainder}"
        ));
        result
    }

    fn emit_narrow(
        &mut self,
        source: IntTy,
        target: IntTy,
        operand: String,
    ) -> Result<Value, Vec<BackendError>> {
        self.support.require_trap();
        let source_ty = llvm_ty(Ty::Int(source));
        let extension = if source.signed() { "sext" } else { "zext" };
        let wide = self.new_temp();
        self.instruction(format!(
            "{wide} = {extension} {source_ty} {operand} to i128"
        ));
        let below = self.new_temp();
        self.instruction(format!("{below} = icmp slt i128 {wide}, {}", target.min()));
        let above = self.new_temp();
        self.instruction(format!("{above} = icmp sgt i128 {wide}, {}", target.max()));
        let outside = self.new_temp();
        self.instruction(format!("{outside} = or i1 {below}, {above}"));
        self.emit_trap_guard(&outside, TRAP_NARROW_RANGE, target, source, &operand, None);
        let result = self.new_temp();
        self.instruction(format!(
            "{result} = trunc i128 {wide} to {}",
            llvm_ty(Ty::Int(target))
        ));
        Ok(Value {
            ty: Ty::Int(target),
            operand: Some(result),
        })
    }

    fn emit_trap_guard(
        &mut self,
        failure: &str,
        kind: u32,
        info_type: IntTy,
        lhs_type: IntTy,
        lhs: &str,
        rhs: Option<(IntTy, &str)>,
    ) {
        // The ABI carries raw source-width operand bits.  Zero extension is
        // intentional even for signed inputs: diagnostics can reconstruct the
        // signed value from `type_info`, while the payload remains lossless.
        let lhs_bits = self.emit_raw_bits(lhs_type, lhs);
        let rhs_bits = rhs
            .map(|(ty, value)| self.emit_raw_bits(ty, value))
            .unwrap_or_else(|| "0".into());
        self.emit_trap_branch(
            failure,
            kind,
            packed_type_info(info_type, lhs_type, rhs.map(|(ty, _)| ty)),
            &lhs_bits,
            &rhs_bits,
        );
    }

    fn emit_untyped_trap_guard(&mut self, failure: &str, kind: u32) {
        self.emit_trap_branch(failure, kind, 0, "0", "0");
    }

    fn emit_trap_branch(
        &mut self,
        failure: &str,
        kind: u32,
        type_info: u32,
        lhs_bits: &str,
        rhs_bits: &str,
    ) {
        self.support.require_trap();
        let trap_label = self.new_label("trap");
        let continue_label = self.new_label("trap.ok");
        self.terminate(format!(
            "br i1 {failure}, label %{trap_label}, label %{continue_label}"
        ));

        self.start_block(trap_label);
        self.instruction(format!(
            "call void @__sable_rt_fail_v1(i32 {kind}, i32 {type_info}, i64 {lhs_bits}, i64 {rhs_bits})"
        ));
        self.terminate("unreachable");

        self.start_block(continue_label);
    }

    fn emit_raw_bits(&mut self, integer: IntTy, operand: &str) -> String {
        if integer.bits() == 64 {
            operand.to_owned()
        } else {
            let temp = self.new_temp();
            self.instruction(format!(
                "{temp} = zext {} {operand} to i64",
                llvm_ty(Ty::Int(integer))
            ));
            temp
        }
    }

    fn emit_short_circuit(
        &mut self,
        operator: BinOp,
        lhs: &Expr,
        rhs: &Expr,
    ) -> Result<Value, Vec<BackendError>> {
        let lhs = self.emit_expr(lhs)?;
        let lhs_end = self.current_label().to_owned();
        let rhs_label = self.new_label("sc.rhs");
        let merge_label = self.new_label("sc.end");
        let lhs_operand = lhs.operand.expect("validated boolean lhs");
        match operator {
            BinOp::And => self.terminate(format!(
                "br i1 {lhs_operand}, label %{rhs_label}, label %{merge_label}"
            )),
            BinOp::Or => self.terminate(format!(
                "br i1 {lhs_operand}, label %{merge_label}, label %{rhs_label}"
            )),
            _ => unreachable!("short-circuit operator"),
        }

        self.start_block(rhs_label);
        let rhs = self.emit_expr(rhs)?;
        let rhs_end = self.current_label().to_owned();
        let rhs_operand = rhs.operand.expect("validated boolean rhs");
        self.terminate(format!("br label %{merge_label}"));

        self.start_block(merge_label);
        let temp = self.new_temp();
        let short_value = if operator == BinOp::And { "0" } else { "1" };
        self.instruction(format!(
            "{temp} = phi i1 [ {short_value}, %{lhs_end} ], [ {rhs_operand}, %{rhs_end} ]"
        ));
        Ok(Value {
            ty: Ty::Bool,
            operand: Some(temp),
        })
    }

    fn instruction(&mut self, instruction: impl Into<String>) {
        debug_assert!(self.current_block.is_some(), "instruction after terminator");
        self.lines.push(format!("  {}", instruction.into()));
    }

    fn terminate(&mut self, terminator: impl Into<String>) {
        self.instruction(terminator);
        self.current_block = None;
    }

    fn start_block(&mut self, label: String) {
        debug_assert!(self.current_block.is_none(), "new block before terminator");
        self.lines.push(format!("{label}:"));
        self.current_block = Some(label);
    }

    fn current_label(&self) -> &str {
        self.current_block
            .as_deref()
            .expect("expression lowering left a terminated block")
    }

    fn new_slot(&mut self) -> String {
        let slot = format!("%v{}", self.next_local);
        self.next_local += 1;
        slot
    }

    fn new_temp(&mut self) -> String {
        let temp = format!("%t{}", self.next_temp);
        self.next_temp += 1;
        temp
    }

    fn new_label(&mut self, role: &str) -> String {
        let label = format!("b{}.{}", self.next_block, role);
        self.next_block += 1;
        label
    }
}

fn collect_local_declarations(statements: &[Stmt], declarations: &mut Vec<(String, Ty)>) {
    for statement in statements {
        match statement {
            Stmt::Decl { name, ty, .. } => declarations.push((name.clone(), *ty)),
            Stmt::VarDecl { name, ty, .. } => {
                declarations.push((name.clone(), ty.expect("validated inferred type")));
            }
            Stmt::If {
                then_block,
                else_block,
                ..
            } => {
                collect_local_declarations(then_block, declarations);
                if let Some(else_block) = else_block {
                    collect_local_declarations(else_block, declarations);
                }
            }
            Stmt::While { body, .. } | Stmt::Unsafe { body, .. } => {
                collect_local_declarations(body, declarations);
            }
            _ => {}
        }
    }
}

fn emit_main_bridge(function: &Fn, out: &mut String) {
    out.push_str("define i32 @main() {\nentry:\n");
    if function.ret == Ty::Unit {
        out.push_str(&format!(
            "  call void @{}()\n  ret i32 0\n",
            mangle(function)
        ));
    } else {
        out.push_str(&format!(
            "  %result = call i32 @{}()\n  ret i32 %result\n",
            mangle(function)
        ));
    }
    out.push_str("}\n");
}

fn llvm_ty(ty: Ty) -> String {
    match ty {
        Ty::Int(integer) => format!("i{}", integer.bits()),
        Ty::Bool => "i1".into(),
        Ty::Unit => "void".into(),
        Ty::Option(ValueTy::Bool) => LLVM_OPTION_BOOL.into(),
        Ty::Record(record) => llvm_record_ty(record),
        _ => unreachable!("type without an LLVM runtime representation validated out"),
    }
}

fn integer_type_code(integer: IntTy) -> u32 {
    match integer {
        IntTy::U8 => 1,
        IntTy::U16 => 2,
        IntTy::U32 => 3,
        IntTy::U64 => 4,
        IntTy::I8 => 5,
        IntTy::I16 => 6,
        IntTy::I32 => 7,
        IntTy::I64 => 8,
        IntTy::TParam(_) => unreachable!("type parameter after monomorphization"),
    }
}

fn packed_type_info(result: IntTy, lhs: IntTy, rhs: Option<IntTy>) -> u32 {
    integer_type_code(result)
        | (integer_type_code(lhs) << 8)
        | (rhs.map(integer_type_code).unwrap_or(0) << 16)
}

fn type_code(ty: Ty) -> String {
    match ty {
        Ty::Int(IntTy::U8) => "u8".into(),
        Ty::Int(IntTy::U16) => "u16".into(),
        Ty::Int(IntTy::U32) => "u32".into(),
        Ty::Int(IntTy::U64) => "u64".into(),
        Ty::Int(IntTy::I8) => "i8".into(),
        Ty::Int(IntTy::I16) => "i16".into(),
        Ty::Int(IntTy::I32) => "i32".into(),
        Ty::Int(IntTy::I64) => "i64".into(),
        Ty::Bool => "b".into(),
        Ty::Unit => "v".into(),
        Ty::Option(ValueTy::Bool) => "ob".into(),
        Ty::Record(record) => format!("r{record}"),
        _ => unreachable!("type without an LLVM runtime representation validated out"),
    }
}

fn mangle(function: &Fn) -> String {
    let params = function
        .params
        .iter()
        .map(|parameter| type_code(parameter.ty))
        .collect::<Vec<_>>()
        .join("_");
    format!(
        "__sable_v0_f_{}_{}__p_{}__r_{}",
        function.name.len(),
        function.name,
        params,
        type_code(function.ret)
    )
}

fn collect_calls_block(statements: &[Stmt], calls: &mut Vec<(String, Span)>) {
    for statement in statements {
        match statement {
            Stmt::Decl { init, .. } => {
                if let Some(init) = init {
                    collect_calls_expr(init, calls);
                }
            }
            Stmt::Assign { value, .. }
            | Stmt::ExprStmt(value)
            | Stmt::Return {
                value: Some(value), ..
            }
            | Stmt::VarDecl { init: value, .. } => collect_calls_expr(value, calls),
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                collect_calls_expr(cond, calls);
                collect_calls_block(then_block, calls);
                if let Some(block) = else_block {
                    collect_calls_block(block, calls);
                }
            }
            Stmt::FieldAssign { value, .. } => collect_calls_expr(value, calls),
            Stmt::FieldStore { index, value, .. } | Stmt::Store { index, value, .. } => {
                collect_calls_expr(index, calls);
                collect_calls_expr(value, calls);
            }
            Stmt::While { cond, body, .. } => {
                collect_calls_expr(cond, calls);
                collect_calls_block(body, calls);
            }
            Stmt::Unsafe { body, .. } | Stmt::Expose { body, .. } => {
                collect_calls_block(body, calls)
            }
            Stmt::StaticAlloc { size, .. } | Stmt::SystemAlloc { size, .. } => {
                collect_calls_expr(size, calls)
            }
            Stmt::SystemDealloc {
                ptr, res, release, ..
            } => {
                collect_calls_expr(ptr, calls);
                collect_calls_expr(res, calls);
                collect_calls_expr(release, calls);
            }
            Stmt::Return { value: None, .. } | Stmt::Assert(_) => {}
        }
    }
}

fn collect_calls_expr(expression: &Expr, calls: &mut Vec<(String, Span)>) {
    match &expression.kind {
        ExprKind::Call {
            callee,
            callee_span,
            args,
            ..
        } => {
            calls.push((callee.clone(), *callee_span));
            for arg in args {
                collect_calls_expr(arg, calls);
            }
        }
        ExprKind::Unary { operand, .. }
        | ExprKind::Widen { arg: operand, .. }
        | ExprKind::Narrow { arg: operand, .. }
        | ExprKind::IsSome { operand }
        | ExprKind::OptValue { operand }
        | ExprKind::SomeE(operand) => collect_calls_expr(operand, calls),
        ExprKind::Binary { lhs, rhs, .. } => {
            collect_calls_expr(lhs, calls);
            collect_calls_expr(rhs, calls);
        }
        ExprKind::Index { index, .. }
        | ExprKind::SelfFieldIndex { index, .. }
        | ExprKind::ClassFieldIndex { index, .. } => collect_calls_expr(index, calls),
        ExprKind::RawOp { args, .. }
        | ExprKind::DeviceOp { args, .. }
        | ExprKind::ResOp { args, .. }
        | ExprKind::CtorCall { args, .. }
        | ExprKind::TraitCall { args, .. }
        | ExprKind::MethodCall { args, .. }
        | ExprKind::RecordLit { args, .. }
        | ExprKind::ArrayLit(args) => {
            for arg in args {
                collect_calls_expr(arg, calls);
            }
        }
        ExprKind::AllocArray { len, init, .. } => {
            collect_calls_expr(len, calls);
            collect_calls_expr(init, calls);
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

fn unsupported(span: Span, detail: impl Into<String>) -> BackendError {
    diag(
        "backend.unsupported",
        "construct is outside the current LLVM backend subset",
        span,
        detail,
    )
}

fn diag(
    name: &str,
    title: impl Into<String>,
    span: Span,
    label: impl Into<String>,
) -> BackendError {
    Diagnostic {
        name: name.into(),
        title: title.into(),
        span,
        label: label.into(),
        notes: Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{
        ExternInfo, GenericTy, Param, Program, ProofReuse, RecordField, StorageLayout, TypeArg,
        ValueTy,
    };

    fn expression(kind: ExprKind, ty: Ty) -> Expr {
        Expr {
            kind,
            span: Span::new(0, 1),
            ty: Some(ty),
        }
    }

    fn function(name: &str, ret: Ty, body: Vec<Stmt>) -> Fn {
        Fn {
            is_pub: false,
            extern_info: None,
            name: name.into(),
            name_span: Span::new(0, 1),
            type_params: Vec::new(),
            type_bounds: Vec::new(),
            requires: Vec::new(),
            proof_reuse: ProofReuse::None,
            params: Vec::<Param>::new(),
            ret,
            pres: Vec::new(),
            posts: Vec::new(),
            variant: None,
            body,
            span: Span::new(0, 1),
        }
    }

    fn parameter(name: &str, ty: Ty) -> Param {
        Param {
            name: name.into(),
            ty,
            span: Span::new(0, 1),
            consumes: false,
        }
    }

    fn call(name: &str, ty: Ty) -> Expr {
        call_with(name, ty, Vec::new())
    }

    fn call_with(name: &str, ty: Ty, args: Vec<Expr>) -> Expr {
        expression(
            ExprKind::Call {
                callee: name.into(),
                callee_span: Span::new(0, 1),
                type_args: Vec::new(),
                args,
            },
            ty,
        )
    }

    fn variable(name: &str, integer: IntTy) -> Expr {
        typed_variable(name, Ty::Int(integer))
    }

    fn typed_variable(name: &str, ty: Ty) -> Expr {
        expression(ExprKind::Var(name.into()), ty)
    }

    fn bool_option(kind: ExprKind) -> Expr {
        expression(kind, Ty::Option(ValueTy::Bool))
    }

    fn bool_option_variable(name: &str) -> Expr {
        bool_option(ExprKind::Var(name.into()))
    }

    fn binary(operator: BinOp, integer: IntTy, lhs: Expr, rhs: Expr) -> Expr {
        expression(
            ExprKind::Binary {
                op: operator,
                op_span: Span::new(0, 1),
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            },
            Ty::Int(integer),
        )
    }

    fn returning_function(name: &str, integer: IntTy, value: Expr) -> Fn {
        function(
            name,
            Ty::Int(integer),
            vec![Stmt::Return {
                value: Some(value),
                span: Span::new(0, 1),
            }],
        )
    }

    fn program(fns: Vec<Fn>) -> Program {
        Program {
            fns,
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

    fn integer_pair_record() -> RecordDecl {
        RecordDecl {
            is_pub: false,
            name: "Pair".into(),
            name_span: Span::new(0, 1),
            // Deliberately not LLVM's natural `{ i32, i64 }` layout: the
            // gap pins that raw-cell geometry and semantic values are
            // separate representations.
            layout: StorageLayout { size: 24, align: 8 },
            layout_span: Span::new(0, 1),
            fields: vec![
                RecordField {
                    name: "answer".into(),
                    ty: Ty::Int(IntTy::I32),
                    offset: 0,
                    span: Span::new(0, 1),
                    offset_span: Span::new(0, 1),
                },
                RecordField {
                    name: "marker".into(),
                    ty: Ty::Int(IntTy::U64),
                    offset: 16,
                    span: Span::new(0, 1),
                    offset_span: Span::new(0, 1),
                },
            ],
            span: Span::new(0, 1),
        }
    }

    fn pair_literal(answer: Expr, marker: Expr) -> Expr {
        expression(
            ExprKind::RecordLit {
                record: "Pair".into(),
                record_span: Span::new(0, 1),
                args: vec![answer, marker],
            },
            Ty::Record(0),
        )
    }

    fn pair_answer(name: &str) -> Expr {
        expression(
            ExprKind::RecordField {
                obj: name.into(),
                obj_span: Span::new(0, 1),
                field: "answer".into(),
            },
            Ty::Int(IntTy::I32),
        )
    }

    #[test]
    fn emits_literal_and_main_bridge_deterministically() {
        let f = function(
            "answer",
            Ty::Int(IntTy::I32),
            vec![Stmt::Return {
                value: Some(expression(ExprKind::IntLit(42), Ty::Int(IntTy::I32))),
                span: Span::new(0, 1),
            }],
        );
        let ir = emit_program(
            &program(vec![f]),
            1,
            &EmitOptions {
                entry: Some("answer".into()),
            },
        )
        .unwrap();
        assert!(ir.contains("define internal i32 @__sable_v0_f_6_answer__p___r_i32()"));
        assert!(ir.contains("ret i32 42"));
        assert!(ir.contains("define i32 @main()"));
        assert!(!ir.contains("llvm.assume"));
        assert!(!ir.contains(" nsw "));
        assert!(!ir.contains(LLVM_OPTION_BOOL));
    }

    #[test]
    fn integer_pod_record_is_nominal_and_transports_through_locals_calls_and_returns() {
        let record = Ty::Record(0);
        let i32_ty = Ty::Int(IntTy::I32);
        let u64_ty = Ty::Int(IntTy::U64);

        let mut make = function(
            "make",
            record,
            vec![Stmt::Return {
                value: Some(pair_literal(
                    typed_variable("answer", i32_ty),
                    typed_variable("marker", u64_ty),
                )),
                span: Span::new(0, 1),
            }],
        );
        make.params = vec![parameter("answer", i32_ty), parameter("marker", u64_ty)];

        let mut project = function(
            "project",
            i32_ty,
            vec![
                Stmt::Decl {
                    ty: record,
                    name: "copy".into(),
                    name_span: Span::new(0, 1),
                    init: Some(typed_variable("pair", record)),
                    mutable: false,
                },
                Stmt::Return {
                    value: Some(pair_answer("copy")),
                    span: Span::new(0, 1),
                },
            ],
        );
        project.params = vec![parameter("pair", record)];

        let forward = function(
            "forward",
            record,
            vec![
                Stmt::Decl {
                    ty: record,
                    name: "result".into(),
                    name_span: Span::new(0, 1),
                    init: Some(pair_literal(
                        expression(ExprKind::IntLit(0), i32_ty),
                        expression(ExprKind::IntLit(0), u64_ty),
                    )),
                    mutable: true,
                },
                Stmt::If {
                    cond: expression(ExprKind::BoolLit(true), Ty::Bool),
                    then_block: vec![Stmt::Assign {
                        name: "result".into(),
                        name_span: Span::new(0, 1),
                        value: call_with(
                            "make",
                            record,
                            vec![
                                expression(ExprKind::IntLit(42), i32_ty),
                                expression(ExprKind::IntLit(7), u64_ty),
                            ],
                        ),
                    }],
                    else_block: Some(vec![Stmt::Assign {
                        name: "result".into(),
                        name_span: Span::new(0, 1),
                        value: pair_literal(
                            expression(ExprKind::IntLit(1), i32_ty),
                            expression(ExprKind::IntLit(2), u64_ty),
                        ),
                    }]),
                },
                Stmt::Return {
                    value: Some(typed_variable("result", record)),
                    span: Span::new(0, 1),
                },
            ],
        );

        let consume = function(
            "consume",
            i32_ty,
            vec![
                Stmt::Decl {
                    ty: record,
                    name: "value".into(),
                    name_span: Span::new(0, 1),
                    init: Some(call("forward", record)),
                    mutable: false,
                },
                Stmt::Return {
                    value: Some(call_with(
                        "project",
                        i32_ty,
                        vec![typed_variable("value", record)],
                    )),
                    span: Span::new(0, 1),
                },
            ],
        );

        let mut checked = program(vec![make, project, forward, consume]);
        checked.records.push(integer_pair_record());
        let ir = emit_program(&checked, 1, &EmitOptions::default()).unwrap();

        assert_eq!(ir.matches("%sable.record.0 = type { i32, i64 }").count(), 1);
        assert!(ir.contains("not its raw-cell layout"));
        let named_type = ir.find("%sable.record.0 = type").unwrap();
        let first_definition = ir.find("define internal").unwrap();
        assert!(named_type < first_definition);
        assert!(
            ir.contains("define internal %sable.record.0 @__sable_v0_f_4_make__p_i32_u64__r_r0")
        );
        assert!(ir.contains(
            "define internal i32 @__sable_v0_f_7_project__p_r0__r_i32(%sable.record.0 %p0)"
        ));
        assert!(ir.contains("alloca %sable.record.0"));
        assert!(ir.contains("store %sable.record.0 %p0"));
        assert!(ir.contains("load %sable.record.0"));
        assert!(ir.contains("insertvalue %sable.record.0 zeroinitializer, i32"));
        assert!(ir.contains("insertvalue %sable.record.0"));
        assert!(ir.contains("extractvalue %sable.record.0"));
        assert!(
            ir.contains(
                "call %sable.record.0 @__sable_v0_f_4_make__p_i32_u64__r_r0(i32 42, i64 7)"
            )
        );
        assert!(ir.contains("call i32 @__sable_v0_f_7_project__p_r0__r_i32(%sable.record.0"));
        assert!(!ir.contains("getelementptr"));
        assert!(!ir.contains(" inbounds "));
    }

    #[test]
    fn pod_record_value_slice_rejects_pointer_fields_and_imported_identity() {
        let mut pointer_record = integer_pair_record();
        pointer_record.name = "Node".into();
        pointer_record.fields[0].name = "next".into();
        pointer_record.fields[0].ty = Ty::RawRecord(0);
        let mut pointer_program = program(Vec::new());
        pointer_program.records.push(pointer_record);
        let pointer_error = emit_program(&pointer_program, 1, &EmitOptions::default()).unwrap_err();
        assert_eq!(pointer_error[0].name, "backend.unsupported");
        assert!(pointer_error[0].label.contains("integer-only POD values"));

        let mut imported_record = integer_pair_record();
        imported_record.name_span = Span::new(2, 3);
        let mut imported_program = program(Vec::new());
        imported_program.records.push(imported_record);
        let imported_error =
            emit_program(&imported_program, 1, &EmitOptions::default()).unwrap_err();
        assert_eq!(imported_error[0].name, "backend.unsupported");
        assert!(imported_error[0].label.contains("cross-module record ABI"));

        let make_imported = function(
            "make_imported",
            Ty::Record(0),
            vec![Stmt::Return {
                value: Some(pair_literal(
                    expression(ExprKind::IntLit(1), Ty::Int(IntTy::I32)),
                    expression(ExprKind::IntLit(2), Ty::Int(IntTy::U64)),
                )),
                span: Span::new(0, 1),
            }],
        );
        let entry = function(
            "entry",
            Ty::Int(IntTy::I32),
            vec![
                Stmt::Decl {
                    ty: Ty::Record(0),
                    name: "imported".into(),
                    name_span: Span::new(0, 1),
                    init: Some(call("make_imported", Ty::Record(0))),
                    mutable: false,
                },
                Stmt::Return {
                    value: Some(pair_answer("imported")),
                    span: Span::new(0, 1),
                },
            ],
        );
        imported_program.fns.extend([make_imported, entry]);
        let selected_import = emit_program(
            &imported_program,
            1,
            &EmitOptions {
                entry: Some("entry".into()),
            },
        )
        .unwrap_err();
        assert_eq!(selected_import[0].name, "backend.unsupported");
        assert!(selected_import[0].label.contains("cross-module record ABI"));

        // Entry closure selection keeps an unrelated unsupported declaration
        // outside the native artifact, matching the existing function gate.
        let unrelated_entry = returning_function(
            "unrelated_entry",
            IntTy::I32,
            expression(ExprKind::IntLit(42), Ty::Int(IntTy::I32)),
        );
        let mut unrelated_program = program(vec![unrelated_entry]);
        unrelated_program.records.push({
            let mut record = integer_pair_record();
            record.name_span = Span::new(2, 3);
            record
        });
        let selected = emit_program(
            &unrelated_program,
            1,
            &EmitOptions {
                entry: Some("unrelated_entry".into()),
            },
        )
        .unwrap();
        assert!(!selected.contains("%sable.record."));

        let mut root_program = program(vec![function(
            "record_entry",
            Ty::Record(0),
            vec![Stmt::Return {
                value: Some(pair_literal(
                    expression(ExprKind::IntLit(1), Ty::Int(IntTy::I32)),
                    expression(ExprKind::IntLit(2), Ty::Int(IntTy::U64)),
                )),
                span: Span::new(0, 1),
            }],
        )]);
        root_program.records.push(integer_pair_record());
        let entry_record_error = emit_program(
            &root_program,
            1,
            &EmitOptions {
                entry: Some("record_entry".into()),
            },
        )
        .unwrap_err();
        assert_eq!(entry_record_error[0].name, "backend.entry_signature");
    }

    #[test]
    fn boolean_option_is_canonical_and_transports_across_cfg_calls_and_locals() {
        let option = Ty::Option(ValueTy::Bool);
        let make_false = function(
            "make_false",
            option,
            vec![Stmt::Return {
                value: Some(bool_option(ExprKind::SomeE(Box::new(expression(
                    ExprKind::BoolLit(false),
                    Ty::Bool,
                ))))),
                span: Span::new(0, 1),
            }],
        );
        let forward = function(
            "forward",
            option,
            vec![
                Stmt::Decl {
                    ty: option,
                    name: "result".into(),
                    name_span: Span::new(0, 1),
                    init: Some(bool_option(ExprKind::NoneE)),
                    mutable: true,
                },
                Stmt::If {
                    cond: expression(ExprKind::BoolLit(true), Ty::Bool),
                    then_block: vec![Stmt::Assign {
                        name: "result".into(),
                        name_span: Span::new(0, 1),
                        value: call("make_false", option),
                    }],
                    else_block: Some(vec![Stmt::Assign {
                        name: "result".into(),
                        name_span: Span::new(0, 1),
                        value: bool_option(ExprKind::SomeE(Box::new(expression(
                            ExprKind::BoolLit(true),
                            Ty::Bool,
                        )))),
                    }]),
                },
                Stmt::Return {
                    value: Some(bool_option_variable("result")),
                    span: Span::new(0, 1),
                },
            ],
        );
        let consume = function(
            "consume",
            Ty::Bool,
            vec![
                Stmt::VarDecl {
                    name: "value".into(),
                    name_span: Span::new(0, 1),
                    init: call("forward", option),
                    mutable: false,
                    ty: Some(option),
                },
                Stmt::If {
                    cond: expression(
                        ExprKind::IsSome {
                            operand: Box::new(bool_option_variable("value")),
                        },
                        Ty::Bool,
                    ),
                    then_block: vec![Stmt::Return {
                        value: Some(expression(
                            ExprKind::OptValue {
                                operand: Box::new(bool_option_variable("value")),
                            },
                            Ty::Bool,
                        )),
                        span: Span::new(0, 1),
                    }],
                    else_block: None,
                },
                Stmt::Return {
                    value: Some(expression(ExprKind::BoolLit(false), Ty::Bool)),
                    span: Span::new(0, 1),
                },
            ],
        );

        let ir = emit_program(
            &program(vec![make_false, forward, consume]),
            1,
            &EmitOptions::default(),
        )
        .unwrap();

        assert_eq!(
            ir.matches("%sable.option.bool = type { i8, i8 }").count(),
            1
        );
        let named_type = ir.find("%sable.option.bool = type").unwrap();
        let first_definition = ir.find("define internal").unwrap();
        assert!(named_type < first_definition);
        assert!(ir.contains(
            "define internal %sable.option.bool @__sable_v0_f_10_make_false__p___r_ob()"
        ));
        assert!(ir.contains("alloca %sable.option.bool"));
        assert!(ir.contains("store %sable.option.bool zeroinitializer"));
        assert!(ir.contains("call %sable.option.bool @__sable_v0_f_10_make_false__p___r_ob()"));
        assert!(ir.contains("load %sable.option.bool"));
        assert!(ir.contains("ret %sable.option.bool"));
        assert!(ir.contains("zext i1 0 to i8"));
        assert!(ir.contains("insertvalue %sable.option.bool zeroinitializer, i8 1, 0"));
        assert!(ir.contains("insertvalue %sable.option.bool"));
        assert!(ir.contains("extractvalue %sable.option.bool"));
        assert!(ir.contains("icmp ne i8"));

        let consume = ir
            .find("define internal i1 @__sable_v0_f_7_consume__p___r_b()")
            .map(|start| &ir[start..])
            .expect("Boolean-option consumer is emitted");
        let absent = consume.find("icmp eq i8").unwrap();
        let branch = consume[absent..].find("br i1").unwrap() + absent;
        let trap = consume
            .find("@__sable_rt_fail_v1(i32 8, i32 0, i64 0, i64 0)")
            .unwrap();
        let continuation = consume.find("trap.ok:").unwrap();
        let payload = consume[continuation..]
            .find("extractvalue %sable.option.bool")
            .unwrap()
            + continuation;
        let canonical_bool = consume[payload..].find("trunc i8").unwrap() + payload;
        assert!(absent < branch && branch < trap && trap < continuation);
        assert!(continuation < payload && payload < canonical_bool);
        for forbidden in [" nsw ", " nuw ", " exact ", " inbounds ", "llvm.assume"] {
            assert!(
                !ir.contains(forbidden),
                "forbidden LLVM promise: {forbidden}"
            );
        }
    }

    #[test]
    fn boolean_option_does_not_open_parameters_entries_or_other_payloads() {
        let option = Ty::Option(ValueTy::Bool);
        let mut parameterized = function(
            "parameterized",
            Ty::Bool,
            vec![Stmt::Return {
                value: Some(expression(ExprKind::BoolLit(false), Ty::Bool)),
                span: Span::new(0, 1),
            }],
        );
        parameterized.params = vec![parameter("value", option)];
        let parameter_error =
            emit_program(&program(vec![parameterized]), 1, &EmitOptions::default()).unwrap_err();
        assert_eq!(parameter_error[0].name, "backend.unsupported");
        assert!(parameter_error[0].label.contains("function parameter"));

        for unsupported_return in [
            Ty::Option(ValueTy::Int(IntTy::I32)),
            Ty::Option(ValueTy::Record(0)),
            Ty::Option(ValueTy::Param(crate::ast::TypeParamId::from_legacy(0))),
            Ty::OptionRaw(0),
        ] {
            let error = emit_program(
                &program(vec![function(
                    "unsupported",
                    unsupported_return,
                    Vec::new(),
                )]),
                1,
                &EmitOptions::default(),
            )
            .unwrap_err();
            assert_eq!(error[0].name, "backend.unsupported");
            assert!(error[0].label.contains("runtime representation"));
        }

        let forged_record = emit_program(
            &program(vec![function("unsupported", Ty::Record(0), Vec::new())]),
            1,
            &EmitOptions::default(),
        )
        .unwrap_err();
        assert_eq!(forged_record[0].name, "backend.unsupported");
        assert!(
            forged_record[0]
                .label
                .contains("outside the checked program")
        );

        let option_entry = function(
            "option_entry",
            option,
            vec![Stmt::Return {
                value: Some(bool_option(ExprKind::NoneE)),
                span: Span::new(0, 1),
            }],
        );
        let entry_error = emit_program(
            &program(vec![option_entry]),
            1,
            &EmitOptions {
                entry: Some("option_entry".into()),
            },
        )
        .unwrap_err();
        assert_eq!(entry_error[0].name, "backend.entry_signature");

        let mut audited = function("foreign_option", option, Vec::new());
        audited.extern_info = Some(ExternInfo {
            abi: "C".into(),
            audit_id: "test".into(),
            reason: "unit test".into(),
            span: Span::new(0, 1),
        });
        let extern_error =
            emit_program(&program(vec![audited]), 1, &EmitOptions::default()).unwrap_err();
        assert_eq!(extern_error[0].name, "backend.unsupported");
        assert!(extern_error[0].label.contains("audited extern"));
    }

    #[test]
    fn residual_recursive_generic_shapes_remain_fail_closed() {
        let callee = function(
            "callee",
            Ty::Bool,
            vec![Stmt::Return {
                value: Some(expression(ExprKind::BoolLit(true), Ty::Bool)),
                span: Span::new(0, 1),
            }],
        );
        let residual_call = expression(
            ExprKind::Call {
                callee: "callee".into(),
                callee_span: Span::new(0, 1),
                type_args: vec![TypeArg {
                    ty: GenericTy::Option(Box::new(GenericTy::Option(Box::new(GenericTy::Bool)))),
                    span: Span::new(0, 1),
                }],
                args: Vec::new(),
            },
            Ty::Bool,
        );
        let caller = function(
            "caller",
            Ty::Bool,
            vec![Stmt::Return {
                value: Some(residual_call),
                span: Span::new(0, 1),
            }],
        );
        let error =
            emit_program(&program(vec![callee, caller]), 1, &EmitOptions::default()).unwrap_err();
        assert_eq!(error[0].name, "backend.unsupported");
        assert!(error[0].label.contains("retains type arguments"));

        let mut residual_function = function(
            "generic",
            Ty::Bool,
            vec![Stmt::Return {
                value: Some(expression(ExprKind::BoolLit(true), Ty::Bool)),
                span: Span::new(0, 1),
            }],
        );
        residual_function.type_params.push("T".into());
        residual_function.type_bounds.push(None);
        let error = emit_program(
            &program(vec![residual_function]),
            1,
            &EmitOptions::default(),
        )
        .unwrap_err();
        assert_eq!(error[0].name, "backend.unsupported");
        assert!(error[0].label.contains("generic declaration metadata"));
    }

    #[test]
    fn checked_arithmetic_uses_deduplicated_intrinsics_and_guarded_traps() {
        let int = Ty::Int(IntTy::I32);
        let first_binary = expression(
            ExprKind::Binary {
                op: BinOp::Add,
                op_span: Span::new(0, 1),
                lhs: Box::new(expression(ExprKind::IntLit(1), int)),
                rhs: Box::new(expression(ExprKind::IntLit(2), int)),
            },
            int,
        );
        let f = function(
            "add",
            int,
            vec![Stmt::Return {
                value: Some(first_binary),
                span: Span::new(0, 1),
            }],
        );
        let second_binary = expression(
            ExprKind::Binary {
                op: BinOp::Add,
                op_span: Span::new(0, 1),
                lhs: Box::new(expression(ExprKind::IntLit(3), int)),
                rhs: Box::new(expression(ExprKind::IntLit(4), int)),
            },
            int,
        );
        let g = function(
            "add_again",
            int,
            vec![Stmt::Return {
                value: Some(second_binary),
                span: Span::new(0, 1),
            }],
        );
        let ir = emit_program(&program(vec![f, g]), 1, &EmitOptions::default()).unwrap();
        assert_eq!(
            ir.matches("declare { i32, i1 } @llvm.sadd.with.overflow.i32")
                .count(),
            1
        );
        let call = ir
            .find("call { i32, i1 } @llvm.sadd.with.overflow.i32")
            .unwrap();
        let guard = ir[call..].find("br i1").unwrap() + call;
        let continuation = ir[guard..].find("trap.ok:").unwrap() + guard;
        let ret = ir[continuation..].find("ret i32").unwrap() + continuation;
        assert!(call < guard && guard < continuation && continuation < ret);
        assert!(ir.contains("call void @__sable_rt_fail_v1(i32 1, i32 460551"));
        assert!(ir.contains("define weak void @__sable_rt_trap_v1"));
        assert!(ir.contains("call void @llvm.trap()\nunreachable"));
    }

    #[test]
    fn whole_module_does_not_silently_omit_generic_declarations() {
        let mut program = program(Vec::new());
        program.fn_templates.push(function(
            "identity",
            Ty::Int(IntTy::I32),
            vec![Stmt::Return {
                value: Some(expression(ExprKind::IntLit(0), Ty::Int(IntTy::I32))),
                span: Span::new(0, 1),
            }],
        ));
        let error = emit_program(&program, 1, &EmitOptions::default()).unwrap_err();
        assert_eq!(error[0].name, "backend.unsupported");
        assert!(error[0].label.contains("generic function template"));
    }

    #[test]
    fn entry_selection_ignores_only_unreachable_unsupported_functions() {
        let entry = returning_function(
            "entry",
            IntTy::I32,
            expression(ExprKind::IntLit(42), Ty::Int(IntTy::I32)),
        );
        let mut unrelated = function(
            "unrelated",
            Ty::Unit,
            vec![Stmt::Return {
                value: None,
                span: Span::new(0, 1),
            }],
        );
        unrelated.params = vec![parameter(
            "values",
            Ty::Array(ValueTy::Int(IntTy::I32), crate::ast::Mutability::Shared),
        )];
        let program = program(vec![entry, unrelated]);

        let selected = emit_program(
            &program,
            1,
            &EmitOptions {
                entry: Some("entry".into()),
            },
        )
        .expect("an unreachable unsupported function is outside the selected executable");
        assert!(selected.contains("define i32 @main()"));
        assert!(!selected.contains("unrelated"));

        let whole_module = emit_program(&program, 1, &EmitOptions::default()).unwrap_err();
        assert_eq!(whole_module[0].name, "backend.unsupported");
    }

    #[test]
    fn syntactically_unreachable_short_circuit_callee_is_still_selected() {
        let unsupported = function(
            "unsupported_rhs",
            Ty::Bool,
            vec![
                Stmt::Decl {
                    ty: Ty::Array(ValueTy::Int(IntTy::I32), crate::ast::Mutability::Owned),
                    name: "values".into(),
                    name_span: Span::new(0, 1),
                    init: None,
                    mutable: true,
                },
                Stmt::Return {
                    value: Some(expression(ExprKind::BoolLit(true), Ty::Bool)),
                    span: Span::new(0, 1),
                },
            ],
        );
        let condition = expression(
            ExprKind::Binary {
                op: BinOp::And,
                op_span: Span::new(0, 1),
                lhs: Box::new(expression(ExprKind::BoolLit(false), Ty::Bool)),
                rhs: Box::new(call("unsupported_rhs", Ty::Bool)),
            },
            Ty::Bool,
        );
        let entry = function(
            "entry",
            Ty::Int(IntTy::I32),
            vec![
                Stmt::If {
                    cond: condition,
                    then_block: vec![Stmt::Return {
                        value: Some(expression(ExprKind::IntLit(0), Ty::Int(IntTy::I32))),
                        span: Span::new(0, 1),
                    }],
                    else_block: None,
                },
                Stmt::Return {
                    value: Some(expression(ExprKind::IntLit(42), Ty::Int(IntTy::I32))),
                    span: Span::new(0, 1),
                },
            ],
        );

        let error = emit_program(
            &program(vec![entry, unsupported]),
            1,
            &EmitOptions {
                entry: Some("entry".into()),
            },
        )
        .unwrap_err();
        assert_eq!(error[0].name, "backend.unsupported");
        assert!(error[0].label.contains("local variable"));
    }

    #[test]
    fn recursion_is_rejected_only_when_it_enters_the_selected_closure() {
        let entry = returning_function(
            "entry",
            IntTy::I32,
            expression(ExprKind::IntLit(42), Ty::Int(IntTy::I32)),
        );
        let recursive = function(
            "recursive",
            Ty::Int(IntTy::I32),
            vec![Stmt::Return {
                value: Some(call("recursive", Ty::Int(IntTy::I32))),
                span: Span::new(0, 1),
            }],
        );
        let unrelated_program = program(vec![entry, recursive.clone()]);

        emit_program(
            &unrelated_program,
            1,
            &EmitOptions {
                entry: Some("entry".into()),
            },
        )
        .expect("unrelated recursion is outside the selected executable");
        let whole_error = emit_program(&unrelated_program, 1, &EmitOptions::default()).unwrap_err();
        assert_eq!(whole_error[0].name, "backend.recursion_unsupported");

        let reachable_entry = function(
            "reachable_entry",
            Ty::Int(IntTy::I32),
            vec![Stmt::Return {
                value: Some(call("recursive", Ty::Int(IntTy::I32))),
                span: Span::new(0, 1),
            }],
        );
        let reachable = program(vec![reachable_entry, recursive]);
        let reachable_error = emit_program(
            &reachable,
            1,
            &EmitOptions {
                entry: Some("reachable_entry".into()),
            },
        )
        .unwrap_err();
        assert_eq!(reachable_error[0].name, "backend.recursion_unsupported");
    }

    #[test]
    fn comparisons_use_the_checked_integer_signedness() {
        let mut signed = function(
            "signed_less",
            Ty::Bool,
            vec![Stmt::Return {
                value: Some(expression(
                    ExprKind::Binary {
                        op: BinOp::Lt,
                        op_span: Span::new(0, 1),
                        lhs: Box::new(expression(ExprKind::Var("x".into()), Ty::Int(IntTy::I32))),
                        rhs: Box::new(expression(ExprKind::Var("y".into()), Ty::Int(IntTy::I32))),
                    },
                    Ty::Bool,
                )),
                span: Span::new(0, 1),
            }],
        );
        signed.params = vec![
            parameter("x", Ty::Int(IntTy::I32)),
            parameter("y", Ty::Int(IntTy::I32)),
        ];

        let mut unsigned = function(
            "unsigned_less",
            Ty::Bool,
            vec![Stmt::Return {
                value: Some(expression(
                    ExprKind::Binary {
                        op: BinOp::Lt,
                        op_span: Span::new(0, 1),
                        lhs: Box::new(expression(ExprKind::Var("x".into()), Ty::Int(IntTy::U8))),
                        rhs: Box::new(expression(ExprKind::Var("y".into()), Ty::Int(IntTy::U8))),
                    },
                    Ty::Bool,
                )),
                span: Span::new(0, 1),
            }],
        );
        unsigned.params = vec![
            parameter("x", Ty::Int(IntTy::U8)),
            parameter("y", Ty::Int(IntTy::U8)),
        ];

        let ir =
            emit_program(&program(vec![signed, unsigned]), 1, &EmitOptions::default()).unwrap();
        assert!(ir.contains("icmp slt i32"));
        assert!(ir.contains("icmp ult i8"));
    }

    #[test]
    fn if_with_one_returning_branch_keeps_its_merge_live() {
        let int = Ty::Int(IntTy::I32);
        let mut choose = function(
            "choose",
            int,
            vec![
                Stmt::If {
                    cond: expression(ExprKind::Var("flag".into()), Ty::Bool),
                    then_block: vec![Stmt::Return {
                        value: Some(expression(ExprKind::IntLit(1), int)),
                        span: Span::new(0, 1),
                    }],
                    else_block: None,
                },
                Stmt::Return {
                    value: Some(expression(ExprKind::IntLit(2), int)),
                    span: Span::new(0, 1),
                },
            ],
        );
        choose.params = vec![parameter("flag", Ty::Bool)];

        let ir = emit_program(&program(vec![choose]), 1, &EmitOptions::default()).unwrap();
        assert!(ir.contains("label %b0.if.then, label %b1.if.end"));
        assert!(ir.contains("b0.if.then:\n  ret i32 1"));
        assert!(ir.contains("b1.if.end:\n  ret i32 2"));
    }

    #[test]
    fn short_circuit_phi_uses_the_actual_operand_predecessors() {
        let left = function(
            "left",
            Ty::Bool,
            vec![Stmt::Return {
                value: Some(expression(ExprKind::BoolLit(true), Ty::Bool)),
                span: Span::new(0, 1),
            }],
        );
        let right = function(
            "right",
            Ty::Bool,
            vec![Stmt::Return {
                value: Some(expression(ExprKind::BoolLit(false), Ty::Bool)),
                span: Span::new(0, 1),
            }],
        );
        let both = function(
            "both",
            Ty::Bool,
            vec![Stmt::Return {
                value: Some(expression(
                    ExprKind::Binary {
                        op: BinOp::And,
                        op_span: Span::new(0, 1),
                        lhs: Box::new(call("left", Ty::Bool)),
                        rhs: Box::new(call("right", Ty::Bool)),
                    },
                    Ty::Bool,
                )),
                span: Span::new(0, 1),
            }],
        );

        let ir = emit_program(
            &program(vec![left, right, both]),
            1,
            &EmitOptions::default(),
        )
        .unwrap();
        assert!(ir.contains("br i1 %t0, label %b0.sc.rhs, label %b1.sc.end"));
        assert!(ir.contains("b0.sc.rhs:\n  %t1 = call i1"));
        assert!(ir.contains("phi i1 [ 0, %entry ], [ %t1, %b0.sc.rhs ]"));
    }

    #[test]
    fn while_rechecks_its_condition_and_accepts_a_returning_body() {
        let int = Ty::Int(IntTy::I32);
        let mut loop_once = function(
            "loop_once",
            int,
            vec![
                Stmt::While {
                    cond: expression(ExprKind::Var("keep_going".into()), Ty::Bool),
                    invariants: Vec::new(),
                    variant: None,
                    kw_span: Span::new(0, 1),
                    body: vec![Stmt::Return {
                        value: Some(expression(ExprKind::IntLit(7), int)),
                        span: Span::new(0, 1),
                    }],
                },
                Stmt::Return {
                    value: Some(expression(ExprKind::IntLit(9), int)),
                    span: Span::new(0, 1),
                },
            ],
        );
        loop_once.params = vec![parameter("keep_going", Ty::Bool)];

        let ir = emit_program(&program(vec![loop_once]), 1, &EmitOptions::default()).unwrap();
        assert!(ir.contains("br label %b0.while.head\nb0.while.head:\n  %t0 = load i1"));
        assert!(ir.contains("b1.while.body:\n  ret i32 7"));
        assert!(ir.contains("b2.while.end:\n  ret i32 9"));
    }

    #[test]
    fn returning_a_unit_call_preserves_the_call_then_returns_void() {
        let sink = function(
            "sink",
            Ty::Unit,
            vec![Stmt::Return {
                value: None,
                span: Span::new(0, 1),
            }],
        );
        let wrapper = function(
            "wrapper",
            Ty::Unit,
            vec![Stmt::Return {
                value: Some(call("sink", Ty::Unit)),
                span: Span::new(0, 1),
            }],
        );

        let ir = emit_program(&program(vec![sink, wrapper]), 1, &EmitOptions::default()).unwrap();
        assert!(ir.contains("call void @__sable_v0_f_4_sink__p___r_v()\n  ret void"));
    }

    #[test]
    fn uninitialized_declaration_has_no_speculative_zero_store() {
        let local = function(
            "local",
            Ty::Unit,
            vec![
                Stmt::Decl {
                    ty: Ty::Int(IntTy::I32),
                    name: "x".into(),
                    name_span: Span::new(0, 1),
                    init: None,
                    mutable: true,
                },
                Stmt::Return {
                    value: None,
                    span: Span::new(0, 1),
                },
            ],
        );

        let ir = emit_program(&program(vec![local]), 1, &EmitOptions::default()).unwrap();
        assert!(ir.contains("%v0 = alloca i32"));
        assert!(!ir.contains("store i32 0, ptr %v0"));
    }

    #[test]
    fn checked_negation_and_unsigned_arithmetic_choose_matching_intrinsics() {
        let mut negate = returning_function(
            "negate",
            IntTy::I8,
            expression(
                ExprKind::Unary {
                    op: UnOp::Neg,
                    operand: Box::new(variable("x", IntTy::I8)),
                },
                Ty::Int(IntTy::I8),
            ),
        );
        negate.params = vec![parameter("x", Ty::Int(IntTy::I8))];
        let mut multiply = returning_function(
            "multiply",
            IntTy::U16,
            binary(
                BinOp::Mul,
                IntTy::U16,
                variable("x", IntTy::U16),
                variable("y", IntTy::U16),
            ),
        );
        multiply.params = vec![
            parameter("x", Ty::Int(IntTy::U16)),
            parameter("y", Ty::Int(IntTy::U16)),
        ];

        let ir =
            emit_program(&program(vec![negate, multiply]), 1, &EmitOptions::default()).unwrap();
        assert!(ir.contains("@llvm.ssub.with.overflow.i8(i8 0, i8"));
        assert!(ir.contains("@llvm.umul.with.overflow.i16"));
        assert!(ir.contains("@__sable_rt_fail_v1(i32 4"));
        assert!(ir.contains("@__sable_rt_fail_v1(i32 3"));
    }

    #[test]
    fn signed_division_guards_llvm_ub_and_corrects_euclidean_result() {
        let mut divide = returning_function(
            "divide",
            IntTy::I32,
            binary(
                BinOp::Div,
                IntTy::I32,
                variable("x", IntTy::I32),
                variable("y", IntTy::I32),
            ),
        );
        divide.params = vec![
            parameter("x", Ty::Int(IntTy::I32)),
            parameter("y", Ty::Int(IntTy::I32)),
        ];
        let ir = emit_program(&program(vec![divide]), 1, &EmitOptions::default()).unwrap();

        let zero_check = ir.find("icmp eq i32 %t1, 0").unwrap();
        let zero_guard = ir[zero_check..].find("br i1").unwrap() + zero_check;
        let overflow_check = ir.find("icmp eq i32 %t0, -2147483648").unwrap();
        let overflow_guard = ir[overflow_check..].find("br i1").unwrap() + overflow_check;
        let divide = ir.find(" = sdiv i32").unwrap();
        assert!(zero_check < zero_guard && zero_guard < overflow_check);
        assert!(overflow_check < overflow_guard && overflow_guard < divide);
        assert!(ir[divide..].contains(" = srem i32"));
        assert!(ir[divide..].contains("icmp slt i32"));
        let correction = &ir[divide..];
        assert!(correction.contains(" = add i32"));
        assert!(correction.contains(" = sub i32"));
        assert!(correction.contains("select i1"));
    }

    #[test]
    fn signed_remainder_routes_min_negative_one_around_srem() {
        let mut remainder = returning_function(
            "remainder",
            IntTy::I64,
            binary(
                BinOp::Rem,
                IntTy::I64,
                variable("x", IntTy::I64),
                variable("y", IntTy::I64),
            ),
        );
        remainder.params = vec![
            parameter("x", Ty::Int(IntTy::I64)),
            parameter("y", Ty::Int(IntTy::I64)),
        ];
        let ir = emit_program(&program(vec![remainder]), 1, &EmitOptions::default()).unwrap();

        let split = ir.find("label %b2.rem.min-neg-one").unwrap();
        let normal = ir.find("b3.rem.normal:\n  %t").unwrap();
        let srem = ir.find(" = srem i64").unwrap();
        let special = ir.find("b2.rem.min-neg-one:\n").unwrap();
        let merge = ir.find("b4.rem.merge:\n").unwrap();
        assert!(split < normal && normal < srem && srem < special && special < merge);
        let phi = &ir[merge..];
        assert!(phi.contains("phi i64"));
        assert!(phi.contains("[ 0, %b2.rem.min-neg-one ]"));
        assert!(phi.contains(" = add i64"));
        assert!(phi.contains(" = sub i64"));
        assert!(phi.contains("select i1"));
    }

    #[test]
    fn conversions_preserve_signedness_and_guard_narrowing_in_i128() {
        let mut widen_signed = returning_function(
            "widen_signed",
            IntTy::I64,
            expression(
                ExprKind::Widen {
                    target: IntTy::I64,
                    arg: Box::new(variable("x", IntTy::I16)),
                },
                Ty::Int(IntTy::I64),
            ),
        );
        widen_signed.params = vec![parameter("x", Ty::Int(IntTy::I16))];
        let mut widen_unsigned = returning_function(
            "widen_unsigned",
            IntTy::U32,
            expression(
                ExprKind::Widen {
                    target: IntTy::U32,
                    arg: Box::new(variable("x", IntTy::U8)),
                },
                Ty::Int(IntTy::U32),
            ),
        );
        widen_unsigned.params = vec![parameter("x", Ty::Int(IntTy::U8))];
        let mut narrow = returning_function(
            "narrow",
            IntTy::I8,
            expression(
                ExprKind::Narrow {
                    target: IntTy::I8,
                    arg: Box::new(variable("x", IntTy::U64)),
                },
                Ty::Int(IntTy::I8),
            ),
        );
        narrow.params = vec![parameter("x", Ty::Int(IntTy::U64))];
        let mut narrow_signed = returning_function(
            "narrow_signed",
            IntTy::U8,
            expression(
                ExprKind::Narrow {
                    target: IntTy::U8,
                    arg: Box::new(variable("x", IntTy::I8)),
                },
                Ty::Int(IntTy::U8),
            ),
        );
        narrow_signed.params = vec![parameter("x", Ty::Int(IntTy::I8))];
        let ir = emit_program(
            &program(vec![widen_signed, widen_unsigned, narrow, narrow_signed]),
            1,
            &EmitOptions::default(),
        )
        .unwrap();

        assert!(ir.contains("sext i16"));
        assert!(ir.contains("zext i8"));
        assert!(ir.contains("zext i64 %t0 to i128"));
        assert!(ir.contains("icmp slt i128"));
        assert!(ir.contains("icmp sgt i128"));
        let guard = ir.find("br i1").unwrap();
        let trunc = ir.find("trunc i128").unwrap();
        assert!(guard < trunc);
        // destination i8=5, source u64=4, no rhs: 5 | (4 << 8)
        assert!(ir.contains("@__sable_rt_fail_v1(i32 7, i32 1029"));
        // The signed interpretation lives in type_info; the payload is the
        // lossless original source-width bit pattern (an i64 needs no cast).
        assert!(ir.contains("i32 1029, i64 %t0, i64 0)"));
        // destination u8=1, source i8=5, no rhs: 1 | (5 << 8). Signed
        // sub-64-bit payloads are deliberately zero-extended raw bits.
        assert!(ir.contains("= zext i8 %t0 to i64"));
        assert!(ir.contains("i32 1281"));
    }

    #[test]
    fn arithmetic_ir_never_uses_poison_promises() {
        let mut add = returning_function(
            "add",
            IntTy::I32,
            binary(
                BinOp::Add,
                IntTy::I32,
                variable("x", IntTy::I32),
                variable("y", IntTy::I32),
            ),
        );
        add.params = vec![
            parameter("x", Ty::Int(IntTy::I32)),
            parameter("y", Ty::Int(IntTy::I32)),
        ];
        let ir = emit_program(&program(vec![add]), 1, &EmitOptions::default()).unwrap();
        for forbidden in [" nsw ", " nuw ", " exact ", " inbounds ", "llvm.assume"] {
            assert!(
                !ir.contains(forbidden),
                "forbidden LLVM promise: {forbidden}"
            );
        }
    }
}
