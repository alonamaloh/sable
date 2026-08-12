//! Strict textual LLVM IR lowering for the verified scalar core (ADR 0058).
//!
//! This first slice handles scalar storage, calls, comparisons, and structured
//! control flow.  A construct is either lowered with its Sable meaning or
//! rejected with a source diagnostic; there is no silent fallback and no
//! unchecked arithmetic.

use crate::VerifiedProgram;
use crate::ast::{BinOp, Expr, ExprKind, Fn, IntTy, Program, Stmt, Ty, UnOp};
use crate::diag::Diagnostic;
use crate::span::Span;
use std::collections::{HashMap, HashSet};

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
        validate_function(program, &program.fns[index])?;
    }

    let selected_set: HashSet<usize> = selected.iter().copied().collect();
    let mut out = String::from(
        "; Sable textual LLVM IR v0\n; Generated from a Lean-verified program (ADR 0058).\n\n",
    );
    for (index, function) in program.fns.iter().enumerate() {
        if selected_set.contains(&index) {
            FunctionEmitter::new(program, function).emit(&mut out)?;
            out.push('\n');
        }
    }

    if let Some(entry) = &options.entry {
        let function = program
            .fns
            .iter()
            .find(|function| function.name == *entry)
            .expect("entry selection validated above");
        emit_main_bridge(function, &mut out);
    }
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
        validate_whole_program_surface(program)?;
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

fn validate_whole_program_surface(program: &Program) -> Result<(), Vec<BackendError>> {
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
    if let Some(record) = program.records.first() {
        return Err(vec![unsupported(
            record.name_span,
            format!("record `{}` is outside the scalar LLVM subset", record.name),
        )]);
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

fn validate_function(program: &Program, function: &Fn) -> Result<(), Vec<BackendError>> {
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
        require_value_scalar(parameter.ty, parameter.span, "function parameter")?;
    }
    require_scalar(function.ret, function.name_span, "function return type")?;
    validate_block(program, &function.body)
}

fn validate_block(program: &Program, statements: &[Stmt]) -> Result<(), Vec<BackendError>> {
    for statement in statements {
        match statement {
            Stmt::Decl {
                ty,
                name_span,
                init,
                ..
            } => {
                require_value_scalar(*ty, *name_span, "local variable")?;
                if let Some(value) = init {
                    validate_expr(program, value)?;
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
                require_value_scalar(ty, *name_span, "inferred local")?;
                validate_expr(program, init)?;
            }
            Stmt::Assign { value, .. }
            | Stmt::ExprStmt(value)
            | Stmt::Return {
                value: Some(value), ..
            } => validate_expr(program, value)?,
            Stmt::Return { value: None, .. } | Stmt::Assert(_) => {}
            Stmt::Unsafe { body, .. } => validate_block(program, body)?,
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                validate_bool_expr(program, cond, "`if` condition")?;
                validate_block(program, then_block)?;
                if let Some(else_block) = else_block {
                    validate_block(program, else_block)?;
                }
            }
            Stmt::While { cond, body, .. } => {
                validate_bool_expr(program, cond, "`while` condition")?;
                validate_block(program, body)?;
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

fn validate_expr(program: &Program, expression: &Expr) -> Result<(), Vec<BackendError>> {
    match &expression.kind {
        ExprKind::IntLit(_) | ExprKind::BoolLit(_) | ExprKind::Var(_) => {
            let ty = expression.ty.ok_or_else(|| {
                vec![unsupported(
                    expression.span,
                    "expression is missing its checked type",
                )]
            })?;
            require_scalar(ty, expression.span, "expression")
        }
        ExprKind::Call { callee, args, .. } => {
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
            for argument in args {
                validate_expr(program, argument)?;
            }
            require_scalar(function.ret, expression.span, "call result")
        }
        ExprKind::Unary {
            op: UnOp::Not,
            operand,
        } => validate_bool_expr(program, operand, "logical-not operand"),
        ExprKind::Binary {
            op: BinOp::And | BinOp::Or,
            lhs,
            rhs,
            ..
        } => {
            validate_bool_expr(program, lhs, "short-circuit left operand")?;
            validate_bool_expr(program, rhs, "short-circuit right operand")?;
            require_expr_type(expression, Ty::Bool, "short-circuit result")
        }
        ExprKind::Binary {
            op: op @ (BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq | BinOp::Ne),
            lhs,
            rhs,
            ..
        } => {
            validate_expr(program, lhs)?;
            validate_expr(program, rhs)?;
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
        ExprKind::Unary { .. }
        | ExprKind::Binary {
            op: BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem,
            ..
        } => Err(vec![unsupported(
            expression.span,
            "checked arithmetic awaits the guarded-arithmetic LLVM slice",
        )]),
        _ => Err(vec![unsupported(
            expression.span,
            "expression is outside the straight-line scalar LLVM subset",
        )]),
    }
}

fn validate_bool_expr(
    program: &Program,
    expression: &Expr,
    role: &str,
) -> Result<(), Vec<BackendError>> {
    validate_expr(program, expression)?;
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

fn require_scalar(ty: Ty, span: Span, role: &str) -> Result<(), Vec<BackendError>> {
    if matches!(ty, Ty::Int(_) | Ty::Bool | Ty::Unit) {
        Ok(())
    } else {
        Err(vec![unsupported(
            span,
            format!("{role} type `{}` is not scalar", ty.name()),
        )])
    }
}

fn require_value_scalar(ty: Ty, span: Span, role: &str) -> Result<(), Vec<BackendError>> {
    if matches!(ty, Ty::Int(_) | Ty::Bool) {
        Ok(())
    } else {
        Err(vec![unsupported(
            span,
            format!(
                "{role} type `{}` has no first-slice LLVM value representation",
                ty.name()
            ),
        )])
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

struct FunctionEmitter<'a> {
    program: &'a Program,
    function: &'a Fn,
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

impl<'a> FunctionEmitter<'a> {
    fn new(program: &'a Program, function: &'a Fn) -> Self {
        Self {
            program,
            function,
            locals: HashMap::new(),
            next_local: 0,
            next_temp: 0,
            next_block: 0,
            lines: Vec::new(),
            current_block: Some("entry".into()),
        }
    }

    fn emit(mut self, out: &mut String) -> Result<(), Vec<BackendError>> {
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
            _ => unreachable!("validated before lowering"),
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
        _ => unreachable!("non-scalar type validated out"),
    }
}

fn type_code(ty: Ty) -> &'static str {
    match ty {
        Ty::Int(IntTy::U8) => "u8",
        Ty::Int(IntTy::U16) => "u16",
        Ty::Int(IntTy::U32) => "u32",
        Ty::Int(IntTy::U64) => "u64",
        Ty::Int(IntTy::I8) => "i8",
        Ty::Int(IntTy::I16) => "i16",
        Ty::Int(IntTy::I32) => "i32",
        Ty::Int(IntTy::I64) => "i64",
        Ty::Bool => "b",
        Ty::Unit => "v",
        _ => unreachable!("non-scalar type validated out"),
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
    use crate::ast::{Param, Program};

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
            from_template: None,
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
        expression(
            ExprKind::Call {
                callee: name.into(),
                callee_span: Span::new(0, 1),
                type_args: Vec::new(),
                args: Vec::new(),
            },
            ty,
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
    }

    #[test]
    fn rejects_arithmetic_until_it_is_guarded() {
        let int = Ty::Int(IntTy::I32);
        let binary = expression(
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
                value: Some(binary),
                span: Span::new(0, 1),
            }],
        );
        let error = emit_program(&program(vec![f]), 1, &EmitOptions::default()).unwrap_err();
        assert_eq!(error[0].name, "backend.unsupported");
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
}
