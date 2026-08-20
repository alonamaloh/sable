//! Strict textual LLVM IR lowering for the verified scalar, Boolean-option,
//! bounded POD-record, owned-local Boolean-array, local `u32`-array, direct
//! local Boolean owner-slot, and fixed-owner class core with internal borrows,
//! returns, and named moves (ADRs 0058--0059).
//!
//! The backend lowers scalar storage, calls, comparisons, and structured
//! control flow.  A construct is either lowered with its Sable meaning or
//! rejected with a source diagnostic; there is no silent fallback and no
//! unchecked arithmetic.

use crate::VerifiedProgram;
use crate::ast::{
    BinOp, BindingMode, ClassDecl, Expr, ExprKind, Fn, IntTy, Mutability, Program, RecordDecl,
    SelfKind, SlotOp, Stmt, Ty, UnOp,
};
use crate::control::{
    AssignmentAction, AssignmentStaging, BlockId, BodyPlan, ClassDropAction, ClassDropPhase,
    ClassDropPlan, ControlProgram, DropId, ExitRoute, PlanError, ScopeId, SlotAction,
    SlotActionKind, StatementPlanKind, TrapSite, ValueDropRecipe,
};
use crate::diag::Diagnostic;
use crate::ownership::{CheckedOwnershipPlan, ValueTransferKind};
use crate::place::Place;
use crate::span::Span;
use crate::transition::{
    CallArgumentEffect, CallEffect, CallOwner, CallSiteKey, CallTarget, CheckedCallTransition,
};
use std::collections::{BTreeSet, HashMap, HashSet};

const ARRAY_CAPACITY: u64 = 50_000_000;

pub type BackendError = Diagnostic;

#[derive(Debug, Clone, Default)]
pub struct EmitOptions {
    /// A root-module, zero-argument `i32`/unit function for which a C `main`
    /// bridge should be emitted.  Without an entry, every production function
    /// in the flattened checked program is considered.
    pub entry: Option<String>,
}

/// Lower the exact program accepted by Lean under the assurance carried by the
/// `VerifiedProgram`. The opaque capability keeps a production caller from
/// substituting a freshly loaded or mutated AST.
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
    let mut ir = emit_program_with_plans(
        verified.program(),
        verified.control(),
        verified.ownership(),
        verified.root_span_end(),
        options,
        verified.info().proof_assurance.summary(),
    )?;
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

#[cfg(test)]
fn emit_program(
    program: &Program,
    root_span_end: usize,
    options: &EmitOptions,
) -> Result<String, Vec<BackendError>> {
    emit_program_inner(
        program,
        None,
        None,
        root_span_end,
        options,
        "test-only unchecked input",
    )
}

#[cfg(test)]
fn emit_program_with_control(
    program: &Program,
    control: &ControlProgram,
    root_span_end: usize,
    options: &EmitOptions,
) -> Result<String, Vec<BackendError>> {
    emit_program_inner(
        program,
        Some(control),
        None,
        root_span_end,
        options,
        "test-only unchecked input",
    )
}

fn emit_program_with_plans(
    program: &Program,
    control: &ControlProgram,
    ownership: &CheckedOwnershipPlan,
    root_span_end: usize,
    options: &EmitOptions,
    proof_assurance: &str,
) -> Result<String, Vec<BackendError>> {
    emit_program_inner(
        program,
        Some(control),
        Some(ownership),
        root_span_end,
        options,
        proof_assurance,
    )
}

fn emit_program_inner(
    program: &Program,
    control: Option<&ControlProgram>,
    ownership: Option<&CheckedOwnershipPlan>,
    root_span_end: usize,
    options: &EmitOptions,
    proof_assurance: &str,
) -> Result<String, Vec<BackendError>> {
    let selected = select_callables(program, root_span_end, options)?;
    validate_acyclic(program, &selected)?;
    for &index in &selected.functions {
        validate_function(
            program,
            control,
            ownership,
            &program.fns[index],
            root_span_end,
        )?;
    }
    for &(class, initializer) in &selected.initializers {
        validate_initializer(
            program,
            control,
            ownership,
            class,
            &program.classes[class].inits[initializer],
            root_span_end,
        )?;
    }
    for &(class, method) in &selected.methods {
        validate_method(
            program,
            control,
            ownership,
            class,
            method,
            &program.classes[class].methods[method],
            root_span_end,
        )?;
    }

    let selected_set: HashSet<usize> = selected.functions.iter().copied().collect();
    let mut out = format!(
        "; Sable textual LLVM IR v0\n; Sable proof assurance: {}.\n; Exact checked-program capability retained for lowering (ADR 0058).\n\n",
        proof_assurance,
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
    for &(class, initializer) in &selected.initializers {
        FunctionEmitter::new_initializer(program, control, class, initializer, &mut support)?
            .emit(&mut definitions)?;
        definitions.push('\n');
    }
    for &(class, method) in &selected.methods {
        FunctionEmitter::new_method(program, control, class, method, &mut support)?
            .emit(&mut definitions)?;
        definitions.push('\n');
    }
    for (index, function) in program.fns.iter().enumerate() {
        if selected_set.contains(&index) {
            FunctionEmitter::new(program, control, function, &mut support)?
                .emit(&mut definitions)?;
            definitions.push('\n');
        }
    }

    if let Some(entry) = &options.entry {
        let function = program
            .fns
            .iter()
            .find(|function| function.name == *entry)
            .expect("entry selection validated above");
        emit_main_bridge(function, &mut definitions)?;
    }
    support.emit(program, &mut out)?;
    out.push_str(&definitions);
    Ok(out)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Callable {
    Function(usize),
    Initializer(usize, usize),
    Method(usize, usize),
}

#[derive(Default)]
struct SelectedCallables {
    functions: Vec<usize>,
    initializers: Vec<(usize, usize)>,
    methods: Vec<(usize, usize)>,
}

fn select_callables(
    program: &Program,
    root_span_end: usize,
    options: &EmitOptions,
) -> Result<SelectedCallables, Vec<BackendError>> {
    let mut selected: HashSet<Callable> = HashSet::new();
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
        if let Some(parameter) = function
            .params
            .iter()
            .find(|parameter| parameter.ty.is_affine_option())
        {
            return Err(vec![affine_option_unsupported(
                parameter.span,
                "LLVM entry parameter",
                parameter.ty.clone(),
            )]);
        }
        if function.ret.is_affine_option() {
            return Err(vec![affine_option_unsupported(
                function.name_span,
                "LLVM entry return type",
                function.ret.clone(),
            )]);
        }
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
        work.push(Callable::Function(index));
    } else {
        validate_whole_program_surface(program, root_span_end)?;
        work.extend(
            program
                .fns
                .iter()
                .enumerate()
                .filter(|(_, function)| !function.name.starts_with("test_"))
                .map(|(index, _)| Callable::Function(index)),
        );
    }

    while let Some(callable) = work.pop() {
        if !selected.insert(callable) {
            continue;
        }
        work.extend(callable_dependencies(program, callable)?);
    }

    let mut result = SelectedCallables::default();
    for callable in selected {
        match callable {
            Callable::Function(index) => result.functions.push(index),
            Callable::Initializer(class, initializer) => {
                result.initializers.push((class, initializer));
            }
            Callable::Method(class, method) => result.methods.push((class, method)),
        }
    }
    result.functions.sort_unstable();
    result.initializers.sort_unstable();
    result.methods.sort_unstable();
    Ok(result)
}

fn callable_body<'a>(program: &'a Program, callable: Callable) -> &'a [Stmt] {
    match callable {
        Callable::Function(index) => &program.fns[index].body,
        Callable::Initializer(class, initializer) => {
            &program.classes[class].inits[initializer].body
        }
        Callable::Method(class, method) => &program.classes[class].methods[method].f.body,
    }
}

fn callable_function(program: &Program, callable: Callable) -> &Fn {
    match callable {
        Callable::Function(index) => &program.fns[index],
        Callable::Initializer(class, initializer) => &program.classes[class].inits[initializer],
        Callable::Method(class, method) => &program.classes[class].methods[method].f,
    }
}

fn callable_name(program: &Program, callable: Callable) -> String {
    match callable {
        Callable::Function(index) => program.fns[index].name.clone(),
        Callable::Initializer(class, initializer) => format!(
            "{}::{}",
            program.classes[class].name, program.classes[class].inits[initializer].name
        ),
        Callable::Method(class, method) => format!(
            "{}::{}",
            program.classes[class].name, program.classes[class].methods[method].f.name
        ),
    }
}

fn callable_span(program: &Program, callable: Callable) -> Span {
    match callable {
        Callable::Function(index) => program.fns[index].name_span,
        Callable::Initializer(class, initializer) => {
            program.classes[class].inits[initializer].name_span
        }
        Callable::Method(class, method) => program.classes[class].methods[method].f.name_span,
    }
}

fn callable_dependencies(
    program: &Program,
    callable: Callable,
) -> Result<Vec<Callable>, Vec<BackendError>> {
    let body = callable_body(program, callable);
    let mut result = Vec::new();
    let mut calls = Vec::new();
    collect_calls_block(body, &mut calls);
    for (callee, span) in calls {
        let Some(index) = program
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
        if program.fns[index].name.starts_with("test_") {
            return Err(vec![diag(
                "backend.test_unsupported",
                "production code may not lower a dynamic test call",
                span,
                format!("`{callee}` is a test function"),
            )]);
        }
        result.push(Callable::Function(index));
    }

    let mut constructors = Vec::new();
    collect_constructors_block(body, &mut constructors);
    for (class_name, initializer_name, checked_class, span) in constructors {
        let Some(class) = checked_class else {
            return Err(vec![diag(
                "backend.constructor_missing",
                "constructor result has no checked class identity",
                span,
                format!("`{class_name}::{initializer_name}` is not typed as a class"),
            )]);
        };
        let Some(declaration) = program.classes.get(class) else {
            return Err(vec![diag(
                "backend.constructor_missing",
                "constructor result carries an invalid checked class index",
                span,
                format!("`{class_name}::{initializer_name}` carries class index {class}"),
            )]);
        };
        if declaration.name != class_name {
            return Err(vec![diag(
                "backend.constructor_missing",
                "constructor spelling disagrees with its checked class identity",
                span,
                format!(
                    "constructor spells `{class_name}`, but its result names `{}`",
                    declaration.name
                ),
            )]);
        }
        let Some(initializer) = declaration
            .inits
            .iter()
            .position(|declaration| declaration.name == initializer_name)
        else {
            return Err(vec![diag(
                "backend.constructor_missing",
                "LLVM lowering could not resolve a constructor",
                span,
                format!("class `{class_name}` has no initializer `{initializer_name}`"),
            )]);
        };
        result.push(Callable::Initializer(class, initializer));
    }
    let mut methods = Vec::new();
    collect_method_calls_block(body, &mut methods);
    for (receiver, method_name, span) in methods {
        let receiver_ty = if receiver == "self" {
            match callable {
                Callable::Initializer(class, _) | Callable::Method(class, _) => Ty::Class(class),
                Callable::Function(_) => {
                    return Err(vec![diag(
                        "backend.class_unsupported",
                        "method receiver `self` is outside a class member",
                        span,
                        "a free function has no implicit receiver",
                    )]);
                }
            }
        } else {
            callable_function(program, callable)
                .params
                .iter()
                .find(|parameter| parameter.name == receiver)
                .map(|parameter| parameter.ty.clone())
                .or_else(|| find_declared_type(body, &receiver))
                .ok_or_else(|| {
                    vec![diag(
                        "backend.class_unsupported",
                        "method receiver is not a checked local",
                        span,
                        format!("`{receiver}` has no declaration in this callable"),
                    )]
                })?
        };
        let class = match receiver_ty.class_index() {
            Some(class) => class,
            None => {
                let other = receiver_ty;
                return Err(vec![diag(
                    "backend.class_unsupported",
                    "method receiver has a non-class checked type",
                    span,
                    format!("`{receiver}` has type `{}`", other.name()),
                )]);
            }
        };
        let Some(receiver_class) = program.classes.get(class) else {
            return Err(vec![diag(
                "backend.class_unsupported",
                "method receiver carries an invalid checked class index",
                span,
                format!("`{receiver}` carries class index {class}, outside the checked program"),
            )]);
        };
        let candidates = receiver_class
            .methods
            .iter()
            .enumerate()
            .filter(|(_, method)| method.f.name == method_name)
            .map(|(method, _)| method)
            .collect::<Vec<_>>();
        let [method] = candidates.as_slice() else {
            return Err(vec![diag(
                "backend.method_missing",
                "LLVM lowering could not resolve a unique method",
                span,
                format!(
                    "method `{method_name}` has {} checked candidate(s)",
                    candidates.len()
                ),
            )]);
        };
        result.push(Callable::Method(class, *method));
    }
    Ok(result)
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

fn validate_acyclic(
    program: &Program,
    selected: &SelectedCallables,
) -> Result<(), Vec<BackendError>> {
    fn visit(
        program: &Program,
        callable: Callable,
        selected: &HashSet<Callable>,
        states: &mut HashMap<Callable, u8>,
    ) -> Result<(), BackendError> {
        if states.get(&callable) == Some(&1) {
            return Err(diag(
                "backend.recursion_unsupported",
                "recursive calls are outside the first LLVM subset",
                callable_span(program, callable),
                format!(
                    "`{}` participates in a recursive call cycle",
                    callable_name(program, callable)
                ),
            ));
        }
        if states.get(&callable) == Some(&2) {
            return Ok(());
        }
        states.insert(callable, 1);
        let dependencies = callable_dependencies(program, callable).map_err(|errors| {
            errors
                .into_iter()
                .next()
                .expect("dependency resolution reports at least one diagnostic")
        })?;
        for dependency in dependencies {
            if selected.contains(&dependency) {
                visit(program, dependency, selected, states)?;
            }
        }
        states.insert(callable, 2);
        Ok(())
    }

    let selected_set: HashSet<Callable> = selected
        .functions
        .iter()
        .copied()
        .map(Callable::Function)
        .chain(
            selected
                .initializers
                .iter()
                .copied()
                .map(|(class, initializer)| Callable::Initializer(class, initializer)),
        )
        .chain(
            selected
                .methods
                .iter()
                .copied()
                .map(|(class, method)| Callable::Method(class, method)),
        )
        .collect();
    let mut states = HashMap::new();
    for &callable in &selected_set {
        if let Err(error) = visit(program, callable, &selected_set, &mut states) {
            return Err(vec![error]);
        }
    }
    Ok(())
}

fn llvm_validation_plan<'a>(
    control: Option<&'a ControlProgram>,
    program: &Program,
    owner: &CallOwner,
    function: &Fn,
) -> Result<Option<&'a BodyPlan>, Vec<BackendError>> {
    let Some(control) = control else {
        // Raw AST lowering exists only for focused unit tests. Production
        // callers always provide the checker-retained carrier.
        return Ok(None);
    };
    let body = control
        .body(owner, function.span)
        .map_err(|error| vec![control_plan_backend_error(error)])?;
    body.validate_callable(function.span, &function.params, &function.body)
        .map_err(|error| vec![control_plan_backend_error(error)])?;
    for action in body.plan().field_assignments() {
        if let Some(drop_action) = action.drop_action() {
            control
                .validate_value_drop_action(drop_action, &program.classes, action.span())
                .map_err(|error| vec![control_plan_backend_error(error)])?;
        }
    }
    for action in body.plan().temporary_drops() {
        control
            .validate_value_drop_action(action.drop_action(), &program.classes, action.span())
            .map_err(|error| vec![control_plan_backend_error(error)])?;
    }
    validate_llvm_exposure_plan_tree(body.plan(), &function.body, body.plan().body_block().id())
        .map_err(|error| vec![control_plan_backend_error(error)])?;
    Ok(Some(body.plan()))
}

fn validate_function(
    program: &Program,
    control: Option<&ControlProgram>,
    ownership: Option<&CheckedOwnershipPlan>,
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
    let plan = llvm_validation_plan(
        control,
        program,
        &CallOwner::Function(function.name.clone()),
        function,
    )?;
    if let Some(parameter) = function
        .params
        .iter()
        .find(|parameter| parameter.ty.is_affine_option())
    {
        return Err(vec![affine_option_unsupported(
            parameter.span,
            "function parameter",
            parameter.ty.clone(),
        )]);
    }
    if function.ret.is_affine_option() {
        return Err(vec![affine_option_unsupported(
            function.name_span,
            "function return type",
            function.ret.clone(),
        )]);
    }
    for parameter in &function.params {
        require_parameter_value(
            program,
            root_span_end,
            parameter.ty.clone(),
            parameter.span,
            "function parameter",
        )?;
    }
    if let Ty::Class(class) = function.ret {
        require_fixed_class(program, class, function.name_span, "function return type")?;
    } else {
        require_runtime_type(
            program,
            root_span_end,
            function.ret.clone(),
            function.name_span,
            // `require_runtime_type` spells "<role> type"; the class refusal
            // above names the role on its own.
            "function return",
        )?;
    }
    let mut locals = ValidationLocals::with_method_authority(
        ownership,
        CallOwner::Function(function.name.clone()),
    );
    for parameter in &function.params {
        locals.insert(
            parameter.name.clone(),
            ValidationLocal {
                ty: parameter.ty.clone(),
                mutable: false,
            },
            parameter.span,
        )?;
    }
    validate_block(
        program,
        &function.body,
        root_span_end,
        &mut locals,
        function.ret.clone(),
        None,
        None,
        plan,
        plan.map(|plan| plan.body_block().id()),
    )?;
    locals.finish_method_authority(function.name_span)
}

#[derive(Clone, PartialEq, Eq)]
struct InitializerValidation {
    class: usize,
    fields_initialized: Vec<bool>,
}

fn validate_initializer(
    program: &Program,
    control: Option<&ControlProgram>,
    ownership: Option<&CheckedOwnershipPlan>,
    class: usize,
    initializer: &Fn,
    root_span_end: usize,
) -> Result<(), Vec<BackendError>> {
    let declaration = require_native_owner_class(
        program,
        class,
        root_span_end,
        initializer.name_span,
        "selected initializer",
    )?;
    if initializer.extern_info.is_some()
        || !initializer.type_params.is_empty()
        || !initializer.type_bounds.is_empty()
        || initializer.ret != Ty::Unit
    {
        return Err(vec![unsupported(
            initializer.name_span,
            format!(
                "initializer `{}::{}` is not a concrete internal unit initializer",
                program.classes[class].name, initializer.name
            ),
        )]);
    }
    let plan = llvm_validation_plan(
        control,
        program,
        &CallOwner::Constructor {
            class: program.classes[class].name.clone(),
            init: initializer.name.clone(),
        },
        initializer,
    )?;
    let mut locals = ValidationLocals::with_method_authority(
        ownership,
        CallOwner::Constructor {
            class: declaration.name.clone(),
            init: initializer.name.clone(),
        },
    );
    for parameter in &initializer.params {
        if require_fixed_class(
            program,
            class,
            initializer.name_span,
            "selected initializer",
        )
        .is_ok()
        {
            require_initializer_parameter(
                program,
                root_span_end,
                parameter.ty.clone(),
                parameter.span,
            )?;
        } else if !matches!(parameter.ty, Ty::Int(integer) if !matches!(integer, IntTy::TParam(_)))
        {
            return Err(vec![diag(
                "backend.class_unsupported",
                "scalar-owner constructor parameter is outside the exact internal ABI",
                parameter.span,
                format!(
                    "parameter `{}` has type `{}`; scalar-owner constructors accept concrete integers only",
                    parameter.name,
                    parameter.ty.name()
                ),
            )]);
        }
        locals.insert(
            parameter.name.clone(),
            ValidationLocal {
                ty: parameter.ty.clone(),
                mutable: false,
            },
            parameter.span,
        )?;
    }
    let mut context = InitializerValidation {
        class,
        fields_initialized: vec![false; declaration.fields.len()],
    };
    validate_block(
        program,
        &initializer.body,
        root_span_end,
        &mut locals,
        Ty::Unit,
        Some(&mut context),
        None,
        plan,
        plan.map(|plan| plan.body_block().id()),
    )?;
    if context
        .fields_initialized
        .iter()
        .any(|initialized| !initialized)
    {
        return Err(vec![unsupported(
            initializer.name_span,
            format!(
                "initializer `{}::{}` does not initialize every native field exactly once",
                program.classes[class].name, initializer.name
            ),
        )]);
    }
    locals.finish_method_authority(initializer.name_span)
}

fn validate_method(
    program: &Program,
    control: Option<&ControlProgram>,
    ownership: Option<&CheckedOwnershipPlan>,
    class: usize,
    method_index: usize,
    method: &crate::ast::Method,
    root_span_end: usize,
) -> Result<(), Vec<BackendError>> {
    let declaration = require_native_owner_class(
        program,
        class,
        root_span_end,
        method.f.name_span,
        "selected method",
    )?;
    let fixed = require_fixed_class(program, class, method.f.name_span, "selected method").is_ok();
    if fixed {
        if declaration.name != "Integer"
            || method_index != 0
            || method.f.name != "flip_sign"
            || method.self_kind != SelfKind::Mut
            || !method.f.params.is_empty()
            || method.f.ret != Ty::Unit
            || method.f.extern_info.is_some()
            || !method.f.type_params.is_empty()
            || !method.f.type_bounds.is_empty()
        {
            return Err(vec![diag(
                "backend.class_unsupported",
                "method is outside the concrete `Integer` surface the LLVM backend lowers",
                method.f.name_span,
                "the backend lowers only `Integer::flip_sign(&mut self) -> ()`, with no explicit arguments",
            )]);
        }
    } else {
        if declaration
            .methods
            .get(method_index)
            .is_none_or(|candidate| candidate.f.name != method.f.name)
        {
            return Err(vec![diag(
                "backend.method_missing",
                "selected scalar-owner method lost its checked identity",
                method.f.name_span,
                format!(
                    "class `{}` has no matching method at index {method_index}",
                    declaration.name
                ),
            )]);
        }
        for parameter in &method.f.params {
            require_scalar_owner_method_parameter(
                program,
                root_span_end,
                parameter.ty.clone(),
                parameter.span,
                &format!("method parameter `{}`", parameter.name),
            )?;
        }
        require_scalar_owner_method_result(
            program,
            root_span_end,
            method.f.ret.clone(),
            method.f.name_span,
        )?;
    }
    let plan = llvm_validation_plan(
        control,
        program,
        &CallOwner::Method {
            class: program.classes[class].name.clone(),
            method: method.f.name.clone(),
        },
        &method.f,
    )?;
    let mut locals = ValidationLocals::with_method_authority(
        ownership,
        CallOwner::Method {
            class: declaration.name.clone(),
            method: method.f.name.clone(),
        },
    );
    locals.insert(
        "self".into(),
        ValidationLocal {
            ty: Ty::borrow(
                match method.self_kind {
                    SelfKind::Shared => Mutability::Shared,
                    SelfKind::Mut => Mutability::Mut,
                },
                Ty::Class(class),
            ),
            mutable: method.self_kind == SelfKind::Mut,
        },
        method.f.name_span,
    )?;
    for parameter in &method.f.params {
        locals.insert(
            parameter.name.clone(),
            ValidationLocal {
                ty: parameter.ty.clone(),
                mutable: false,
            },
            parameter.span,
        )?;
    }
    validate_block(
        program,
        &method.f.body,
        root_span_end,
        &mut locals,
        method.f.ret.clone(),
        None,
        Some((class, method.self_kind)),
        plan,
        plan.map(|plan| plan.body_block().id()),
    )?;
    locals.finish_method_authority(method.f.name_span)
}

#[derive(Clone)]
struct ValidationLocal {
    ty: Ty,
    mutable: bool,
}

/// The checker reserves local names function-wide, while ordinary `if` and
/// `while` bodies have lexical lifetimes. `unsafe` is only a vocabulary gate,
/// so its declarations intentionally enter the current scope.
struct ValidationLocals {
    scopes: Vec<HashMap<String, ValidationLocal>>,
    declared: HashSet<String>,
    moved_classes: HashSet<String>,
    moved_slots: HashSet<String>,
    call_owner: Option<CallOwner>,
    checked_methods: HashMap<CallSiteKey, CheckedCallTransition>,
    visited_methods: HashSet<CallSiteKey>,
}

impl ValidationLocals {
    fn new() -> Self {
        Self {
            scopes: vec![HashMap::new()],
            declared: HashSet::new(),
            moved_classes: HashSet::new(),
            moved_slots: HashSet::new(),
            call_owner: None,
            checked_methods: HashMap::new(),
            visited_methods: HashSet::new(),
        }
    }

    fn with_method_authority(ownership: Option<&CheckedOwnershipPlan>, owner: CallOwner) -> Self {
        let mut locals = Self::new();
        let Some(ownership) = ownership else {
            return locals;
        };
        locals.call_owner = Some(owner.clone());
        locals.checked_methods = ownership
            .calls
            .for_owner(&owner)
            .filter(|(key, _)| matches!(key.target, CallTarget::Method { .. }))
            .map(|(key, call)| (key.clone(), call.clone()))
            .collect();
        locals
    }

    fn checked_method_call(
        &mut self,
        key: &CallSiteKey,
        span: Span,
    ) -> Result<Option<CheckedCallTransition>, Vec<BackendError>> {
        let Some(owner) = self.call_owner.as_ref() else {
            return Ok(None);
        };
        if &key.owner != owner {
            return Err(vec![diag(
                "internal.control_plan_invalid",
                "method call is detached from its checked callable owner",
                span,
                format!(
                    "expected {}, observed {}",
                    owner.render(),
                    key.owner.render()
                ),
            )]);
        }
        let Some(call) = self.checked_methods.get(key).cloned() else {
            return Err(vec![diag(
                "internal.control_plan_invalid",
                "LLVM method call has no exact checker-authored call plan",
                span,
                format!(
                    "{} at this source identity was not retained for {}",
                    key.target.render(),
                    owner.render()
                ),
            )]);
        };
        if call.key != *key {
            return Err(vec![diag(
                "internal.control_plan_invalid",
                "LLVM method call plan has a detached value identity",
                span,
                "the retained transition key must exactly match its checker-authored map key",
            )]);
        }
        if !self.visited_methods.insert(key.clone()) {
            return Err(vec![diag(
                "internal.control_plan_invalid",
                "LLVM method call reused one checked call identity",
                span,
                "each retained method transition must be consumed exactly once",
            )]);
        }
        Ok(Some(call))
    }

    fn finish_method_authority(&self, span: Span) -> Result<(), Vec<BackendError>> {
        if let Some((key, _)) = self
            .checked_methods
            .iter()
            .find(|(key, _)| !self.visited_methods.contains(*key))
        {
            return Err(vec![diag(
                "internal.control_plan_invalid",
                "checked method call was not consumed by LLVM validation",
                span,
                format!(
                    "unused transition for {} at byte {}",
                    key.target.render(),
                    key.span.start
                ),
            )]);
        }
        Ok(())
    }

    fn insert(
        &mut self,
        name: String,
        local: ValidationLocal,
        span: Span,
    ) -> Result<(), Vec<BackendError>> {
        if !self.declared.insert(name.clone()) {
            return Err(vec![unsupported(
                span,
                format!("duplicate LLVM local `{name}` escaped checking"),
            )]);
        }
        self.scopes
            .last_mut()
            .expect("validation has a function scope")
            .insert(name.clone(), local);
        self.moved_classes.remove(&name);
        self.moved_slots.remove(&name);
        Ok(())
    }

    fn get(&self, name: &str) -> Option<ValidationLocal> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).cloned())
    }

    fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    fn pop_scope(&mut self) {
        assert!(self.scopes.len() > 1, "cannot pop the function scope");
        let removed = self.scopes.pop().expect("validated lexical scope");
        for name in removed.keys() {
            self.moved_classes.remove(name);
            self.moved_slots.remove(name);
        }
    }

    fn require_live_class(
        &self,
        name: &str,
        span: Span,
        role: &str,
    ) -> Result<(), Vec<BackendError>> {
        if self.moved_classes.contains(name) {
            return Err(vec![diag(
                "backend.class_moved",
                "fixed-owner class value was already moved",
                span,
                format!("{role} uses moved-from class local `{name}`"),
            )]);
        }
        Ok(())
    }

    fn mark_class_moved(&mut self, name: &str) {
        self.moved_classes.insert(name.to_owned());
    }

    fn require_live_slots(
        &self,
        name: &str,
        span: Span,
        role: &str,
    ) -> Result<(), Vec<BackendError>> {
        if self.moved_slots.contains(name) {
            return Err(vec![diag(
                "backend.slots_moved",
                "owner-slot value was already moved",
                span,
                format!("{role} uses moved-from owner-slot local `{name}`"),
            )]);
        }
        Ok(())
    }

    fn mark_slots_moved(&mut self, name: &str) {
        self.moved_slots.insert(name.to_owned());
    }
}

fn validate_llvm_exposure_plan_shape(
    plan: &BodyPlan,
    parent_block: BlockId,
    parent_scope: ScopeId,
    kw_span: Span,
    array: &str,
    mutable: bool,
    ptr: &str,
    res: &str,
) -> Result<(), PlanError> {
    let exposure = plan.exposure_plan(parent_scope, kw_span)?;
    let body = plan.block(exposure.body());
    let Some(normal) = exposure.normal() else {
        return Err(PlanError {
            span: kw_span,
            message: "checked LLVM exposure has no retained normal epilogue".into(),
        });
    };
    let rebuild = normal.rebuild();
    let mutability = if mutable {
        Mutability::Mut
    } else {
        Mutability::Shared
    };
    if exposure.parent_scope() != parent_scope
        || exposure.keyword_span() != kw_span
        || body.parent() != Some(parent_block)
        || body.scope() != exposure.body_scope()
        || !exposure.body_flow().can_fall_through()
        || normal.parent_scope() != parent_scope
        || normal.capture() != &Place::local(res)
        || normal.body_exit().scopes() != [exposure.body_scope()]
        || rebuild.owner() != &Place::local(array)
        || !matches!(rebuild.owner_ty().as_array(), Some((Ty::Int(IntTy::U8), _)))
        || rebuild.mutability() != mutability
        || rebuild.pointer() != &Place::local(ptr)
        || rebuild.resource() != &Place::local(res)
        || rebuild.keyword_span() != kw_span
        || !normal.release_loan().is_root()
        || normal.close().clears().last() != Some(normal.release_loan())
    {
        return Err(PlanError {
            span: kw_span,
            message: "LLVM exposure disagrees with its retained parent/body/epilogue shape".into(),
        });
    }
    Ok(())
}

fn validate_llvm_exposure_plan_tree(
    plan: &BodyPlan,
    statements: &[Stmt],
    block: BlockId,
) -> Result<(), PlanError> {
    let retained = plan.block(block);
    if retained.statements().len() != statements.len() {
        return Err(PlanError {
            span: retained.anchor(),
            message: "LLVM exposure preflight found a changed retained block length".into(),
        });
    }
    let scope = retained.scope();
    let statement_plans = retained.statements().to_vec();
    for (statement, statement_plan) in statements.iter().zip(statement_plans) {
        match (statement_plan.kind(), statement) {
            (StatementPlanKind::Unsafe(child), Stmt::Unsafe { body, .. }) => {
                validate_llvm_exposure_plan_tree(plan, body, child)?;
            }
            (
                StatementPlanKind::Branch(_),
                Stmt::If {
                    cond,
                    then_block,
                    else_block,
                },
            ) => {
                let branch = plan.branch(scope, cond.span, else_block.is_some())?;
                validate_llvm_exposure_plan_tree(plan, then_block, branch.then_arm().block())?;
                if let (Some(source), Some(arm)) = (else_block.as_deref(), branch.else_arm()) {
                    validate_llvm_exposure_plan_tree(plan, source, arm.block())?;
                }
            }
            (
                StatementPlanKind::Loop(_),
                Stmt::While {
                    cond,
                    kw_span,
                    body,
                    ..
                },
            ) => {
                let loop_plan = plan.loop_plan(scope, *kw_span, cond.span)?;
                validate_llvm_exposure_plan_tree(plan, body, loop_plan.body())?;
            }
            (
                StatementPlanKind::Exposure(_),
                Stmt::Expose {
                    kw_span,
                    array,
                    mutable,
                    ptr,
                    res,
                    body,
                    ..
                },
            ) => {
                validate_llvm_exposure_plan_shape(
                    plan, block, scope, *kw_span, array, *mutable, ptr, res,
                )?;
                let exposure = plan.exposure_plan(scope, *kw_span)?;
                validate_llvm_exposure_plan_tree(plan, body, exposure.body())?;
            }
            _ => {}
        }
    }
    Ok(())
}

fn validate_block(
    program: &Program,
    statements: &[Stmt],
    root_span_end: usize,
    locals: &mut ValidationLocals,
    ret_ty: Ty,
    mut initializer: Option<&mut InitializerValidation>,
    method: Option<(usize, SelfKind)>,
    plan: Option<&BodyPlan>,
    block: Option<BlockId>,
) -> Result<bool, Vec<BackendError>> {
    let retained = match (plan, block) {
        (Some(plan), Some(block)) => {
            let block = plan.block(block);
            if block.statements().len() != statements.len() {
                return Err(vec![control_plan_backend_error(PlanError {
                    span: block.anchor(),
                    message: "LLVM validation block length changed after checking".into(),
                })]);
            }
            Some((
                block.scope(),
                block.flow(),
                block.anchor(),
                block.statements().to_vec(),
            ))
        }
        (None, None) => None,
        _ => {
            return Err(vec![control_plan_backend_error(PlanError {
                span: Span::new(0, 0),
                message: "LLVM validation received a partial retained block context".into(),
            })]);
        }
    };
    let mut returned = false;
    for (index, statement) in statements.iter().enumerate() {
        let statement_plan = retained
            .as_ref()
            .map(|(_, _, _, statements)| &statements[index]);
        let entry_reachable =
            statement_plan.map_or(!returned, |statement| statement.entry_reachable());
        if !entry_reachable {
            break;
        }
        if let Some(statement_plan) = statement_plan {
            let kind = statement_plan.kind();
            let matches = match statement {
                Stmt::Return { .. } => matches!(kind, StatementPlanKind::Return),
                Stmt::If { .. } => matches!(kind, StatementPlanKind::Branch(_)),
                Stmt::While { .. } => matches!(kind, StatementPlanKind::Loop(_)),
                Stmt::Unsafe { .. } => matches!(kind, StatementPlanKind::Unsafe(_)),
                Stmt::Expose { .. } => matches!(kind, StatementPlanKind::Exposure(_)),
                Stmt::Decl { .. }
                | Stmt::Assign { .. }
                | Stmt::ExprStmt(_)
                | Stmt::Assert(_)
                | Stmt::VarDecl { .. }
                | Stmt::FieldAssign { .. }
                | Stmt::FieldStore { .. }
                | Stmt::Store { .. }
                | Stmt::StaticAlloc { .. }
                | Stmt::SystemAlloc { .. }
                | Stmt::SystemDealloc { .. } => matches!(kind, StatementPlanKind::Linear(_)),
            };
            if !matches {
                return Err(vec![control_plan_backend_error(PlanError {
                    span: retained
                        .as_ref()
                        .map_or(Span::new(0, 0), |(_, _, anchor, _)| *anchor),
                    message: "LLVM validation statement changed its retained structural role"
                        .into(),
                })]);
            }
        }
        if let (Some(plan), Some((scope, _, _, _))) = (plan, retained.as_ref()) {
            match statement {
                Stmt::FieldAssign {
                    field,
                    field_span,
                    value,
                } => {
                    let destination = Place::field("self", field);
                    let action = plan
                        .field_assignment(*scope, *field_span, &destination, value)
                        .map_err(|error| vec![control_plan_backend_error(error)])?;
                    let staging_matches = matches!(
                        (action.drop_if_present(), action.staging()),
                        (true, AssignmentStaging::Temporary(temp)) if temp.is_root()
                    ) || matches!(
                        (action.drop_if_present(), action.staging()),
                        (false, AssignmentStaging::Direct)
                    );
                    if action.scope() != *scope
                        || action.destination() != &destination
                        || !staging_matches
                    {
                        return Err(vec![control_plan_backend_error(PlanError {
                            span: *field_span,
                            message: "LLVM field assignment is detached from its retained action"
                                .into(),
                        })]);
                    }
                }
                Stmt::ExprStmt(expression) if matches!(expression.ty, Some(Ty::Class(_))) => {
                    let action = plan
                        .temporary_drop(*scope, expression)
                        .map_err(|error| vec![control_plan_backend_error(error)])?;
                    if action.scope() != *scope || !action.temporary().is_root() {
                        return Err(vec![control_plan_backend_error(PlanError {
                            span: expression.span,
                            message: "LLVM discarded class result is detached from its retained temporary action"
                                .into(),
                        })]);
                    }
                }
                _ => {}
            }
        }
        match statement {
            Stmt::Decl {
                ty,
                name,
                name_span,
                init,
                mutable,
            } => {
                if matches!(ty, Ty::Slots(_)) {
                    if !is_owned_bool_slots(ty) {
                        return Err(vec![slots_unsupported(
                            *name_span,
                            format!("local `{name}` with type `{}`", ty.name()),
                        )]);
                    }
                    let Some(value) = init else {
                        return Err(vec![diag(
                            "backend.slots_initializer",
                            "native owner-slot local has no initializer",
                            *name_span,
                            format!("`{name}` must receive an allocation or whole-owner move"),
                        )]);
                    };
                    validate_bool_slots_initializer(program, value, root_span_end, locals, name)?;
                } else if ty.is_affine_option() {
                    validate_affine_bool_option_decl(
                        program,
                        name,
                        ty.clone(),
                        *mutable,
                        init.as_ref(),
                        root_span_end,
                        locals,
                        *name_span,
                    )?;
                } else if is_owned_native_array(&ty.clone()) {
                    require_local_value(
                        program,
                        root_span_end,
                        ty.clone(),
                        *name_span,
                        "local variable",
                    )?;
                    let Some(value) = init else {
                        return Err(vec![unsupported(
                            *name_span,
                            format!("owned array local `{name}` has no initializer"),
                        )]);
                    };
                    if ty.is_owned_bool_array() {
                        validate_fresh_bool_array_initializer(
                            program,
                            value,
                            root_span_end,
                            locals,
                            name,
                            true,
                        )?;
                    } else {
                        validate_fresh_u32_array_initializer(
                            program,
                            value,
                            root_span_end,
                            locals,
                        )?;
                    }
                } else if let Ty::Class(class) = ty {
                    require_native_owner_class(
                        program,
                        *class,
                        root_span_end,
                        *name_span,
                        "local variable",
                    )?;
                    if let Some(value) = init {
                        validate_fixed_class_initializer(
                            program,
                            *class,
                            value,
                            root_span_end,
                            locals,
                        )?;
                    }
                } else {
                    require_local_value(
                        program,
                        root_span_end,
                        ty.clone(),
                        *name_span,
                        "local variable",
                    )?;
                    if let Some(value) = init {
                        validate_expr(program, value, root_span_end, locals)?;
                    }
                }
                locals.insert(
                    name.clone(),
                    ValidationLocal {
                        ty: ty.clone(),
                        mutable: *mutable,
                    },
                    *name_span,
                )?;
            }
            Stmt::VarDecl {
                ty,
                name,
                name_span,
                init,
                mutable,
            } => {
                let Some(ref ty) = *ty else {
                    return Err(vec![unsupported(
                        *name_span,
                        "inferred local is missing its checked type",
                    )]);
                };
                if matches!(ty, Ty::Slots(_)) {
                    if !is_owned_bool_slots(ty) {
                        return Err(vec![slots_unsupported(
                            *name_span,
                            format!("inferred local `{name}` with type `{}`", ty.name()),
                        )]);
                    }
                    validate_bool_slots_initializer(program, init, root_span_end, locals, name)?;
                    locals.insert(
                        name.clone(),
                        ValidationLocal {
                            ty: ty.clone(),
                            mutable: *mutable,
                        },
                        *name_span,
                    )?;
                    continue;
                }
                if let Ty::Class(class) = ty {
                    validate_fixed_class_initializer(program, *class, init, root_span_end, locals)?;
                    locals.insert(
                        name.clone(),
                        ValidationLocal {
                            ty: ty.clone(),
                            mutable: *mutable,
                        },
                        *name_span,
                    )?;
                    continue;
                }
                if ty.is_affine_option() {
                    return Err(vec![affine_option_unsupported(
                        *name_span,
                        "inferred local",
                        ty.clone(),
                    )]);
                }
                if matches!(init.kind, ExprKind::OptTake { .. }) {
                    return Err(vec![affine_option_take_position(
                        init.span,
                        name,
                        "inferred declaration",
                    )]);
                }
                require_local_value(
                    program,
                    root_span_end,
                    ty.clone(),
                    *name_span,
                    "inferred local",
                )?;
                if is_owned_native_array(&ty.clone()) {
                    if ty.is_owned_bool_array() {
                        validate_fresh_bool_array_initializer(
                            program,
                            init,
                            root_span_end,
                            locals,
                            name,
                            false,
                        )?;
                    } else {
                        validate_fresh_u32_array_initializer(program, init, root_span_end, locals)?;
                    }
                } else {
                    validate_expr(program, init, root_span_end, locals)?;
                }
                locals.insert(
                    name.clone(),
                    ValidationLocal {
                        ty: ty.clone(),
                        mutable: *mutable,
                    },
                    *name_span,
                )?;
            }
            Stmt::Assign {
                name,
                name_span,
                value,
            } => {
                let Some(local) = locals.get(name) else {
                    return Err(vec![unsupported(
                        *name_span,
                        format!("assignment names unknown or out-of-scope local `{name}`"),
                    )]);
                };
                if !local.mutable {
                    return Err(vec![unsupported(
                        *name_span,
                        format!("assignment targets immutable local `{name}`"),
                    )]);
                }
                if matches!(local.ty, Ty::Slots(_)) {
                    if !is_owned_bool_slots(&local.ty) {
                        return Err(vec![slots_unsupported(
                            *name_span,
                            format!("assignment to `{name}` with type `{}`", local.ty.name()),
                        )]);
                    }
                    validate_bool_slots_initializer(program, value, root_span_end, locals, name)?;
                    locals.moved_slots.remove(name);
                    continue;
                }
                if is_owned_native_array(&local.ty) {
                    return Err(vec![unsupported(
                        *name_span,
                        format!("owned array local `{name}` cannot be rebound"),
                    )]);
                }
                if let Ty::Class(class) = local.ty {
                    validate_fixed_class_initializer(program, class, value, root_span_end, locals)?;
                    // Assignment installs a fresh owner even when the old
                    // destination had already been moved from. The RHS was
                    // validated first so self-borrows still require the old
                    // destination to be live.
                    locals.moved_classes.remove(name);
                    continue;
                }
                if local.ty.is_affine_option() {
                    return Err(vec![affine_option_unsupported(
                        *name_span,
                        &format!("whole-option assignment to `{name}`"),
                        local.ty,
                    )]);
                }
                validate_expr(program, value, root_span_end, locals)?;
                require_expr_type(value, local.ty, "assignment value")?;
            }
            Stmt::ExprStmt(value) => validate_expr(program, value, root_span_end, locals)?,
            Stmt::Return { span, .. } if initializer.is_some() => {
                return Err(vec![unsupported(
                    *span,
                    "fixed-owner native initializers may not return early",
                )]);
            }
            Stmt::Return {
                value: Some(value),
                span: _,
            } => {
                require_expr_type(value, ret_ty.clone(), "return value")?;
                if let Ty::Class(class) = ret_ty {
                    validate_fixed_class_initializer(program, class, value, root_span_end, locals)?;
                } else {
                    validate_expr(program, value, root_span_end, locals)?;
                }
                returned = true;
            }
            Stmt::Return { value: None, span } => {
                if ret_ty != Ty::Unit {
                    return Err(vec![unsupported(
                        *span,
                        format!(
                            "value-less return in function returning `{}`",
                            ret_ty.name()
                        ),
                    )]);
                }
                returned = true;
            }
            Stmt::Assert(_) => {}
            Stmt::Unsafe { body, .. } => {
                let child = statement_plan.and_then(|statement| match statement.kind() {
                    StatementPlanKind::Unsafe(child) => Some(child),
                    _ => None,
                });
                returned = validate_block(
                    program,
                    body,
                    root_span_end,
                    locals,
                    ret_ty.clone(),
                    initializer.as_deref_mut(),
                    method,
                    plan,
                    child,
                )?;
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                let branch_plan = match (plan, retained.as_ref()) {
                    (Some(plan), Some((scope, _, _, _))) => Some(
                        plan.branch(*scope, cond.span, else_block.is_some())
                            .map_err(|error| vec![control_plan_backend_error(error)])?
                            .clone(),
                    ),
                    (None, None) => None,
                    _ => unreachable!("retained validation context is all-or-none"),
                };
                validate_bool_expr(program, cond, "`if` condition", root_span_end, locals)?;
                let base_initializer = initializer.as_deref().cloned();
                let before_moved = locals.moved_classes.clone();
                let before_moved_slots = locals.moved_slots.clone();
                locals.push_scope();
                let mut then_initializer = base_initializer.clone();
                let then_returned = validate_block(
                    program,
                    then_block,
                    root_span_end,
                    locals,
                    ret_ty.clone(),
                    then_initializer.as_mut(),
                    method,
                    plan,
                    branch_plan.as_ref().map(|branch| branch.then_arm().block()),
                )?;
                locals.pop_scope();
                let then_moved = locals.moved_classes.clone();
                let then_moved_slots = locals.moved_slots.clone();
                locals.moved_classes = before_moved.clone();
                locals.moved_slots = before_moved_slots.clone();
                let mut else_initializer = base_initializer.clone();
                let (else_returned, else_moved, else_moved_slots) =
                    if let Some(else_block) = else_block {
                        locals.push_scope();
                        let else_returned = validate_block(
                            program,
                            else_block,
                            root_span_end,
                            locals,
                            ret_ty.clone(),
                            else_initializer.as_mut(),
                            method,
                            plan,
                            branch_plan
                                .as_ref()
                                .and_then(|branch| branch.else_arm())
                                .map(|arm| arm.block()),
                        )?;
                        locals.pop_scope();
                        (
                            else_returned,
                            locals.moved_classes.clone(),
                            locals.moved_slots.clone(),
                        )
                    } else {
                        (false, before_moved.clone(), before_moved_slots.clone())
                    };
                if then_initializer != else_initializer {
                    return Err(vec![unsupported(
                        cond.span,
                        "fixed-owner class field initialization may not differ across branches",
                    )]);
                }
                if let (Some(target), Some(merged)) = (initializer.as_deref_mut(), then_initializer)
                {
                    *target = merged;
                }
                if !then_returned && !else_returned && then_moved != else_moved {
                    return Err(vec![diag(
                        "backend.class_branch_shape",
                        "fixed-owner class state differs across branch paths",
                        cond.span,
                        "every reaching branch must leave the same class owners live",
                    )]);
                }
                if !then_returned && !else_returned && then_moved_slots != else_moved_slots {
                    return Err(vec![diag(
                        "backend.slots_branch_shape",
                        "owner-slot state differs across branch paths",
                        cond.span,
                        "every reaching branch must leave the same owner-slot locals live",
                    )]);
                }
                locals.moved_classes = match (then_returned, else_returned) {
                    (true, true) => before_moved,
                    (true, false) => else_moved,
                    (false, true) => then_moved,
                    (false, false) => then_moved,
                };
                locals.moved_slots = match (then_returned, else_returned) {
                    (true, true) => before_moved_slots,
                    (true, false) => else_moved_slots,
                    (false, true) => then_moved_slots,
                    (false, false) => then_moved_slots,
                };
                returned = then_returned && else_returned;
            }
            Stmt::While {
                cond,
                kw_span,
                body,
                ..
            } => {
                let loop_plan = match (plan, retained.as_ref()) {
                    (Some(plan), Some((scope, _, _, _))) => Some(
                        plan.loop_plan(*scope, *kw_span, cond.span)
                            .map_err(|error| vec![control_plan_backend_error(error)])?
                            .clone(),
                    ),
                    (None, None) => None,
                    _ => unreachable!("retained validation context is all-or-none"),
                };
                validate_bool_expr(program, cond, "`while` condition", root_span_end, locals)?;
                let before = initializer.as_deref().cloned();
                let before_moved = locals.moved_classes.clone();
                let before_moved_slots = locals.moved_slots.clone();
                let mut body_initializer = before.clone();
                locals.push_scope();
                let body_returned = validate_block(
                    program,
                    body,
                    root_span_end,
                    locals,
                    ret_ty.clone(),
                    body_initializer.as_mut(),
                    method,
                    plan,
                    loop_plan.as_ref().map(|loop_plan| loop_plan.body()),
                )?;
                locals.pop_scope();
                if body_initializer != before {
                    return Err(vec![unsupported(
                        cond.span,
                        "fixed-owner class field initialization may not occur in a loop",
                    )]);
                }
                if !body_returned && locals.moved_classes != before_moved {
                    return Err(vec![diag(
                        "backend.class_loop_shape",
                        "fixed-owner class state changes across a loop backedge",
                        cond.span,
                        "every reaching iteration must restore the same live class owners",
                    )]);
                }
                if !body_returned && locals.moved_slots != before_moved_slots {
                    return Err(vec![diag(
                        "backend.slots_loop_shape",
                        "owner-slot state changes across a loop backedge",
                        cond.span,
                        "every reaching iteration must restore the same live owner-slot locals",
                    )]);
                }
                locals.moved_classes = before_moved;
                locals.moved_slots = before_moved_slots;
            }
            Stmt::FieldAssign {
                field,
                field_span,
                value,
            } => validate_initializer_field_assign(
                program,
                field,
                *field_span,
                value,
                root_span_end,
                locals,
                initializer.as_deref_mut(),
                method,
            )?,
            Stmt::FieldStore {
                field,
                field_span,
                index,
                value,
            } => validate_initializer_field_store(
                program,
                field,
                *field_span,
                index,
                value,
                root_span_end,
                locals,
                initializer.as_deref(),
            )?,
            Stmt::Store {
                array,
                array_span,
                index,
                value,
            } => validate_native_array_store(
                program,
                array,
                *array_span,
                index,
                value,
                root_span_end,
                locals,
            )?,
            Stmt::Expose {
                kw_span,
                array,
                array_span,
                mutable,
                ptr,
                res,
                ..
            } => {
                reject_named_affine_option(locals, array, *array_span, "array exposure source")?;
                if let (Some(plan), Some(block), Some((scope, _, _, _))) =
                    (plan, block, retained.as_ref())
                {
                    validate_llvm_exposure_plan_shape(
                        plan, block, *scope, *kw_span, array, *mutable, ptr, res,
                    )
                    .map_err(|error| vec![control_plan_backend_error(error)])?;
                }
                return Err(vec![unsupported(
                    *kw_span,
                    "raw/resource storage is outside the scalar LLVM subset",
                )]);
            }
            Stmt::StaticAlloc { kw_span, .. }
            | Stmt::SystemAlloc { kw_span, .. }
            | Stmt::SystemDealloc { kw_span, .. } => {
                return Err(vec![unsupported(
                    *kw_span,
                    "raw/resource storage is outside the scalar LLVM subset",
                )]);
            }
        }
        if let Some(statement_plan) = statement_plan {
            let planned_return = statement_plan.flow().definitely_returns();
            if returned != planned_return {
                return Err(vec![control_plan_backend_error(PlanError {
                    span: retained
                        .as_ref()
                        .map_or(Span::new(0, 0), |(_, _, anchor, _)| *anchor),
                    message:
                        "LLVM validation reachability disagrees with its retained statement flow"
                            .into(),
                })]);
            }
            returned = planned_return;
        }
    }
    if let Some((_, flow, anchor, _)) = retained {
        let planned_return = flow.definitely_returns();
        if returned != planned_return {
            return Err(vec![control_plan_backend_error(PlanError {
                span: anchor,
                message: "LLVM validation block result disagrees with its retained flow".into(),
            })]);
        }
        Ok(planned_return)
    } else {
        Ok(returned)
    }
}

fn is_owned_u32_array(ty: Ty) -> bool {
    ty.is_owned_array_of(&Ty::Int(IntTy::U32))
}

fn is_u32_array(ty: &Ty) -> bool {
    ty.is_array_of(&Ty::Int(IntTy::U32))
}

fn is_owned_native_array(ty: &Ty) -> bool {
    ty.is_owned_bool_array() || is_owned_u32_array(ty.clone())
}

/// An array the backend has a descriptor for, in any binding mode.
fn is_native_array(ty: &Ty) -> bool {
    ty.is_bool_array() || is_u32_array(ty)
}

fn is_owned_bool_slots(ty: &Ty) -> bool {
    matches!(ty, Ty::Slots(payload) if payload.as_ref() == &Ty::Bool)
}

fn is_concrete_scalar(ty: &Ty) -> bool {
    matches!(ty, Ty::Bool) || matches!(ty, Ty::Int(integer) if !matches!(integer, IntTy::TParam(_)))
}

/// A deliberately module-internal owner shape for exercising the exact
/// method ABI without widening the older `Nat`/`Integer` gate.  The class is
/// represented by one LLVM aggregate containing only concrete integer
/// fields; it carries no nested ownership, erased authority, generic proof
/// reuse, executable destruction, or public/cross-module surface.
fn require_exact_scalar_owner_class<'a>(
    program: &'a Program,
    class: usize,
    root_span_end: usize,
    span: Span,
    role: &str,
) -> Result<&'a ClassDecl, Vec<BackendError>> {
    let Some(declaration) = program.classes.get(class) else {
        return Err(vec![diag(
            "backend.class_unsupported",
            "scalar-owner class carries an invalid checked class index",
            span,
            format!("{role} carries class index {class}, outside the checked program"),
        )]);
    };
    let member_is_internal = |function: &Fn| {
        !function.is_pub
            && function.extern_info.is_none()
            && function.name_span.start < root_span_end
            && function.type_params.is_empty()
            && function.type_bounds.is_empty()
            && function.proof_reuse.is_none()
            && function.params.iter().all(|parameter| !parameter.consumes)
    };
    let supported = declaration.name != "Nat"
        && declaration.name != "Integer"
        && !declaration.is_pub
        && declaration.name_span.start < root_span_end
        && declaration.type_params.is_empty()
        && declaration.type_bounds.is_empty()
        && declaration.proof_reuse.is_none()
        && !declaration.fields.is_empty()
        && declaration.fields.iter().all(|field| {
            !field.must_consume
                && matches!(field.ty, Ty::Int(integer) if !matches!(integer, IntTy::TParam(_)))
        })
        && declaration.inits.iter().all(member_is_internal)
        && declaration
            .methods
            .iter()
            .all(|method| member_is_internal(&method.f))
        && matches!(declaration.deinit.as_deref(), None | Some([]));
    if !supported {
        return Err(vec![diag(
            "backend.class_unsupported",
            "class is outside the exact scalar-owner LLVM subset",
            span,
            format!(
                "{role} uses `{}`; scalar owners must be private root-module classes with only concrete integer fields, ProofReuse::None, no generic metadata, no must-consume fields, and absent or empty destruction",
                declaration.name
            ),
        )]);
    }
    Ok(declaration)
}

fn require_native_owner_class<'a>(
    program: &'a Program,
    class: usize,
    root_span_end: usize,
    span: Span,
    role: &str,
) -> Result<&'a ClassDecl, Vec<BackendError>> {
    if let Ok(declaration) = require_fixed_class(program, class, span, role) {
        return Ok(declaration);
    }
    require_exact_scalar_owner_class(program, class, root_span_end, span, role)
}

fn require_fixed_class<'a>(
    program: &'a Program,
    class: usize,
    span: Span,
    role: &str,
) -> Result<&'a ClassDecl, Vec<BackendError>> {
    let Some(declaration) = program.classes.get(class) else {
        return Err(vec![unsupported(
            span,
            format!("{role} carries class index {class}, outside the checked program"),
        )]);
    };
    let common_supported = declaration.type_params.is_empty()
        && declaration.type_bounds.is_empty()
        && declaration.proof_reuse.is_none()
        && declaration.fields.iter().all(|field| !field.must_consume);
    let nat_supported = declaration.name == "Nat"
        && declaration.fields.len() == 1
        && declaration.fields[0].name == "limbs"
        && declaration.fields[0].ty == Ty::array(Ty::Int(IntTy::U32))
        && declaration.methods.is_empty()
        && matches!(declaration.deinit.as_deref(), Some([]));
    let integer_supported = declaration.name == "Integer"
        && declaration.fields.len() == 2
        && declaration.fields[0].name == "mag"
        && matches!(declaration.fields[0].ty, Ty::Class(child) if child != class)
        && declaration.fields[1].name == "neg"
        && declaration.fields[1].ty == Ty::Int(IntTy::U64)
        && declaration.methods.len() == 1
        && declaration.methods[0].f.name == "flip_sign"
        && declaration.methods[0].self_kind == SelfKind::Mut
        && declaration.methods[0].f.params.is_empty()
        && declaration.methods[0].f.ret == Ty::Unit
        && matches!(declaration.deinit.as_deref(), None | Some([]));
    if !common_supported || (!nat_supported && !integer_supported) {
        return Err(vec![diag(
            "backend.class_unsupported",
            "class is outside the fixed-owner class shapes the LLVM backend lowers",
            span,
            format!(
                "{role} uses `{}`; the backend lowers only the concrete `Nat {{ [u32] limbs }}` and `Integer {{ Nat mag; u64 neg }}` shapes, each with an empty destruction and method surface",
                declaration.name
            ),
        )]);
    }
    if integer_supported {
        let Ty::Class(child) = declaration.fields[0].ty else {
            unreachable!("checked Integer magnitude field")
        };
        let Some(child_declaration) = program.classes.get(child) else {
            return Err(vec![diag(
                "backend.class_unsupported",
                "Integer magnitude carries an invalid class index",
                span,
                format!("`{}.mag` carries class index {child}", declaration.name),
            )]);
        };
        let child_is_nat = child_declaration.name == "Nat"
            && child_declaration.type_params.is_empty()
            && child_declaration.type_bounds.is_empty()
            && child_declaration.proof_reuse.is_none()
            && child_declaration.fields.len() == 1
            && child_declaration.fields[0].name == "limbs"
            && child_declaration.fields[0].ty == Ty::array(Ty::Int(IntTy::U32))
            && !child_declaration.fields[0].must_consume
            && child_declaration.methods.is_empty()
            && matches!(child_declaration.deinit.as_deref(), Some([]));
        if !child_is_nat {
            return Err(vec![diag(
                "backend.class_unsupported",
                "Integer magnitude does not use the exact native Nat shape",
                span,
                format!(
                    "`{}.mag` names `{}`",
                    declaration.name, child_declaration.name
                ),
            )]);
        }
    }
    Ok(declaration)
}

fn require_initializer_parameter(
    program: &Program,
    _root_span_end: usize,
    ty: Ty,
    span: Span,
) -> Result<(), Vec<BackendError>> {
    match ty {
        ref borrowed
            if borrowed.as_array_borrow() == Some((&Ty::Int(IntTy::U32), Mutability::Shared)) =>
        {
            Ok(())
        }
        Ty::Int(integer) if !matches!(integer, IntTy::TParam(_)) => Ok(()),
        Ty::Class(class) => {
            let declaration = require_fixed_class(program, class, span, "initializer parameter")?;
            if declaration.name == "Nat" {
                Ok(())
            } else {
                Err(vec![diag(
                    "backend.class_unsupported",
                    "initializer owned parameter is outside the exact native take ABI",
                    span,
                    "the backend lowers only owned `Nat` initializer parameters",
                )])
            }
        }
        _ => Err(vec![unsupported(
            span,
            format!(
                "initializer parameter type `{}` is outside the exact native constructor ABI",
                ty.name()
            ),
        )]),
    }
}

fn require_scalar_owner_method_parameter(
    program: &Program,
    root_span_end: usize,
    ty: Ty,
    span: Span,
    role: &str,
) -> Result<(), Vec<BackendError>> {
    if is_concrete_scalar(&ty) {
        return Ok(());
    }
    if let Ty::Class(class) = ty {
        require_exact_scalar_owner_class(program, class, root_span_end, span, role)?;
        return Ok(());
    }
    Err(vec![diag(
        "backend.class_unsupported",
        "method parameter is outside the exact scalar-owner ABI",
        span,
        format!(
            "{role} has type `{}`; only concrete scalars and owned exact scalar-owner classes cross this internal method boundary",
            ty.name()
        ),
    )])
}

fn require_scalar_owner_method_result(
    program: &Program,
    root_span_end: usize,
    ty: Ty,
    span: Span,
) -> Result<(), Vec<BackendError>> {
    if ty == Ty::Unit || is_concrete_scalar(&ty) {
        return Ok(());
    }
    if let Ty::Class(class) = ty {
        require_exact_scalar_owner_class(program, class, root_span_end, span, "method result")?;
        return Ok(());
    }
    Err(vec![diag(
        "backend.class_unsupported",
        "method result is outside the exact scalar-owner ABI",
        span,
        format!(
            "method result `{}` must be a concrete scalar, unit, or an exact scalar-owner class",
            ty.name()
        ),
    )])
}

fn validate_fixed_class_initializer(
    program: &Program,
    class: usize,
    expression: &Expr,
    root_span_end: usize,
    locals: &mut ValidationLocals,
) -> Result<(), Vec<BackendError>> {
    let declaration = require_native_owner_class(
        program,
        class,
        root_span_end,
        expression.span,
        "class local initializer",
    )?;
    let scalar_owner = require_exact_scalar_owner_class(
        program,
        class,
        root_span_end,
        expression.span,
        "class local initializer",
    )
    .is_ok();
    require_expr_type(expression, Ty::Class(class), "class constructor result")?;
    match &expression.kind {
        ExprKind::CtorCall {
            class: class_name,
            type_args,
            init,
            args,
            ..
        } => {
            if !type_args.is_empty() || *class_name != declaration.name {
                return Err(vec![diag(
                    "backend.class_unsupported",
                    "class constructor identity is incoherent",
                    expression.span,
                    format!(
                        "checked class `{}` does not match constructor spelling `{class_name}` or retains type arguments",
                        declaration.name
                    ),
                )]);
            }
            let Some(initializer) = declaration
                .inits
                .iter()
                .find(|candidate| candidate.name == *init)
            else {
                return Err(vec![diag(
                    "backend.constructor_missing",
                    "LLVM lowering could not resolve a constructor",
                    expression.span,
                    format!("class `{class_name}` has no initializer `{init}`"),
                )]);
            };
            if args.len() != initializer.params.len() {
                return Err(vec![unsupported(
                    expression.span,
                    format!(
                        "constructor `{class_name}::{init}` has {} argument(s), expected {}",
                        args.len(),
                        initializer.params.len()
                    ),
                )]);
            }
            validate_moving_arguments(
                program,
                &initializer.params,
                args,
                root_span_end,
                locals,
                true,
                "constructor",
            )
        }
        ExprKind::Call {
            callee,
            type_args,
            args,
            ..
        } => {
            if scalar_owner {
                return Err(vec![diag(
                    "backend.class_unsupported",
                    "scalar-owner class cannot cross the free-function return ABI",
                    expression.span,
                    format!(
                        "bind `{}` only from its constructor, an exact scalar-owner method result, or a named owner move",
                        declaration.name
                    ),
                )]);
            }
            if !type_args.is_empty() {
                return Err(vec![unsupported(
                    expression.span,
                    format!("class-returning call to `{callee}` retains type arguments"),
                )]);
            }
            let Some(function) = program.fns.iter().find(|function| function.name == *callee)
            else {
                return Err(vec![diag(
                    "backend.call_missing",
                    "LLVM lowering could not resolve a class-returning call",
                    expression.span,
                    format!("no checked function named `{callee}`"),
                )]);
            };
            if function.extern_info.is_some() || function.ret != Ty::Class(class) {
                return Err(vec![diag(
                    "backend.class_unsupported",
                    "class-returning call is outside the fixed-owner class shapes the LLVM backend lowers",
                    expression.span,
                    format!("`{callee}` does not return the checked fixed-owner class"),
                )]);
            }
            validate_moving_arguments(
                program,
                &function.params,
                args,
                root_span_end,
                locals,
                false,
                "class-returning call",
            )
        }
        ExprKind::MethodCall { .. } if scalar_owner => {
            validate_native_method_call(program, expression, root_span_end, locals)
        }
        ExprKind::Var(source) => {
            let Some(local) = locals.get(source) else {
                return Err(vec![unsupported(
                    expression.span,
                    format!("class move names unknown or out-of-scope local `{source}`"),
                )]);
            };
            if local.ty != Ty::Class(class) {
                return Err(vec![diag(
                    "backend.class_unsupported",
                    "class move source has the wrong nominal type",
                    expression.span,
                    format!("`{source}` has checked type `{}`", local.ty.name()),
                )]);
            }
            locals.require_live_class(source, expression.span, "class move")?;
            locals.mark_class_moved(source);
            Ok(())
        }
        _ => Err(vec![diag(
            "backend.class_unsupported",
            "class value source is outside the fixed-owner class shapes the LLVM backend lowers",
            expression.span,
            "expected a direct constructor, admitted destination-passing call, or named owner move",
        )]),
    }
}

fn validate_moving_arguments(
    program: &Program,
    params: &[crate::ast::Param],
    args: &[Expr],
    root_span_end: usize,
    locals: &mut ValidationLocals,
    initializer_parameters: bool,
    role: &str,
) -> Result<(), Vec<BackendError>> {
    if args.len() != params.len() {
        return Err(vec![unsupported(
            args.first()
                .map_or(Span::new(0, 0), |argument| argument.span),
            format!(
                "{role} has {} argument(s), expected {}",
                args.len(),
                params.len()
            ),
        )]);
    }
    validate_owned_argument_aliases(args, params, locals)?;
    for (argument, parameter) in args.iter().zip(params) {
        if initializer_parameters {
            require_initializer_parameter(
                program,
                root_span_end,
                parameter.ty.clone(),
                parameter.span,
            )?;
        } else {
            require_parameter_value(
                program,
                root_span_end,
                parameter.ty.clone(),
                parameter.span,
                "class-returning function parameter",
            )?;
        }
        match &parameter.ty {
            Ty::Class(class) => {
                validate_fixed_class_initializer(program, *class, argument, root_span_end, locals)?;
            }
            class_borrow if class_borrow.as_class_borrow().is_some() => {
                validate_class_borrow_argument(program, argument, parameter.ty.clone(), locals)?;
            }
            array_borrow if array_borrow.as_array_borrow().is_some() => {
                validate_native_array_borrow_argument(
                    program,
                    argument,
                    parameter.ty.clone(),
                    locals,
                )?
            }
            _ => {
                validate_expr(program, argument, root_span_end, locals)?;
                require_expr_type(argument, parameter.ty.clone(), "moving call argument")?;
            }
        }
    }
    validate_borrow_aliases(args, params, locals)
}

fn validate_owned_argument_aliases(
    args: &[Expr],
    params: &[crate::ast::Param],
    locals: &ValidationLocals,
) -> Result<(), Vec<BackendError>> {
    for (owned_index, (owned_argument, owned_parameter)) in args.iter().zip(params).enumerate() {
        if !matches!(owned_parameter.ty, Ty::Class(_)) {
            continue;
        }
        let ExprKind::Var(owner) = &owned_argument.kind else {
            continue;
        };
        for (borrow_index, borrow_argument) in args.iter().enumerate() {
            if owned_index == borrow_index {
                continue;
            }
            let mut places = Vec::new();
            collect_argument_borrow_places(borrow_argument, locals, &mut places);
            if places.iter().any(|(place, _, _)| place == owner) {
                return Err(vec![diag(
                    "backend.class_unsupported",
                    "owned class argument overlaps a borrow in the same call",
                    borrow_argument.span,
                    format!(
                        "`{owner}` is both borrowed and moved by value; moving it would invalidate the callee's borrow"
                    ),
                )]);
            }
        }
    }
    Ok(())
}

fn validate_call_arguments(
    program: &Program,
    function: &Fn,
    args: &[Expr],
    root_span_end: usize,
    locals: &mut ValidationLocals,
) -> Result<(), Vec<BackendError>> {
    if args.len() != function.params.len() {
        return Err(vec![unsupported(
            function.name_span,
            format!(
                "call to `{}` has {} argument(s), but its checked signature has {}",
                function.name,
                args.len(),
                function.params.len()
            ),
        )]);
    }
    for (argument, parameter) in args.iter().zip(&function.params) {
        if parameter.ty.as_class_borrow().is_some() {
            validate_class_borrow_argument(program, argument, parameter.ty.clone(), locals)?;
        } else if parameter.ty.as_array_borrow().is_some() {
            validate_native_array_borrow_argument(program, argument, parameter.ty.clone(), locals)?;
        } else {
            validate_expr(program, argument, root_span_end, locals)?;
            require_expr_type(argument, parameter.ty.clone(), "call argument")?;
        }
    }
    validate_borrow_aliases(args, &function.params, locals)
}

fn validate_initializer_field_assign(
    program: &Program,
    field: &str,
    field_span: Span,
    value: &Expr,
    root_span_end: usize,
    locals: &mut ValidationLocals,
    initializer: Option<&mut InitializerValidation>,
    method: Option<(usize, SelfKind)>,
) -> Result<(), Vec<BackendError>> {
    let class = initializer
        .as_ref()
        .map(|context| context.class)
        .or_else(|| method.map(|m| m.0));
    let Some(class) = class else {
        return Err(vec![unsupported(
            field_span,
            "class field assignment is outside a supported member",
        )]);
    };
    let declaration = require_native_owner_class(
        program,
        class,
        root_span_end,
        field_span,
        "member field assignment",
    )?;
    let Some((field_index, declaration_field)) = declaration
        .fields
        .iter()
        .enumerate()
        .find(|(_, declaration_field)| declaration_field.name == field)
    else {
        return Err(vec![diag(
            "backend.class_unsupported",
            "fixed-owner class field assignment names an unknown field",
            field_span,
            format!("class `{}` has no field `{field}`", declaration.name),
        )]);
    };
    if let Some(initializer) = initializer {
        if initializer.fields_initialized[field_index] {
            return Err(vec![diag(
                "backend.class_unsupported",
                "fixed-owner class field is initialized more than once",
                field_span,
                format!(
                    "field `{}.{field}` was already initialized",
                    declaration.name
                ),
            )]);
        }
        match &declaration_field.ty {
            Ty::Array(element) if element.as_ref() == &Ty::Int(IntTy::U32) => {
                validate_fresh_u32_array_initializer(program, value, root_span_end, locals)?;
            }
            Ty::Class(child) => {
                validate_fixed_class_initializer(program, *child, value, root_span_end, locals)?;
            }
            Ty::Int(integer) if !matches!(integer, IntTy::TParam(_)) => {
                validate_expr(program, value, root_span_end, locals)?;
                require_expr_type(
                    value,
                    declaration_field.ty.clone(),
                    "initializer scalar field",
                )?;
            }
            other => {
                return Err(vec![diag(
                    "backend.class_unsupported",
                    "field type is outside the exact native class layout",
                    field_span,
                    format!("`{}.{field}` has type `{}`", declaration.name, other.name()),
                )]);
            }
        }
        initializer.fields_initialized[field_index] = true;
        return Ok(());
    }
    let Some((_, SelfKind::Mut)) = method else {
        return Err(vec![diag(
            "backend.class_unsupported",
            "shared method cannot assign a class field",
            field_span,
            "a lowered method mutates a field only through `&mut self`",
        )]);
    };
    let Ty::Int(integer) = declaration_field.ty else {
        return Err(vec![diag(
            "backend.class_unsupported",
            "method field replacement is outside the exact native scalar surface",
            field_span,
            "a lowered method may assign only a concrete integer field",
        )]);
    };
    require_concrete_integer(integer, field_span, "method scalar field")?;
    validate_expr(program, value, root_span_end, locals)?;
    require_expr_type(
        value,
        declaration_field.ty.clone(),
        "method scalar field assignment",
    )
}

fn validate_initializer_field_store(
    program: &Program,
    field: &str,
    field_span: Span,
    index: &Expr,
    value: &Expr,
    root_span_end: usize,
    locals: &mut ValidationLocals,
    initializer: Option<&InitializerValidation>,
) -> Result<(), Vec<BackendError>> {
    let Some(initializer) = initializer else {
        return Err(vec![unsupported(
            field_span,
            "class field store is outside a supported initializer",
        )]);
    };
    let declaration = require_fixed_class(
        program,
        initializer.class,
        field_span,
        "initializer field store",
    )?;
    let Some((field_index, declaration_field)) = declaration
        .fields
        .iter()
        .enumerate()
        .find(|(_, declaration_field)| declaration_field.name == field)
    else {
        return Err(vec![diag(
            "backend.class_unsupported",
            "fixed-owner class field store names an unknown field",
            field_span,
            format!("class `{}` has no field `{field}`", declaration.name),
        )]);
    };
    if declaration_field.ty != Ty::array(Ty::Int(IntTy::U32))
        || !initializer.fields_initialized[field_index]
    {
        return Err(vec![diag(
            "backend.class_unsupported",
            "fixed-owner class field store has no initialized destination",
            field_span,
            format!(
                "field `{field}` is not initialized in `{}`",
                declaration.name
            ),
        )]);
    }
    validate_expr(program, index, root_span_end, locals)?;
    require_expr_type(index, Ty::Int(IntTy::U64), "class array-field store index")?;
    validate_expr(program, value, root_span_end, locals)?;
    require_expr_type(value, Ty::Int(IntTy::U32), "class array-field store value")
}

fn validate_fixed_class_field_base(
    program: &Program,
    locals: &ValidationLocals,
    object: &str,
    field: &str,
    span: Span,
) -> Result<(usize, usize, Ty), Vec<BackendError>> {
    let Some(local) = locals.get(object) else {
        return Err(vec![unsupported(
            span,
            format!("class field access names unknown or out-of-scope local `{object}`"),
        )]);
    };
    if matches!(local.ty, Ty::Class(_)) {
        locals.require_live_class(object, span, "class field access")?;
    }
    let class = match local.ty.class_index() {
        Some(class) => class,
        None => {
            return Err(vec![diag(
                "backend.class_unsupported",
                "class field access has a non-class base",
                span,
                format!("`{object}` has type `{}`", local.ty.name()),
            )]);
        }
    };
    let declaration = require_fixed_class(program, class, span, "class field access")?;
    let Some((field_index, declaration_field)) = declaration
        .fields
        .iter()
        .enumerate()
        .find(|(_, declaration_field)| declaration_field.name == field)
    else {
        return Err(vec![diag(
            "backend.class_unsupported",
            "class field access names an unsupported field",
            span,
            format!("class `{}` has no native field `{field}`", declaration.name),
        )]);
    };
    Ok((class, field_index, declaration_field.ty.clone()))
}

fn validate_native_owner_class_field_base(
    program: &Program,
    root_span_end: usize,
    locals: &ValidationLocals,
    object: &str,
    field: &str,
    span: Span,
) -> Result<(usize, usize, Ty), Vec<BackendError>> {
    let Some(local) = locals.get(object) else {
        return Err(vec![unsupported(
            span,
            format!("class field access names unknown or out-of-scope local `{object}`"),
        )]);
    };
    if matches!(local.ty, Ty::Class(_)) {
        locals.require_live_class(object, span, "class field access")?;
    }
    let Some(class) = local.ty.class_index() else {
        return Err(vec![diag(
            "backend.class_unsupported",
            "class field access has a non-class base",
            span,
            format!("`{object}` has type `{}`", local.ty.name()),
        )]);
    };
    let declaration =
        require_native_owner_class(program, class, root_span_end, span, "class field access")?;
    let Some((field_index, declaration_field)) = declaration
        .fields
        .iter()
        .enumerate()
        .find(|(_, declaration_field)| declaration_field.name == field)
    else {
        return Err(vec![diag(
            "backend.class_unsupported",
            "class field access names an unsupported field",
            span,
            format!("class `{}` has no native field `{field}`", declaration.name),
        )]);
    };
    Ok((class, field_index, declaration_field.ty.clone()))
}

fn affine_bool_option_ty() -> Ty {
    Ty::affine_array_option(Ty::Bool)
}

fn is_affine_bool_option(ty: &Ty) -> bool {
    *ty == affine_bool_option_ty()
}

fn reject_named_affine_option(
    locals: &ValidationLocals,
    name: &str,
    span: Span,
    role: &str,
) -> Result<(), Vec<BackendError>> {
    if let Some(local) = locals.get(name) {
        if local.ty.is_affine_option() {
            return Err(vec![affine_option_unsupported(span, role, local.ty)]);
        }
    }
    Ok(())
}

fn validate_affine_bool_option_decl(
    program: &Program,
    name: &str,
    ty: Ty,
    mutable: bool,
    init: Option<&Expr>,
    root_span_end: usize,
    locals: &mut ValidationLocals,
    span: Span,
) -> Result<(), Vec<BackendError>> {
    if !is_affine_bool_option(&ty.clone()) {
        return Err(vec![affine_option_unsupported(
            span,
            &format!("declaration `{name}`"),
            ty,
        )]);
    }
    if !mutable {
        return Err(vec![diag(
            "backend.affine_option_unsupported",
            "affine option is outside the locals the LLVM backend lowers",
            span,
            format!("affine option local `{name}` must be mutable"),
        )]);
    }
    let Some(init) = init else {
        return Err(vec![diag(
            "backend.affine_option_unsupported",
            "affine option is outside the locals the LLVM backend lowers",
            span,
            format!(
                "affine option local `{name}` must be initialized by `none` or `some(alloc_array<bool>(...))`"
            ),
        )]);
    };
    require_expr_type(init, affine_bool_option_ty(), "affine-option initializer")?;
    match &init.kind {
        ExprKind::NoneE => Ok(()),
        ExprKind::SomeE(payload) => {
            require_expr_type(payload, Ty::array(Ty::Bool), "affine-option payload")?;
            let ExprKind::AllocArray { elem, len, init } = &payload.kind else {
                return Err(vec![affine_option_initializer_unsupported(init.span, name)]);
            };
            if *elem != Ty::Bool {
                return Err(vec![affine_option_initializer_unsupported(init.span, name)]);
            }
            validate_expr(program, len, root_span_end, locals)?;
            require_expr_type(len, Ty::Int(IntTy::U64), "Boolean array allocation length")?;
            validate_bool_expr(
                program,
                init,
                "Boolean array allocation initializer",
                root_span_end,
                locals,
            )
        }
        _ => Err(vec![affine_option_initializer_unsupported(init.span, name)]),
    }
}

fn validate_affine_option_take(
    expression: &Expr,
    destination: &str,
    option: &str,
    option_span: Span,
    locals: &ValidationLocals,
) -> Result<(), Vec<BackendError>> {
    require_expr_type(expression, Ty::array(Ty::Bool), "affine-option take result")?;
    if destination == option {
        return Err(vec![diag(
            "backend.affine_option_unsupported",
            "affine option is outside the locals the LLVM backend lowers",
            expression.span,
            format!("`.take` destination `{destination}` cannot also be its source"),
        )]);
    }
    if locals.declared.contains(destination) {
        return Err(vec![unsupported(
            expression.span,
            format!("duplicate LLVM local `{destination}` escaped checking"),
        )]);
    }
    let Some(source) = locals.get(option) else {
        return Err(vec![diag(
            "backend.affine_option_unsupported",
            "affine option is outside the locals the LLVM backend lowers",
            option_span,
            format!("`.take` names unknown or out-of-scope local `{option}`"),
        )]);
    };
    if !is_affine_bool_option(&source.ty) {
        return if source.ty.is_affine_option() {
            Err(vec![affine_option_unsupported(
                option_span,
                &format!("`.take` source `{option}`"),
                source.ty,
            )])
        } else {
            Err(vec![diag(
                "backend.affine_option_unsupported",
                "affine option is outside the locals the LLVM backend lowers",
                option_span,
                format!(
                    "`.take` source `{option}` has type `{}`; expected `option<[bool]>`",
                    source.ty.name()
                ),
            )])
        };
    }
    if !source.mutable {
        return Err(vec![diag(
            "backend.affine_option_unsupported",
            "affine option is outside the locals the LLVM backend lowers",
            option_span,
            format!("`.take` source `{option}` must be mutable"),
        )]);
    }
    Ok(())
}

fn validate_fresh_bool_array_initializer(
    program: &Program,
    expression: &Expr,
    root_span_end: usize,
    locals: &mut ValidationLocals,
    local: &str,
    allow_take: bool,
) -> Result<(), Vec<BackendError>> {
    let expected = Ty::array(Ty::Bool);
    require_expr_type(expression, expected, "owned Boolean-array initializer")?;
    match &expression.kind {
        ExprKind::ArrayLit(elements) => {
            if elements.len() as u64 > ARRAY_CAPACITY {
                return Err(vec![unsupported(
                    expression.span,
                    format!(
                        "Boolean array literal has {} elements; the native allocation cap is {ARRAY_CAPACITY}",
                        elements.len()
                    ),
                )]);
            }
            for element in elements {
                validate_bool_expr(
                    program,
                    element,
                    "Boolean array literal element",
                    root_span_end,
                    locals,
                )?;
            }
            Ok(())
        }
        ExprKind::AllocArray { elem, len, init } if *elem == Ty::Bool => {
            validate_expr(program, len, root_span_end, locals)?;
            require_expr_type(len, Ty::Int(IntTy::U64), "Boolean array allocation length")?;
            validate_bool_expr(
                program,
                init,
                "Boolean array allocation initializer",
                root_span_end,
                locals,
            )
        }
        ExprKind::OptTake {
            option,
            option_span,
        } if allow_take => {
            validate_affine_option_take(expression, local, option, *option_span, locals)
        }
        ExprKind::OptTake { option, .. } => Err(vec![affine_option_take_position(
            expression.span,
            option,
            "owned Boolean-array initializer",
        )]),
        _ => Err(vec![unsupported(
            expression.span,
            "owned Boolean-array local must be initialized by a fresh literal or `alloc_array<bool>`",
        )]),
    }
}

fn validate_fresh_u32_array_initializer(
    program: &Program,
    expression: &Expr,
    root_span_end: usize,
    locals: &mut ValidationLocals,
) -> Result<(), Vec<BackendError>> {
    let expected = Ty::array(Ty::Int(IntTy::U32));
    require_expr_type(expression, expected, "owned `u32`-array initializer")?;
    match &expression.kind {
        ExprKind::ArrayLit(elements) => {
            if elements.len() as u64 > ARRAY_CAPACITY {
                return Err(vec![unsupported(
                    expression.span,
                    format!(
                        "`u32` array literal has {} elements; the native allocation cap is {ARRAY_CAPACITY}",
                        elements.len()
                    ),
                )]);
            }
            for element in elements {
                validate_expr(program, element, root_span_end, locals)?;
                require_expr_type(element, Ty::Int(IntTy::U32), "`u32` array literal element")?;
            }
            Ok(())
        }
        ExprKind::AllocArray { elem, len, init } if *elem == Ty::Int(IntTy::U32) => {
            validate_expr(program, len, root_span_end, locals)?;
            require_expr_type(len, Ty::Int(IntTy::U64), "`u32` array allocation length")?;
            validate_expr(program, init, root_span_end, locals)?;
            require_expr_type(
                init,
                Ty::Int(IntTy::U32),
                "`u32` array allocation initializer",
            )
        }
        _ => Err(vec![unsupported(
            expression.span,
            "owned `u32` array local must be initialized by a fresh literal or `alloc_array<u32>`",
        )]),
    }
}

fn validate_native_array_store(
    program: &Program,
    array: &str,
    array_span: Span,
    index: &Expr,
    value: &Expr,
    root_span_end: usize,
    locals: &mut ValidationLocals,
) -> Result<(), Vec<BackendError>> {
    let Some(local) = locals.get(array) else {
        return Err(vec![unsupported(
            array_span,
            format!("array store names unknown or out-of-scope local `{array}`"),
        )]);
    };
    if !is_native_array(&local.ty) {
        return Err(vec![unsupported(
            array_span,
            format!(
                "array store target `{array}` has unsupported LLVM type `{}`",
                local.ty.name()
            ),
        )]);
    }
    // Writing needs the exclusive right to the storage, whichever way the
    // place is bound: a `mut` owner has it, a unique borrow has it, and a
    // shared borrow's whole promise is that it does not.
    match local.ty.binding_mode() {
        BindingMode::Owned if !local.mutable => {
            return Err(vec![unsupported(
                array_span,
                format!("array store targets immutable owned array `{array}`"),
            )]);
        }
        BindingMode::Shared => {
            return Err(vec![unsupported(
                array_span,
                format!("array store targets shared borrow `{array}`"),
            )]);
        }
        BindingMode::Owned | BindingMode::Mut => {}
    }
    validate_expr(program, index, root_span_end, locals)?;
    require_expr_type(index, Ty::Int(IntTy::U64), "array store index")?;
    if local.ty.is_bool_array() {
        validate_bool_expr(
            program,
            value,
            "Boolean array store value",
            root_span_end,
            locals,
        )
    } else {
        validate_expr(program, value, root_span_end, locals)?;
        require_expr_type(value, Ty::Int(IntTy::U32), "`u32` array store value")
    }
}

fn validate_native_array_borrow_argument(
    program: &Program,
    argument: &Expr,
    expected: Ty,
    locals: &ValidationLocals,
) -> Result<(), Vec<BackendError>> {
    let Some((element, _)) = expected.as_array() else {
        return Err(vec![unsupported(
            argument.span,
            "array borrow parameter has no checked element type",
        )]);
    };
    let element = element.clone();
    let Some((_, expected_mutability)) = expected.as_array_borrow() else {
        return Err(vec![unsupported(
            argument.span,
            "owned arrays cannot cross an LLVM call boundary",
        )]);
    };
    let element_name = element.name();
    require_expr_type(argument, expected, "array borrow argument")?;
    let ExprKind::Borrow {
        array,
        field,
        mutable,
    } = &argument.kind
    else {
        return Err(vec![unsupported(
            argument.span,
            format!("borrowed `{element_name}` array parameters require an explicit named borrow"),
        )]);
    };
    let requested = if *mutable {
        Mutability::Mut
    } else {
        Mutability::Shared
    };
    if requested != expected_mutability {
        return Err(vec![unsupported(
            argument.span,
            "borrow syntax mutability does not match the checked call parameter",
        )]);
    }
    let Some(source) = locals.get(array) else {
        return Err(vec![unsupported(
            argument.span,
            format!("array borrow names unknown or out-of-scope local `{array}`"),
        )]);
    };
    if let Some(field) = field {
        if *mutable {
            return Err(vec![diag(
                "backend.class_unsupported",
                "mutable class-field borrow is outside the concrete `Integer` surface the LLVM backend lowers",
                argument.span,
                "the backend lowers shared `u32` field borrows only",
            )]);
        }
        let (_, _, field_ty) =
            validate_fixed_class_field_base(program, locals, array, field, argument.span)?;
        if element != Ty::Int(IntTy::U32) || field_ty != Ty::array(Ty::Int(IntTy::U32)) {
            return Err(vec![diag(
                "backend.class_unsupported",
                "array field borrow has the wrong native type",
                argument.span,
                format!("`{array}.{field}` has type `{}`", field_ty.name()),
            )]);
        }
        return Ok(());
    }
    let Some((source_element, source_mutability)) = source.ty.as_array() else {
        return Err(vec![unsupported(
            argument.span,
            format!("array borrow source `{array}` is not a native array"),
        )]);
    };
    if source_element != &element {
        return Err(vec![unsupported(
            argument.span,
            format!(
                "array borrow source `{array}` holds `{}` elements, not `{element_name}`",
                source_element.name()
            ),
        )]);
    }
    if *mutable
        && (source_mutability == BindingMode::Shared
            || (source_mutability == BindingMode::Owned && !source.mutable))
    {
        return Err(vec![unsupported(
            argument.span,
            format!("cannot mutably borrow `{array}` through a non-mutable array place"),
        )]);
    }
    Ok(())
}

fn validate_class_borrow_argument(
    program: &Program,
    argument: &Expr,
    expected: Ty,
    locals: &ValidationLocals,
) -> Result<(), Vec<BackendError>> {
    let Some((class, expected_mutability)) = expected.as_class_borrow() else {
        return Err(vec![diag(
            "backend.class_unsupported",
            "class borrow is outside the fixed-owner class shapes the LLVM backend lowers",
            argument.span,
            format!(
                "class borrow parameter `{}` has no native reference representation",
                expected.name()
            ),
        )]);
    };
    require_fixed_class(program, class, argument.span, "class borrow parameter")?;
    require_expr_type(argument, expected.clone(), "class borrow argument")?;
    if let ExprKind::Var(name) = &argument.kind {
        let Some(source) = locals.get(name) else {
            return Err(vec![unsupported(
                argument.span,
                format!("class reference names unknown local `{name}`"),
            )]);
        };
        if !matches!(source.ty.as_class_borrow(), Some((source_class, source_mutability))
            if source_class == class
                && (source_mutability == expected_mutability
                    || (source_mutability == Mutability::Mut
                        && expected_mutability == Mutability::Shared)))
        {
            return Err(vec![diag(
                "backend.class_unsupported",
                "forwarded class reference has the wrong nominal type or mutability",
                argument.span,
                format!("`{name}` has type `{}`", source.ty.name()),
            )]);
        }
        return Ok(());
    }
    let ExprKind::Borrow {
        array,
        field,
        mutable,
    } = &argument.kind
    else {
        return Err(vec![diag(
            "backend.class_unsupported",
            "class borrow argument is outside the fixed-owner class shapes the LLVM backend lowers",
            argument.span,
            "a class parameter requires an explicit named borrow with matching mutability",
        )]);
    };
    let Some(source) = locals.get(array) else {
        return Err(vec![unsupported(
            argument.span,
            format!("class borrow names unknown or out-of-scope local `{array}`"),
        )]);
    };
    if matches!(source.ty, Ty::Class(_)) {
        locals.require_live_class(array, argument.span, "class borrow")?;
    }
    let requested_mutability = if *mutable {
        Mutability::Mut
    } else {
        Mutability::Shared
    };
    if requested_mutability != expected_mutability {
        return Err(vec![diag(
            "backend.class_unsupported",
            "class borrow syntax has the wrong mutability",
            argument.span,
            format!("expected `{}`", expected.name()),
        )]);
    }
    if let Some(field) = field {
        if *mutable {
            return Err(vec![diag(
                "backend.class_unsupported",
                "mutable class-field borrow is outside the concrete `Integer` surface the LLVM backend lowers",
                argument.span,
                "borrow the whole Integer mutably and mutate through its method",
            )]);
        }
        let (_, _, field_ty) =
            validate_fixed_class_field_base(program, locals, array, field, argument.span)?;
        if field_ty != Ty::Class(class) {
            return Err(vec![diag(
                "backend.class_unsupported",
                "class field borrow has the wrong nominal type",
                argument.span,
                format!("`{array}.{field}` has type `{}`", field_ty.name()),
            )]);
        }
        return Ok(());
    }
    if source.ty.class_index() != Some(class) {
        return Err(vec![diag(
            "backend.class_unsupported",
            "class borrow source has the wrong nominal type",
            argument.span,
            format!(
                "`{array}` has type `{}`; expected `{}` or its owner",
                source.ty.name(),
                expected.name()
            ),
        )]);
    }
    let mutable_source = match source.ty.as_class_borrow() {
        Some((_, mutability)) => mutability == Mutability::Mut,
        None => matches!(source.ty, Ty::Class(_)) && source.mutable,
    };
    if expected_mutability == Mutability::Mut && !mutable_source {
        return Err(vec![diag(
            "backend.class_unsupported",
            "mutable class borrow needs a mutable owner or reference",
            argument.span,
            format!("`{array}` cannot be borrowed mutably"),
        )]);
    }
    Ok(())
}

fn validate_borrow_aliases(
    args: &[Expr],
    params: &[crate::ast::Param],
    locals: &ValidationLocals,
) -> Result<(), Vec<BackendError>> {
    let mut prior_places: Vec<(String, bool, Span)> = Vec::new();
    for (argument, parameter) in args.iter().zip(params) {
        let mut places = Vec::new();
        collect_argument_borrow_places(argument, locals, &mut places);
        if matches!(parameter.ty.as_unique_borrow(), Some(Ty::Class(_))) {
            if let Some((_, mutable, _)) = places.first_mut() {
                *mutable = true;
            }
        }
        for (place, mutable, span) in &places {
            if let Some((_, _, prior_span)) = prior_places
                .iter()
                .find(|(prior, prior_mutable, _)| prior == place && (*prior_mutable || *mutable))
            {
                return Err(vec![unsupported(
                    *span,
                    format!(
                        "call aliases `{place}` through mutable and overlapping borrows during argument evaluation (first borrow at byte {})",
                        prior_span.start
                    ),
                )]);
            }
        }
        prior_places.extend(places);
    }
    Ok(())
}

fn collect_argument_borrow_places(
    expression: &Expr,
    locals: &ValidationLocals,
    places: &mut Vec<(String, bool, Span)>,
) {
    match &expression.kind {
        ExprKind::Borrow { array, mutable, .. } => {
            places.push((array.clone(), *mutable, expression.span));
        }
        ExprKind::MethodCall { recv, args, .. } => {
            // The only admitted native method has a mutable receiver. Keeping
            // that receiver visible here also fences a retained outer borrow
            // from overlapping a nested method evaluation.
            places.push((recv.clone(), true, expression.span));
            for argument in args {
                collect_argument_borrow_places(argument, locals, places);
            }
        }
        ExprKind::Call { args, .. }
        | ExprKind::RawOp { args, .. }
        | ExprKind::DeviceOp { args, .. }
        | ExprKind::ResOp { args, .. }
        | ExprKind::SlotOp { args, .. }
        | ExprKind::TraitCall { args, .. }
        | ExprKind::CtorCall { args, .. }
        | ExprKind::RecordLit { args, .. }
        | ExprKind::ArrayLit(args) => {
            for argument in args {
                collect_argument_borrow_places(argument, locals, places);
            }
        }
        ExprKind::Unary { operand, .. }
        | ExprKind::Widen { arg: operand, .. }
        | ExprKind::Narrow { arg: operand, .. }
        | ExprKind::IsSome { operand }
        | ExprKind::OptValue { operand }
        | ExprKind::SomeE(operand) => collect_argument_borrow_places(operand, locals, places),
        ExprKind::Binary { lhs, rhs, .. } => {
            collect_argument_borrow_places(lhs, locals, places);
            collect_argument_borrow_places(rhs, locals, places);
        }
        ExprKind::Index { array, index, .. } => {
            places.push((array.clone(), false, expression.span));
            collect_argument_borrow_places(index, locals, places);
        }
        ExprKind::Len { array } => {
            places.push((array.clone(), false, expression.span));
        }
        ExprKind::SelfFieldIndex { index, .. } => {
            places.push(("self".into(), false, expression.span));
            collect_argument_borrow_places(index, locals, places);
        }
        ExprKind::SelfField { .. } | ExprKind::SelfFieldLen { .. } => {
            places.push(("self".into(), false, expression.span));
        }
        ExprKind::ClassFieldIndex { obj, index, .. } => {
            places.push((obj.clone(), false, expression.span));
            collect_argument_borrow_places(index, locals, places);
        }
        ExprKind::ClassField { obj, .. } | ExprKind::ClassFieldLen { obj, .. } => {
            places.push((obj.clone(), false, expression.span));
        }
        ExprKind::AllocArray { len, init, .. } => {
            collect_argument_borrow_places(len, locals, places);
            collect_argument_borrow_places(init, locals, places);
        }
        ExprKind::Var(name) => {
            // A class place aliases; a shared borrow of one aliases without
            // writing. Anything else is a value the call cannot write through.
            if let Some(ty) = locals.get(name).map(|local| local.ty) {
                match (ty.class_index(), ty.binding_mode()) {
                    (Some(_), BindingMode::Owned | BindingMode::Mut) => {
                        places.push((name.clone(), true, expression.span));
                    }
                    (Some(_), BindingMode::Shared) => {
                        places.push((name.clone(), false, expression.span));
                    }
                    (None, _) => {}
                }
            }
        }
        ExprKind::IntLit(_)
        | ExprKind::BoolLit(_)
        | ExprKind::NoneE
        | ExprKind::RecordField { .. }
        | ExprKind::OptTake { .. } => {}
    }
}

fn validate_native_method_call(
    program: &Program,
    expression: &Expr,
    root_span_end: usize,
    locals: &mut ValidationLocals,
) -> Result<(), Vec<BackendError>> {
    let ExprKind::MethodCall {
        recv: receiver,
        recv_span: receiver_span,
        method: method_name,
        args,
        ..
    } = &expression.kind
    else {
        return Err(vec![diag(
            "internal.control_plan_invalid",
            "native method validator received a non-method expression",
            expression.span,
            "the retained expression kind no longer matches its call site",
        )]);
    };
    let Some(local) = locals.get(receiver) else {
        return Err(vec![unsupported(
            *receiver_span,
            format!("method receiver names unknown local `{receiver}`"),
        )]);
    };
    if matches!(local.ty, Ty::Class(_)) {
        locals.require_live_class(receiver, *receiver_span, "method receiver")?;
    }
    let Some(class) = local.ty.class_index() else {
        return Err(vec![diag(
            "backend.class_unsupported",
            "native method receiver is not a class",
            *receiver_span,
            format!("`{receiver}` has type `{}`", local.ty.name()),
        )]);
    };
    let declaration = require_native_owner_class(
        program,
        class,
        root_span_end,
        *receiver_span,
        "method receiver",
    )?;
    let Some(method) = declaration
        .methods
        .iter()
        .find(|candidate| candidate.f.name == *method_name)
    else {
        return Err(vec![diag(
            "backend.method_missing",
            "native method was not found on its receiver",
            expression.span,
            format!("class `{}` has no method `{method_name}`", declaration.name),
        )]);
    };
    let key = locals.call_owner.as_ref().map(|owner| CallSiteKey {
        owner: owner.clone(),
        span: expression.span,
        target: CallTarget::Method {
            class: declaration.name.clone(),
            method: method.f.name.clone(),
        },
    });
    let checked_call = match key.as_ref() {
        Some(key) => locals.checked_method_call(key, expression.span)?,
        None => None,
    };
    if let Some(checked_call) = checked_call.as_ref() {
        validate_exact_method_call_authority(
            checked_call,
            class,
            receiver,
            *receiver_span,
            method,
            args,
        )?;
    }
    let fixed = require_fixed_class(program, class, *receiver_span, "method receiver").is_ok();
    if fixed {
        if method.f.name != "flip_sign"
            || method.self_kind != SelfKind::Mut
            || !method.f.params.is_empty()
            || method.f.ret != Ty::Unit
            || !args.is_empty()
        {
            return Err(vec![diag(
                "backend.class_unsupported",
                "method call is outside the concrete `Integer` surface the LLVM backend lowers",
                expression.span,
                "the backend lowers only the zero-argument unit method `Integer::flip_sign`",
            )]);
        }
    } else {
        require_scalar_owner_method_result(
            program,
            root_span_end,
            method.f.ret.clone(),
            method.f.name_span,
        )?;
        if args.len() != method.f.params.len() {
            return Err(vec![diag(
                "backend.class_unsupported",
                "scalar-owner method call has the wrong arity",
                expression.span,
                format!(
                    "`{}::{}` receives {} argument(s), expected {}",
                    declaration.name,
                    method.f.name,
                    args.len(),
                    method.f.params.len()
                ),
            )]);
        }
    }
    let receiver_is_mutable = match local.ty.binding_mode() {
        BindingMode::Owned => matches!(local.ty, Ty::Class(_)) && local.mutable,
        BindingMode::Mut => matches!(local.ty.referent(), Ty::Class(_)),
        BindingMode::Shared => false,
    };
    if method.self_kind == SelfKind::Mut && !receiver_is_mutable {
        return Err(vec![diag(
            "backend.class_unsupported",
            "mutable method receiver is not mutable",
            *receiver_span,
            format!("`{receiver}` cannot receive `&mut self`"),
        )]);
    }
    require_expr_type(expression, method.f.ret.clone(), "native method result")?;
    if fixed {
        return Ok(());
    }

    validate_owned_argument_aliases(args, &method.f.params, locals)?;
    for (argument, parameter) in args.iter().zip(&method.f.params) {
        require_scalar_owner_method_parameter(
            program,
            root_span_end,
            parameter.ty.clone(),
            parameter.span,
            &format!("method parameter `{}`", parameter.name),
        )?;
        if let Ty::Class(argument_class) = parameter.ty {
            if matches!(&argument.kind, ExprKind::Var(owner) if owner == receiver) {
                return Err(vec![diag(
                    "backend.class_unsupported",
                    "owned method argument aliases its receiver",
                    argument.span,
                    format!(
                        "`{receiver}` cannot be both the live method receiver and an owned argument"
                    ),
                )]);
            }
            validate_fixed_class_initializer(
                program,
                argument_class,
                argument,
                root_span_end,
                locals,
            )?;
        } else {
            validate_expr(program, argument, root_span_end, locals)?;
            require_expr_type(argument, parameter.ty.clone(), "method call argument")?;
        }
    }
    validate_borrow_aliases(args, &method.f.params, locals)
}

fn validate_exact_method_call_authority(
    call: &CheckedCallTransition,
    class: usize,
    receiver: &str,
    receiver_span: Span,
    method: &crate::ast::Method,
    args: &[Expr],
) -> Result<(), Vec<BackendError>> {
    let expected_effect = match method.self_kind {
        SelfKind::Shared => CallEffect::SharedLoan,
        SelfKind::Mut => CallEffect::HavocUniqueBorrow,
    };
    let receiver_matches = call.receiver.as_ref().is_some_and(|checked| {
        checked.class.as_str()
            == match &call.key.target {
                CallTarget::Method { class, .. } => class.as_str(),
                CallTarget::Function(_) | CallTarget::Constructor { .. } => return false,
            }
            && checked.transition.place == Place::local(receiver)
            && checked.transition.referent == Ty::Class(class)
            && checked.transition.effect == expected_effect
            && checked.transition.span == receiver_span
    });
    if !receiver_matches {
        return Err(vec![diag(
            "internal.control_plan_invalid",
            "LLVM method receiver disagrees with its checker-authored call plan",
            receiver_span,
            format!(
                "receiver `{receiver}` must retain the exact class, place, mutability, and source span"
            ),
        )]);
    }
    if call.arguments.len() != method.f.params.len() || args.len() != method.f.params.len() {
        return Err(vec![diag(
            "internal.control_plan_invalid",
            "LLVM method arguments disagree with their checker-authored call plan",
            call.key.span,
            format!(
                "retained {}, declared {}, observed {} argument(s)",
                call.arguments.len(),
                method.f.params.len(),
                args.len()
            ),
        )]);
    }
    for (index, ((checked, parameter), argument)) in call
        .arguments
        .iter()
        .zip(&method.f.params)
        .zip(args)
        .enumerate()
    {
        let CallArgumentEffect::Value(transfer) = &checked.effect else {
            return Err(vec![diag(
                "internal.control_plan_invalid",
                "scalar-owner method argument retained an unsupported loan",
                checked.argument_span,
                format!("parameter `{}` must cross by value", parameter.name),
            )]);
        };
        let source = Place::from_value_expr(argument);
        let expected_kind = if matches!(parameter.ty, Ty::Class(_)) {
            if source.is_some() {
                ValueTransferKind::Move
            } else {
                ValueTransferKind::Fresh
            }
        } else {
            ValueTransferKind::Copy
        };
        let matches = checked.parameter_index == index
            && checked.parameter == parameter.name
            && checked.parameter_ty == parameter.ty
            && checked.argument_span == argument.span
            && transfer.source == source
            && transfer.value_ty == parameter.ty
            && transfer.kind == expected_kind
            && transfer.span == argument.span
            && !transfer.carried_obligation
            && !transfer.branded;
        if !matches {
            return Err(vec![diag(
                "internal.control_plan_invalid",
                "LLVM method argument disagrees with its checker-authored transfer",
                argument.span,
                format!(
                    "argument {index} for `{}` must retain its exact parameter identity, type, source, and move/copy outcome",
                    parameter.name
                ),
            )]);
        }
    }
    Ok(())
}

fn validate_local_bool_slot_container(
    argument: &Expr,
    locals: &ValidationLocals,
    operation: &str,
) -> Result<String, Vec<BackendError>> {
    let ExprKind::Borrow {
        array,
        field: None,
        mutable: true,
    } = &argument.kind
    else {
        return Err(vec![diag(
            "backend.slot_container",
            "native owner-slot operation requires a direct mutable local borrow",
            argument.span,
            format!("`{operation}` must borrow `&mut` from a local `slots<bool>` owner"),
        )]);
    };
    let expected = Ty::borrow(Mutability::Mut, Ty::slots(Ty::Bool));
    if argument.ty.as_ref() != Some(&expected) {
        return Err(vec![diag(
            "backend.slot_container",
            "native owner-slot borrow has the wrong checked type",
            argument.span,
            format!(
                "`{operation}` container is annotated `{}`, expected `{}`",
                argument
                    .ty
                    .as_ref()
                    .map_or_else(|| "<missing>".into(), Ty::name),
                expected.name()
            ),
        )]);
    }
    let Some(local) = locals.get(array) else {
        return Err(vec![diag(
            "backend.slot_container",
            "native owner-slot operation names an unknown local",
            argument.span,
            format!("`{operation}` names `{array}`"),
        )]);
    };
    if local.ty != Ty::slots(Ty::Bool) || !local.mutable {
        return Err(vec![diag(
            "backend.slot_container",
            "native owner-slot operation requires writable Boolean-slot storage",
            argument.span,
            format!("`{array}` has type `{}`", local.ty.name()),
        )]);
    }
    locals.require_live_slots(array, argument.span, operation)?;
    Ok(array.clone())
}

fn validate_bool_slot_operation(
    program: &Program,
    expression: &Expr,
    root_span_end: usize,
    locals: &mut ValidationLocals,
) -> Result<(), Vec<BackendError>> {
    let ExprKind::SlotOp { op, args, .. } = &expression.kind else {
        unreachable!("slot-operation validation is called only for a slot operation")
    };
    match op {
        SlotOp::Alloc { elem } => {
            if elem != &Ty::Bool {
                return Err(vec![slots_unsupported(
                    expression.span,
                    format!("`alloc_slots` payload `{}`", elem.name()),
                )]);
            }
            if args.len() != 1 {
                return Err(vec![diag(
                    "internal.control_plan_invalid",
                    "native slot allocation lost its checked arity",
                    expression.span,
                    format!("retained operation has {} argument(s)", args.len()),
                )]);
            }
            require_expr_type(
                expression,
                Ty::slots(Ty::Bool),
                "native Boolean-slot allocation",
            )?;
            validate_expr(program, &args[0], root_span_end, locals)?;
            require_expr_type(
                &args[0],
                Ty::Int(IntTy::U64),
                "native Boolean-slot allocation length",
            )
        }
        SlotOp::Take => {
            if args.len() != 2 {
                return Err(vec![diag(
                    "internal.control_plan_invalid",
                    "native slot take lost its checked arity",
                    expression.span,
                    format!("retained operation has {} argument(s)", args.len()),
                )]);
            }
            validate_local_bool_slot_container(&args[0], locals, "slot_take")?;
            validate_expr(program, &args[1], root_span_end, locals)?;
            require_expr_type(&args[1], Ty::Int(IntTy::U64), "native slot-take index")?;
            require_expr_type(expression, Ty::Bool, "native slot-take result")
        }
        SlotOp::Put => {
            if args.len() != 3 {
                return Err(vec![diag(
                    "internal.control_plan_invalid",
                    "native slot put lost its checked arity",
                    expression.span,
                    format!("retained operation has {} argument(s)", args.len()),
                )]);
            }
            validate_local_bool_slot_container(&args[0], locals, "slot_put")?;
            validate_expr(program, &args[1], root_span_end, locals)?;
            require_expr_type(&args[1], Ty::Int(IntTy::U64), "native slot-put index")?;
            validate_expr(program, &args[2], root_span_end, locals)?;
            require_expr_type(&args[2], Ty::Bool, "native slot-put value")?;
            require_expr_type(expression, Ty::Unit, "native slot-put result")
        }
    }
}

fn validate_bool_slots_initializer(
    program: &Program,
    expression: &Expr,
    root_span_end: usize,
    locals: &mut ValidationLocals,
    destination: &str,
) -> Result<(), Vec<BackendError>> {
    require_expr_type(
        expression,
        Ty::slots(Ty::Bool),
        "native Boolean-slot owner initializer",
    )?;
    match &expression.kind {
        ExprKind::SlotOp {
            op: SlotOp::Alloc { .. },
            ..
        } => validate_bool_slot_operation(program, expression, root_span_end, locals),
        ExprKind::Var(source) => {
            let Some(local) = locals.get(source) else {
                return Err(vec![diag(
                    "backend.slots_owner_value_position",
                    "native owner-slot move names an unknown local",
                    expression.span,
                    format!("initializer of `{destination}` names `{source}`"),
                )]);
            };
            if local.ty != Ty::slots(Ty::Bool) {
                return Err(vec![diag(
                    "backend.slots_owner_value_position",
                    "native owner-slot move has a mismatched source",
                    expression.span,
                    format!("`{source}` has type `{}`", local.ty.name()),
                )]);
            }
            if source == destination {
                return Err(vec![diag(
                    "backend.slots_owner_value_position",
                    "native owner-slot value cannot move into itself",
                    expression.span,
                    format!("assignment target and source are both `{source}`"),
                )]);
            }
            locals.require_live_slots(source, expression.span, "whole-owner move")?;
            locals.mark_slots_moved(source);
            Ok(())
        }
        _ => Err(vec![diag(
            "backend.slots_owner_value_position",
            "owner slots are outside this native value position",
            expression.span,
            "a local `slots<bool>` owner may be created by `alloc_slots<bool>` or moved directly from another local",
        )]),
    }
}

fn validate_expr(
    program: &Program,
    expression: &Expr,
    root_span_end: usize,
    locals: &mut ValidationLocals,
) -> Result<(), Vec<BackendError>> {
    if matches!(expression.kind, ExprKind::SlotOp { .. }) {
        return validate_bool_slot_operation(program, expression, root_span_end, locals);
    }
    if let ExprKind::IsSome { operand } = &expression.kind {
        if operand.ty.as_ref().is_some_and(Ty::is_affine_option) {
            return validate_affine_option_is_some(expression, operand, locals);
        }
    }
    if let Some(ty) = expression.ty.as_ref().filter(|ty| ty.is_affine_option()) {
        return Err(vec![affine_option_unsupported(
            expression.span,
            "expression",
            ty.clone(),
        )]);
    }
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
        ExprKind::Var(name) => {
            let Some(local) = locals.get(name) else {
                return Err(vec![unsupported(
                    expression.span,
                    format!("expression names unknown or out-of-scope local `{name}`"),
                )]);
            };
            if local.ty.as_array().is_some() {
                return Err(vec![unsupported(
                    expression.span,
                    format!("array local `{name}` cannot be transported as a value"),
                )]);
            }
            if is_owned_bool_slots(&local.ty) {
                locals.require_live_slots(name, expression.span, "owner-slot expression")?;
                return Err(vec![diag(
                    "backend.slots_owner_value_position",
                    "owner slots are outside this native value position",
                    expression.span,
                    "a whole `slots<bool>` owner moves only into an explicit local declaration or local assignment",
                )]);
            }
            if matches!(local.ty, Ty::Slots(_)) {
                return Err(vec![slots_unsupported(
                    expression.span,
                    format!("owner-slot local `{name}`"),
                )]);
            }
            if matches!(local.ty, Ty::Class(_)) {
                locals.require_live_class(name, expression.span, "class expression")?;
                return Err(vec![diag(
                    "backend.class_unsupported",
                    "class value is outside a destination-passing position",
                    expression.span,
                    "owned classes may only initialize another owner, return, or cross an admitted by-value boundary",
                )]);
            }
            let ty = expression.ty.clone().ok_or_else(|| {
                vec![unsupported(
                    expression.span,
                    "expression is missing its checked type",
                )]
            })?;
            require_runtime_type(
                program,
                root_span_end,
                ty.clone(),
                expression.span,
                "expression",
            )?;
            if ty != local.ty {
                return Err(vec![unsupported(
                    expression.span,
                    format!(
                        "local `{name}` has LLVM type `{}` but the expression is annotated `{}`",
                        local.ty.name(),
                        ty.name()
                    ),
                )]);
            }
            Ok(())
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
            if matches!(function.ret, Ty::Class(_)) {
                return Err(vec![diag(
                    "backend.class_unsupported",
                    "class-returning call is outside a destination-passing position",
                    expression.span,
                    "bind or return the owned class result directly",
                )]);
            }
            validate_call_arguments(program, function, args, root_span_end, locals)?;
            require_runtime_type(
                program,
                root_span_end,
                function.ret.clone(),
                expression.span,
                "call result",
            )?;
            require_expr_type(expression, function.ret.clone(), "call result")
        }
        ExprKind::Unary {
            op: UnOp::Not,
            operand,
        } => validate_bool_expr(
            program,
            operand,
            "logical-not operand",
            root_span_end,
            locals,
        ),
        ExprKind::Unary {
            op: UnOp::Neg,
            operand,
        } => {
            validate_expr(program, operand, root_span_end, locals)?;
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
            validate_bool_expr(
                program,
                lhs,
                "short-circuit left operand",
                root_span_end,
                locals,
            )?;
            validate_bool_expr(
                program,
                rhs,
                "short-circuit right operand",
                root_span_end,
                locals,
            )?;
            require_expr_type(expression, Ty::Bool, "short-circuit result")
        }
        ExprKind::Binary {
            op: op @ (BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq | BinOp::Ne),
            lhs,
            rhs,
            ..
        } => {
            validate_expr(program, lhs, root_span_end, locals)?;
            validate_expr(program, rhs, root_span_end, locals)?;
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
            validate_expr(program, lhs, root_span_end, locals)?;
            validate_expr(program, rhs, root_span_end, locals)?;
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
            validate_expr(program, arg, root_span_end, locals)?;
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
            validate_expr(program, arg, root_span_end, locals)?;
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
                Ty::option(Ty::Bool),
                "Boolean option construction",
            )?;
            validate_bool_expr(
                program,
                inner,
                "Boolean option payload",
                root_span_end,
                locals,
            )
        }
        ExprKind::NoneE => require_expr_type(
            expression,
            Ty::option(Ty::Bool),
            "Boolean option construction",
        ),
        ExprKind::IsSome { operand } => {
            validate_expr(program, operand, root_span_end, locals)?;
            require_expr_type(operand, Ty::option(Ty::Bool), "option accessor operand")?;
            require_expr_type(expression, Ty::Bool, "`.is_some` result")
        }
        ExprKind::OptValue { operand } => {
            if let Some(ty) = operand.ty.as_ref().filter(|ty| ty.is_affine_option()) {
                return Err(vec![affine_option_unsupported(
                    operand.span,
                    "copying `.value` accessor operand",
                    ty.clone(),
                )]);
            }
            validate_expr(program, operand, root_span_end, locals)?;
            require_expr_type(operand, Ty::option(Ty::Bool), "option accessor operand")?;
            require_expr_type(expression, Ty::Bool, "Boolean option payload")
        }
        ExprKind::OptTake { option, .. } => Err(vec![affine_option_take_position(
            expression.span,
            option,
            "expression",
        )]),
        ExprKind::Index {
            array,
            array_span,
            index,
        } => {
            let Some(local) = locals.get(array) else {
                return Err(vec![unsupported(
                    *array_span,
                    format!("array index names unknown or out-of-scope local `{array}`"),
                )]);
            };
            if local.ty.is_affine_option() {
                return Err(vec![affine_option_unsupported(
                    *array_span,
                    "array index base",
                    local.ty,
                )]);
            }
            if !is_native_array(&local.ty) {
                return Err(vec![unsupported(
                    *array_span,
                    format!(
                        "array index base `{array}` has unsupported LLVM type `{}`",
                        local.ty.name()
                    ),
                )]);
            }
            validate_expr(program, index, root_span_end, locals)?;
            require_expr_type(index, Ty::Int(IntTy::U64), "array index")?;
            let element_ty = if local.ty.is_bool_array() {
                Ty::Bool
            } else {
                Ty::Int(IntTy::U32)
            };
            require_expr_type(expression, element_ty, "array index result")
        }
        ExprKind::Len { array } => {
            let Some(local) = locals.get(array) else {
                return Err(vec![unsupported(
                    expression.span,
                    format!("array length names unknown or out-of-scope local `{array}`"),
                )]);
            };
            if local.ty.is_affine_option() {
                return Err(vec![affine_option_unsupported(
                    expression.span,
                    "array length base",
                    local.ty,
                )]);
            }
            if is_owned_bool_slots(&local.ty) {
                locals.require_live_slots(array, expression.span, "owner-slot length")?;
            } else if !is_native_array(&local.ty) {
                return Err(vec![unsupported(
                    expression.span,
                    format!(
                        "array length base `{array}` has unsupported LLVM type `{}`",
                        local.ty.name()
                    ),
                )]);
            }
            require_expr_type(expression, Ty::Int(IntTy::U64), "array length result")
        }
        ExprKind::ArrayLit(_) | ExprKind::AllocArray { .. } => Err(vec![unsupported(
            expression.span,
            "Boolean arrays are only values at a fresh owned-local initializer",
        )]),
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
                validate_expr(program, argument, root_span_end, locals)?;
                require_expr_type(argument, field.ty.clone(), "record field initializer")?;
            }
            Ok(())
        }
        ExprKind::RecordField { obj, obj_span, .. } => {
            reject_named_affine_option(locals, obj, *obj_span, "record field base")?;
            let Some(Ty::Int(integer)) = expression.ty else {
                return Err(vec![unsupported(
                    expression.span,
                    "a lowered record projection must have a concrete integer field type",
                )]);
            };
            require_concrete_integer(integer, expression.span, "record field projection")
        }
        ExprKind::Borrow { array, .. } => {
            reject_named_affine_option(locals, array, expression.span, "borrow source")?;
            Err(vec![unsupported(
                expression.span,
                "expression is outside the scalar/Boolean-option/POD-record/owned-Boolean-array LLVM subset",
            )])
        }
        ExprKind::MethodCall { .. } => {
            validate_native_method_call(program, expression, root_span_end, locals)
        }
        ExprKind::ClassFieldIndex {
            obj,
            obj_span,
            field,
            index,
        } => {
            let (_, _, field_ty) =
                validate_fixed_class_field_base(program, locals, obj, field, *obj_span)?;
            if field_ty != Ty::array(Ty::Int(IntTy::U32)) {
                return Err(vec![diag(
                    "backend.class_unsupported",
                    "indexed class field is not the native `u32` array",
                    expression.span,
                    format!("`{obj}.{field}` has type `{}`", field_ty.name()),
                )]);
            }
            validate_expr(program, index, root_span_end, locals)?;
            require_expr_type(index, Ty::Int(IntTy::U64), "class array-field index")?;
            require_expr_type(expression, Ty::Int(IntTy::U32), "class array-field element")
        }
        ExprKind::ClassFieldLen { obj, field } => {
            let (_, _, field_ty) =
                validate_fixed_class_field_base(program, locals, obj, field, expression.span)?;
            if field_ty != Ty::array(Ty::Int(IntTy::U32)) {
                return Err(vec![diag(
                    "backend.class_unsupported",
                    "class `.len` field is not the native `u32` array",
                    expression.span,
                    format!("`{obj}.{field}` has type `{}`", field_ty.name()),
                )]);
            }
            require_expr_type(expression, Ty::Int(IntTy::U64), "class array-field length")
        }
        ExprKind::ClassField {
            obj,
            obj_span,
            field,
        } => {
            let (_, _, field_ty) =
                validate_fixed_class_field_base(program, locals, obj, field, *obj_span)?;
            let Ty::Int(integer) = field_ty else {
                return Err(vec![diag(
                    "backend.class_unsupported",
                    "class field value is outside the concrete `Integer` surface the LLVM backend lowers",
                    expression.span,
                    format!("`{obj}.{field}` has non-scalar type `{}`", field_ty.name()),
                )]);
            };
            require_concrete_integer(integer, expression.span, "class scalar field")?;
            require_expr_type(expression, field_ty, "class scalar field")
        }
        ExprKind::SelfField { field } => {
            let (_, _, field_ty) = validate_native_owner_class_field_base(
                program,
                root_span_end,
                locals,
                "self",
                field,
                expression.span,
            )?;
            let Ty::Int(integer) = field_ty else {
                return Err(vec![diag(
                    "backend.class_unsupported",
                    "method field read is outside the exact native scalar-owner surface",
                    expression.span,
                    format!("`self.{field}` has type `{}`", field_ty.name()),
                )]);
            };
            require_concrete_integer(integer, expression.span, "method scalar field")?;
            require_expr_type(expression, field_ty, "method scalar field")
        }
        _ => Err(vec![unsupported(
            expression.span,
            "expression is outside the scalar/Boolean-option/POD-record/owned-Boolean-array LLVM subset",
        )]),
    }
}

fn validate_affine_option_is_some(
    expression: &Expr,
    operand: &Expr,
    locals: &ValidationLocals,
) -> Result<(), Vec<BackendError>> {
    require_expr_type(expression, Ty::Bool, "affine-option `.is_some` result")?;
    let Some(ty) = operand.ty.as_ref().filter(|ty| ty.is_affine_option()) else {
        unreachable!("called only for an affine-option operand")
    };
    if !is_affine_bool_option(&ty.clone()) {
        return Err(vec![affine_option_unsupported(
            operand.span,
            "`.is_some` operand",
            ty.clone(),
        )]);
    }
    let ExprKind::Var(name) = &operand.kind else {
        return Err(vec![diag(
            "backend.affine_option_unsupported",
            "affine option is outside the locals the LLVM backend lowers",
            operand.span,
            "`.is_some` requires a named affine-option local",
        )]);
    };
    let Some(local) = locals.get(name) else {
        return Err(vec![diag(
            "backend.affine_option_unsupported",
            "affine option is outside the locals the LLVM backend lowers",
            operand.span,
            format!("`.is_some` names unknown or out-of-scope local `{name}`"),
        )]);
    };
    if local.ty != *ty {
        return Err(vec![diag(
            "backend.affine_option_unsupported",
            "affine option is outside the locals the LLVM backend lowers",
            operand.span,
            format!(
                "`.is_some` names `{name}` of type `{}` but is annotated `{}`",
                local.ty.name(),
                ty.clone().name()
            ),
        )]);
    }
    if !local.mutable {
        return Err(vec![diag(
            "backend.affine_option_unsupported",
            "affine option is outside the locals the LLVM backend lowers",
            operand.span,
            format!("affine option local `{name}` must be mutable"),
        )]);
    }
    Ok(())
}

fn validate_bool_expr(
    program: &Program,
    expression: &Expr,
    role: &str,
    root_span_end: usize,
    locals: &mut ValidationLocals,
) -> Result<(), Vec<BackendError>> {
    validate_expr(program, expression, root_span_end, locals)?;
    require_expr_type(expression, Ty::Bool, role)
}

fn require_expr_type(expression: &Expr, expected: Ty, role: &str) -> Result<(), Vec<BackendError>> {
    if expression.ty == Some(expected.clone()) {
        Ok(())
    } else {
        Err(vec![unsupported(
            expression.span,
            format!("{role} is missing checked type `{}`", expected.name()),
        )])
    }
}

/// Authorize one nominal record for the backend's internal *value*
/// representation.  The
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
                "{role} uses imported record `{}`; the backend declares no cross-module record ABI, so a record identity is lowered only inside the module that declares it",
                declaration.name
            ),
        )]);
    }
    for field in &declaration.fields {
        if field.ty.is_affine_option() {
            return Err(vec![affine_option_unsupported(
                field.span,
                &format!("record `{}.{}` field", declaration.name, field.name),
                field.ty.clone(),
            )]);
        }
        if !matches!(field.ty, Ty::Int(integer) if !matches!(integer, IntTy::TParam(_))) {
            return Err(vec![unsupported(
                field.span,
                format!(
                    "record `{}.{}` has field type `{}`; the backend lowers a record value only when every field is a concrete integer",
                    declaration.name,
                    field.name,
                    field.ty.clone().name()
                ),
            )]);
        }
    }
    Ok(())
}

pub(crate) fn require_runtime_type(
    program: &Program,
    root_span_end: usize,
    ty: Ty,
    span: Span,
    role: &str,
) -> Result<(), Vec<BackendError>> {
    match ty {
        Ty::Slots(_) => Err(vec![slots_unsupported(span, role)]),
        Ty::Int(integer) if !matches!(integer, IntTy::TParam(_)) => Ok(()),
        Ty::Bool | Ty::Unit => Ok(()),
        Ty::Option(payload) if payload.as_ref() == &Ty::Bool => Ok(()),
        ty if ty.is_affine_option() => Err(vec![affine_option_unsupported(span, role, ty)]),
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

pub(crate) fn require_local_value(
    program: &Program,
    root_span_end: usize,
    ty: Ty,
    span: Span,
    role: &str,
) -> Result<(), Vec<BackendError>> {
    match ty {
        Ty::Slots(payload) if payload.as_ref() == &Ty::Bool => Ok(()),
        Ty::Slots(_) => Err(vec![slots_unsupported(span, role)]),
        Ty::Int(integer) if !matches!(integer, IntTy::TParam(_)) => Ok(()),
        Ty::Bool => Ok(()),
        Ty::Option(payload) if payload.as_ref() == &Ty::Bool => Ok(()),
        ty if is_affine_bool_option(&ty.clone()) => Ok(()),
        ty if ty.is_affine_option() => Err(vec![affine_option_unsupported(span, role, ty)]),
        ty if is_owned_native_array(&ty.clone()) => Ok(()),
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

pub(crate) fn require_parameter_value(
    program: &Program,
    root_span_end: usize,
    ty: Ty,
    span: Span,
    role: &str,
) -> Result<(), Vec<BackendError>> {
    match ty {
        Ty::Slots(_) => Err(vec![slots_unsupported(span, role)]),
        Ty::Int(integer) if !matches!(integer, IntTy::TParam(_)) => Ok(()),
        Ty::Bool => Ok(()),
        // A Boolean option crosses the call as the internal
        // `%sable.option.bool` aggregate by value, the same representation a
        // return or local of the type already uses. The aggregate's layout is
        // module-internal and versionable, not a source or C ABI. Integer
        // options have no LLVM representation in any position, so they fall
        // through to the named refusal below.
        Ty::Option(payload) if payload.as_ref() == &Ty::Bool => Ok(()),
        // A borrowed array is its descriptor, passed by value. The callee
        // cannot change the length or the allocation, so a `&mut` callee's
        // element writes reach the caller's storage through the shared data
        // pointer and need no write-back.
        ref borrowed
            if matches!(
                borrowed.as_array_borrow(),
                Some((&Ty::Int(IntTy::U32), _)) | Some((&Ty::Bool, _))
            ) =>
        {
            Ok(())
        }
        Ty::Class(class) => {
            let declaration = require_fixed_class(program, class, span, role)?;
            if declaration.name == "Nat" {
                Ok(())
            } else {
                Err(vec![diag(
                    "backend.class_unsupported",
                    "owned class parameter is outside the exact native take ABI",
                    span,
                    "the backend lowers owned `Nat` parameters only",
                )])
            }
        }
        borrowed if borrowed.as_class_borrow().is_some() => {
            let (class, mutability) = borrowed
                .as_class_borrow()
                .expect("the arm's guard already matched a class borrow");
            let declaration = require_fixed_class(program, class, span, role)?;
            // A shared reference is uniform across the fixed-owner classes; a
            // mutable one reaches a `&mut self` method, and only `Integer` has
            // one in the native ABI.
            if mutability == Mutability::Shared || declaration.name == "Integer" {
                Ok(())
            } else {
                Err(vec![diag(
                    "backend.class_unsupported",
                    "mutable class reference is outside the exact native method ABI",
                    span,
                    "the backend lowers mutable `Integer` references only",
                )])
            }
        }
        ty if ty.is_affine_option() => Err(vec![affine_option_unsupported(span, role, ty)]),
        Ty::Record(record) => require_record_value(program, root_span_end, record, span, role),
        _ => Err(vec![unsupported(
            span,
            format!(
                "{role} type `{}` has no LLVM value representation; the backend lowers concrete integers, `bool`, `option<bool>`, borrowed `u32` and `bool` arrays, fixed-owner classes, and integer-field records as values",
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
const TRAP_ARRAY_OOM: u32 = 9;
const TRAP_ARRAY_OOB: u32 = 10;
const TRAP_SLOTS_OOM: u32 = 11;
const TRAP_SLOTS_OOB: u32 = 12;
const TRAP_SLOTS_EMPTY: u32 = 13;
const TRAP_SLOTS_OCCUPIED: u32 = 14;

/// Internal aggregate representation for an option over a non-integer payload.
/// This is deliberately not a C ABI promise: byte fields make the layout
/// unambiguous inside generated LLVM while ordinary Sable `bool` remains i1.
const LLVM_OPTION_BOOL: &str = "%sable.option.bool";

/// Internal owned Boolean-array descriptor. Field 0 is either null for an
/// empty array or a runtime-owned allocation containing one i8 byte per
/// element; field 1 is the logical element count. This is not a source ABI.
const LLVM_ARRAY_BOOL: &str = "%sable.array.bool";

/// Internal `u32`-array descriptor. The v1 allocation hook promises only a
/// byte allocation, so every typed payload access is emitted with `align 1`.
/// Field 1 remains the logical element count, not the allocation byte size.
const LLVM_ARRAY_U32: &str = "%sable.array.u32";

/// Internal affine Boolean-array option. The byte tag is canonical: zero is
/// absent and one owns the nested array descriptor. This remains local-only;
/// it is deliberately not a source or C ABI.
const LLVM_AFFINE_OPTION_BOOL_ARRAY: &str = "%sable.option.array.bool";

/// One independently occupied Boolean owner cell. The tag is canonical zero
/// (empty) or one (occupied); the payload byte is read only after the occupied
/// guard succeeds. This is not an option or an ordinary copy-array element.
const LLVM_SLOT_BOOL_CELL: &str = "%sable.slot.bool";

/// Local-only owner-slot descriptor. A null pointer with length zero is both
/// a live zero-length allocation and the neutral state left by a whole-owner
/// move. Static ownership prevents operations on the latter, while cleanup is
/// intentionally null-safe.
const LLVM_SLOTS_BOOL: &str = "%sable.slots.bool";

/// Nominal identity is the checked program's record tag, the same identity
/// carried by interpreter/SVM values. Numeric names are deterministic and
/// LLVM-safe without making source spelling or flattened indices a linkable
/// ABI: every generated function and type remains module-internal.
fn llvm_record_ty(record: usize) -> String {
    format!("%sable.record.{record}")
}

fn llvm_class_ty(class: usize) -> String {
    format!("%sable.class.{class}")
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
    needs_array_bool: bool,
    needs_array_u32: bool,
    needs_affine_option_bool_array: bool,
    needs_slots_bool: bool,
    classes: BTreeSet<usize>,
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

    fn require_array_bool(&mut self) {
        self.needs_array_bool = true;
        self.needs_trap = true;
    }

    fn require_array_u32(&mut self) {
        self.needs_array_u32 = true;
        self.needs_trap = true;
    }

    fn require_affine_option_bool_array(&mut self) {
        self.needs_affine_option_bool_array = true;
        self.require_array_bool();
    }

    fn require_slots_bool(&mut self) {
        self.needs_slots_bool = true;
        self.needs_trap = true;
    }

    fn require_class(&mut self, program: &Program, class: usize) {
        if !self.classes.insert(class) {
            return;
        }
        for field in &program.classes[class].fields {
            match &field.ty {
                Ty::Array(element) if element.as_ref() == &Ty::Int(IntTy::U32) => {
                    self.require_array_u32();
                }
                Ty::Class(child) => self.require_class(program, *child),
                _ => {}
            }
        }
    }

    fn require_record(&mut self, record: usize) {
        self.records.insert(record);
    }

    fn emit_record_type(
        record: usize,
        declaration: &RecordDecl,
        out: &mut String,
    ) -> Result<(), Vec<BackendError>> {
        let mut fields = Vec::with_capacity(declaration.fields.len());
        for field in &declaration.fields {
            fields.push(require_llvm_ty(
                field.ty.clone(),
                field.span,
                &format!("field `{}.{}`", declaration.name, field.name),
            )?);
        }
        let fields = fields.join(", ");
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
        Ok(())
    }

    fn emit(&self, program: &Program, out: &mut String) -> Result<(), Vec<BackendError>> {
        if self.needs_option_bool {
            out.push_str(LLVM_OPTION_BOOL);
            out.push_str(" = type { i8, i8 }\n\n");
        }
        if self.needs_array_bool {
            out.push_str(LLVM_ARRAY_BOOL);
            out.push_str(" = type { ptr, i64 }\n\n");
        }
        if self.needs_array_u32 {
            out.push_str(LLVM_ARRAY_U32);
            out.push_str(" = type { ptr, i64 }\n\n");
        }
        if self.needs_slots_bool {
            out.push_str(LLVM_SLOT_BOOL_CELL);
            out.push_str(" = type { i8, i8 }\n");
            out.push_str(LLVM_SLOTS_BOOL);
            out.push_str(" = type { ptr, i64 }\n\n");
        }
        if self.needs_array_bool || self.needs_array_u32 || self.needs_slots_bool {
            out.push_str(
                "; target runtime hooks for owned contiguous storage; allocation size is bytes\n\
                 declare ptr @__sable_rt_array_alloc_v1(i64)\n\
                 declare void @__sable_rt_array_free_v1(ptr)\n\n",
            );
        }
        if self.needs_affine_option_bool_array {
            out.push_str(LLVM_AFFINE_OPTION_BOOL_ARRAY);
            out.push_str(" = type { i8, %sable.array.bool }\n\n");
        }
        for class in &self.classes {
            out.push_str(&format!(
                "; internal fixed-owner semantic value for class `{}`; not a public ABI\n",
                program.classes[*class].name
            ));
            let declaration = &program.classes[*class];
            let mut fields = Vec::with_capacity(declaration.fields.len());
            for field in &declaration.fields {
                fields.push(require_llvm_ty(
                    field.ty.clone(),
                    field.span,
                    &format!("field `{}.{}`", declaration.name, field.name),
                )?);
            }
            let fields = fields.join(", ");
            out.push_str(&format!(
                "{} = type {{ {fields} }}\n\n",
                llvm_class_ty(*class)
            ));
        }
        for record in &self.records {
            Self::emit_record_type(*record, &program.records[*record], out)?;
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
                 8 option value of none, 9 array OOM, 10 array index OOB, \
                 11 slots OOM, 12 slots index OOB, 13 slots empty, \
                 14 slots occupied\n\
                 ; type_info bytes: result/destination, lhs/source, rhs; \
                 type codes u8..u64,i8..i64 = 1..8\n\
                 ; array traps use type_info 0: OOM lhs=len/rhs=0; \
                 OOB lhs=index/rhs=len; slots traps use the same payload shape\n\
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
        Ok(())
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

struct ActiveCleanupScope {
    id: ScopeId,
    /// Candidate identity comes from BodyPlan. The backend records only
    /// whether this structured path reached the declaration; place, type, and
    /// exit order stay authoritative in the shared plan.
    reached: HashSet<DropId>,
}

struct FunctionEmitter<'a, 'support> {
    program: &'a Program,
    function: &'a Fn,
    support: &'support mut ModuleSupport,
    initializer_class: Option<usize>,
    method: Option<(usize, usize)>,
    locals: HashMap<String, Local>,
    /// Entry-block storage for plan-named assignment temporaries. The shared
    /// action decides which cleanup-bearing RHS must survive while the old
    /// destination is destroyed.
    assignment_staging_slots: HashMap<Place, String>,
    /// Checker-owned `slot_put` value identities. Even a Boolean payload is
    /// materialized here before either destination guard so the backend
    /// consumes the exact retained staging place and preserves source order.
    slot_put_staging_slots: HashMap<Place, String>,
    late_entry_allocas: Vec<String>,
    next_local: usize,
    next_temp: usize,
    next_block: usize,
    lines: Vec<String>,
    /// Name of the block currently accepting instructions.  `None` means
    /// that its terminator has been emitted; a sibling or merge may still be
    /// started afterwards.
    current_block: Option<String>,
    /// Ownership-bearing locals with a live or backend-neutral slot on the
    /// current structured path, keyed by the shared plan's candidates and
    /// grouped by lexical lifetime. An explicitly uninitialized fixed class is
    /// registered at its declaration after its slot receives the recursively
    /// null-safe `zeroinitializer`; this keeps cleanup correct on one-arm and
    /// zero-iteration paths without inventing a traversal-order notion of
    /// initialization.
    /// An `unsafe` block deliberately shares its caller's scope; `if` branches
    /// and loop bodies push the stable scope selected by their source anchor.
    cleanup_scopes: Vec<ActiveCleanupScope>,
    control: BodyPlan,
    /// Concrete-class destruction recipes retained by the checker. Production
    /// lowering clones these from `ControlProgram`; only test-only unsealed
    /// lowering constructs recipes directly from its synthetic AST.
    class_drop_plans: Vec<ClassDropPlan>,
}

impl<'a, 'support> FunctionEmitter<'a, 'support> {
    fn new(
        program: &'a Program,
        control: Option<&ControlProgram>,
        function: &'a Fn,
        support: &'support mut ModuleSupport,
    ) -> Result<Self, Vec<BackendError>> {
        Self::new_with_owner(
            program,
            control,
            function,
            support,
            CallOwner::Function(function.name.clone()),
        )
    }

    fn new_with_owner(
        program: &'a Program,
        control_program: Option<&ControlProgram>,
        function: &'a Fn,
        support: &'support mut ModuleSupport,
        owner: CallOwner,
    ) -> Result<Self, Vec<BackendError>> {
        let (control, class_drop_plans) = match control_program {
            Some(program) => {
                let body = program
                    .body(&owner, function.span)
                    .map_err(|error| vec![control_plan_backend_error(error)])?;
                body.validate_callable(function.span, &function.params, &function.body)
                    .map_err(|error| vec![control_plan_backend_error(error)])?;
                (body.plan().clone(), program.class_drops().to_vec())
            }
            None => (
                BodyPlan::build(owner, function.span, &function.params, &function.body)
                    .map_err(|error| vec![control_plan_backend_error(error)])?,
                program
                    .classes
                    .iter()
                    .enumerate()
                    .map(|(class, declaration)| ClassDropPlan::build(class, declaration))
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|error| vec![control_plan_backend_error(error)])?,
            ),
        };
        Ok(Self {
            program,
            function,
            support,
            initializer_class: None,
            method: None,
            locals: HashMap::new(),
            assignment_staging_slots: HashMap::new(),
            slot_put_staging_slots: HashMap::new(),
            late_entry_allocas: Vec::new(),
            next_local: 0,
            next_temp: 0,
            next_block: 0,
            lines: Vec::new(),
            current_block: Some("entry".into()),
            cleanup_scopes: vec![
                ActiveCleanupScope {
                    id: control.frame_scope(),
                    reached: HashSet::new(),
                },
                ActiveCleanupScope {
                    id: control.body_scope(),
                    reached: HashSet::new(),
                },
            ],
            control,
            class_drop_plans,
        })
    }

    fn new_initializer(
        program: &'a Program,
        control: Option<&ControlProgram>,
        class: usize,
        initializer: usize,
        support: &'support mut ModuleSupport,
    ) -> Result<Self, Vec<BackendError>> {
        let declaration = &program.classes[class];
        let function = &declaration.inits[initializer];
        let mut emitter = Self::new_with_owner(
            program,
            control,
            function,
            support,
            CallOwner::Constructor {
                class: declaration.name.clone(),
                init: function.name.clone(),
            },
        )?;
        emitter.initializer_class = Some(class);
        Ok(emitter)
    }

    fn new_method(
        program: &'a Program,
        control: Option<&ControlProgram>,
        class: usize,
        method: usize,
        support: &'support mut ModuleSupport,
    ) -> Result<Self, Vec<BackendError>> {
        let declaration = &program.classes[class];
        let function = &declaration.methods[method].f;
        let mut emitter = Self::new_with_owner(
            program,
            control,
            function,
            support,
            CallOwner::Method {
                class: declaration.name.clone(),
                method: function.name.clone(),
            },
        )?;
        emitter.method = Some((class, method));
        Ok(emitter)
    }

    fn emit(mut self, out: &mut String) -> Result<(), Vec<BackendError>> {
        if let Some(class) = self
            .initializer_class
            .or(self.method.map(|(class, _)| class))
        {
            self.support.require_class(self.program, class);
        }
        self.require_type_support(self.function.ret.clone());
        let parameter_types = self
            .function
            .params
            .iter()
            .map(|parameter| parameter.ty.clone())
            .collect::<Vec<_>>();
        for ty in parameter_types {
            self.require_type_support(ty);
        }
        let mut explicit_parameters = Vec::with_capacity(self.function.params.len());
        for (index, parameter) in self.function.params.iter().enumerate() {
            let ty = require_llvm_ty(
                parameter.ty.clone(),
                parameter.span,
                &format!("parameter `{}`", parameter.name),
            )?;
            explicit_parameters.push(format!("{ty} %p{index}"));
        }
        let mut parameters = Vec::new();
        if self.initializer_class.is_some() || self.method.is_some() {
            parameters.push("ptr %self".to_string());
        }
        if self.initializer_class.is_none() && matches!(self.function.ret, Ty::Class(_)) {
            // A class-returning method needs both authorities: `%self` is
            // the receiver loan and `%result` is fresh caller-owned
            // destination storage. Free class-returning functions retain the
            // older one-pointer destination ABI.
            parameters.push("ptr %result".to_string());
        }
        parameters.extend(explicit_parameters);
        let parameters = parameters.join(", ");
        let symbol = match (self.initializer_class, self.method) {
            (Some(class), _) => mangle_initializer(class, self.function)?,
            (None, Some((class, _))) => mangle_method(class, self.function)?,
            (None, None) => mangle(self.function)?,
        };
        let return_ty = if matches!(self.function.ret, Ty::Class(_)) {
            "void".to_string()
        } else {
            require_llvm_ty(
                self.function.ret.clone(),
                self.function.name_span,
                &format!("the return type of `{}`", self.function.name),
            )?
        };
        out.push_str(&format!(
            "define internal {} @{symbol}({parameters}) {{\nentry:\n",
            return_ty,
        ));

        // LLVM permits allocas elsewhere, but keeping every stack slot in the
        // entry block gives branch-local Sable declarations one deterministic
        // representation without moving their initializer effects.
        let parameters = self
            .function
            .params
            .iter()
            .map(|parameter| (parameter.name.clone(), parameter.ty.clone()))
            .collect::<Vec<_>>();
        let mut declarations = Vec::new();
        collect_local_declarations(&self.function.body, &mut declarations);
        for (name, ty) in parameters.iter().chain(declarations.iter()) {
            self.require_type_support(ty.clone());
            let slot_ty = require_llvm_ty(
                ty.clone(),
                self.function.name_span,
                &format!("local `{name}`"),
            )?;
            let slot = self.new_slot();
            self.instruction(format!("{slot} = alloca {slot_ty}"));
            self.locals.insert(
                name.clone(),
                Local {
                    ty: ty.clone(),
                    slot,
                },
            );
        }
        let assignment_staging = self
            .control
            .assignments()
            .filter_map(|action| match (action.ty(), action.staging()) {
                (ty, AssignmentStaging::Temporary(place))
                    if matches!(ty, Ty::Class(_)) || is_owned_bool_slots(ty) =>
                {
                    Some(Ok((place.clone(), ty.clone(), action.span())))
                }
                (_, AssignmentStaging::Direct) => None,
                (ty, AssignmentStaging::Temporary(_)) => Some(Err(vec![diag(
                    "backend.control_plan_unsupported",
                    "LLVM cannot allocate a planned assignment temporary",
                    action.span(),
                    format!(
                        "assignment to `{}` stages unsupported type `{}`",
                        action.destination().render(),
                        ty.clone().name()
                    ),
                )])),
            })
            .collect::<Result<Vec<_>, _>>()?;
        for (place, ty, span) in assignment_staging {
            let slot_ty = match ty {
                Ty::Class(class) => llvm_class_ty(class),
                ty if is_owned_bool_slots(&ty) => LLVM_SLOTS_BOOL.to_string(),
                _ => unreachable!("assignment staging filter admitted this type"),
            };
            let slot = self.new_slot();
            self.instruction(format!("{slot} = alloca {slot_ty}"));
            if self.assignment_staging_slots.insert(place, slot).is_some() {
                return Err(vec![diag(
                    "internal.control_plan_invalid",
                    "duplicate LLVM assignment temporary",
                    span,
                    "one planned assignment temporary must identify one entry slot",
                )]);
            }
        }
        let slot_put_staging = self
            .control
            .slot_actions()
            .filter_map(|action| match action.kind() {
                SlotActionKind::Put { staging, .. } => {
                    Some((staging.clone(), action.payload().clone(), action.span()))
                }
                SlotActionKind::Alloc { .. } | SlotActionKind::Take { .. } => None,
            })
            .collect::<Vec<_>>();
        for (place, payload, span) in slot_put_staging {
            if !place.is_root() || payload != Ty::Bool {
                return Err(vec![diag(
                    "backend.slots_unsupported",
                    "native slot-put staging is outside the Boolean-local subset",
                    span,
                    format!(
                        "retained temporary `{}` stages payload `{}`",
                        place.render(),
                        payload.name()
                    ),
                )]);
            }
            let slot = self.new_slot();
            self.instruction(format!("{slot} = alloca i1"));
            if self.slot_put_staging_slots.insert(place, slot).is_some() {
                return Err(vec![diag(
                    "internal.control_plan_invalid",
                    "duplicate LLVM slot-put staging temporary",
                    span,
                    "one retained slot-put value identity must identify one entry slot",
                )]);
            }
        }
        let field_staging = self
            .control
            .field_assignments()
            .filter_map(|action| match action.staging() {
                AssignmentStaging::Direct => None,
                AssignmentStaging::Temporary(place) => Some((
                    place.clone(),
                    action.ty().clone(),
                    action.span(),
                    action.destination().render(),
                )),
            })
            .collect::<Vec<_>>();
        for (place, ty, span, destination) in field_staging {
            let slot_ty = match ty.clone() {
                Ty::Class(class) => llvm_class_ty(class),
                ty if is_owned_u32_array(ty.clone()) => LLVM_ARRAY_U32.to_string(),
                other => {
                    return Err(vec![diag(
                        "backend.control_plan_unsupported",
                        "LLVM cannot allocate a planned field-assignment temporary",
                        span,
                        format!(
                            "field assignment to `{destination}` stages unsupported type `{}`",
                            other.name()
                        ),
                    )]);
                }
            };
            let slot = self.new_slot();
            self.instruction(format!("{slot} = alloca {slot_ty}"));
            if self.assignment_staging_slots.insert(place, slot).is_some() {
                return Err(vec![diag(
                    "internal.control_plan_invalid",
                    "duplicate LLVM field-assignment temporary",
                    span,
                    "one planned field-assignment temporary must identify one entry slot",
                )]);
            }
        }
        if let Some(class) = self.initializer_class {
            // A native constructor begins with every field absent. The
            // neutral aggregate is the backend's dynamic-liveness encoding;
            // every retained field action can therefore run the same
            // stage/drop-if-present/install sequence as a method replacement.
            self.instruction(format!(
                "store {} zeroinitializer, ptr %self",
                llvm_class_ty(class)
            ));
        }
        for (index, (name, ty)) in parameters.iter().enumerate() {
            let slot = self
                .locals
                .get(name)
                .expect("parameter slot was preallocated")
                .slot
                .clone();
            let stored = require_llvm_ty(
                ty.clone(),
                self.function.name_span,
                &format!("parameter `{name}`"),
            )?;
            self.instruction(format!("store {stored} %p{index}, ptr {slot}"));
            self.arm_cleanup(name)?;
        }

        let body_block = self.control.body_block().id();
        self.emit_block(&self.function.body, body_block)?;
        if self.current_block.is_some() {
            if self.function.ret == Ty::Unit {
                self.emit_implicit_return_cleanups()?;
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
        for line in &self.late_entry_allocas {
            out.push_str(line);
            out.push('\n');
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
            Ty::Option(payload) if payload.as_ref() == &Ty::Bool => {
                self.support.require_option_bool()
            }
            ty if ty.is_bool_array() => self.support.require_array_bool(),
            ty if is_u32_array(&ty.clone()) => self.support.require_array_u32(),
            ty if is_affine_bool_option(&ty.clone()) => {
                self.support.require_affine_option_bool_array()
            }
            ref ty if is_owned_bool_slots(ty) => self.support.require_slots_bool(),
            Ty::Record(record) => self.support.require_record(record),
            ref named if named.class_index().is_some() => {
                let class = named
                    .class_index()
                    .expect("the arm's guard already matched this shape");
                self.support.require_class(self.program, class)
            }
            ty if ty.is_affine_option() => {
                unreachable!("affine option escaped LLVM validation into support collection")
            }
            _ => {}
        }
    }

    fn active_scope(&self) -> ScopeId {
        self.cleanup_scopes
            .last()
            .expect("lowering has an active lexical scope")
            .id
    }

    fn consume_expression_trap_sites(&self, expression: &Expr) -> Result<(), Vec<BackendError>> {
        let scope = self.active_scope();
        let sites = self
            .control
            .expression_trap_sites(scope, expression)
            .map_err(|error| vec![control_plan_backend_error(error)])?;
        self.consume_trap_sites(&sites, Some(scope))
    }

    fn consume_statement_trap_sites(&self, statement: &Stmt) -> Result<(), Vec<BackendError>> {
        let sites = self
            .control
            .statement_trap_sites(self.active_scope(), statement)
            .map_err(|error| vec![control_plan_backend_error(error)])?;
        self.consume_trap_sites(&sites, None)
    }

    /// Authenticate the complete checker-sealed slot transition before
    /// emitting operand effects or allocation/mutation. The exact action also
    /// owns the two direct terminal trap identities; child expressions
    /// consume their own sites recursively when they are evaluated.
    fn slot_action_preflight(&self, expression: &Expr) -> Result<SlotAction, Vec<BackendError>> {
        let scope = self.active_scope();
        let action = self
            .control
            .slot_action(scope, expression)
            .map_err(|error| vec![control_plan_backend_error(error)])?
            .clone();
        let sites = self
            .control
            .slot_action_trap_sites(&action)
            .map_err(|error| vec![control_plan_backend_error(error)])?;
        self.consume_trap_sites(&sites, Some(scope))?;
        Ok(action)
    }

    fn consume_trap_sites(
        &self,
        sites: &[&TrapSite],
        expected_scope: Option<ScopeId>,
    ) -> Result<(), Vec<BackendError>> {
        for site in sites {
            let route = site.route();
            if expected_scope.is_some_and(|scope| site.scope() != scope)
                || route.kind() != crate::control::ExitKind::Trap
                || !route.scopes().is_empty()
                || !route.clears().is_empty()
                || !route.drops().is_empty()
            {
                return Err(vec![diag(
                    "internal.control_plan_invalid",
                    "trap site does not abort through the empty no-unwind route",
                    site.span(),
                    "a source trap may not run lexical cleanup",
                )]);
            }
        }
        Ok(())
    }

    fn emit_block(&mut self, statements: &[Stmt], block: BlockId) -> Result<(), Vec<BackendError>> {
        let (scope, anchor, flow, planned) = {
            let block = self.control.block(block);
            (
                block.scope(),
                block.anchor(),
                block.flow(),
                block.statements().to_vec(),
            )
        };
        if scope != self.active_scope() || planned.len() != statements.len() {
            return Err(vec![control_plan_backend_error(PlanError {
                span: anchor,
                message: "LLVM block disagrees with its retained scope or statement shape".into(),
            })]);
        }
        for (statement, statement_plan) in statements.iter().zip(planned) {
            if self.current_block.is_none() {
                if statement_plan.entry_reachable() {
                    return Err(vec![control_plan_backend_error(PlanError {
                        span: anchor,
                        message: "LLVM terminated before a retained reachable statement".into(),
                    })]);
                }
                break;
            }
            if !statement_plan.entry_reachable() {
                return Err(vec![control_plan_backend_error(PlanError {
                    span: anchor,
                    message: "LLVM reached a statement sealed as structurally unreachable".into(),
                })]);
            }
            let statement_kind = statement_plan.kind();
            let structurally_matches = match statement {
                Stmt::Return { .. } => matches!(statement_kind, StatementPlanKind::Return),
                Stmt::If { .. } => matches!(statement_kind, StatementPlanKind::Branch(_)),
                Stmt::While { .. } => matches!(statement_kind, StatementPlanKind::Loop(_)),
                Stmt::Unsafe { .. } => matches!(statement_kind, StatementPlanKind::Unsafe(_)),
                Stmt::Expose { .. } => matches!(statement_kind, StatementPlanKind::Exposure(_)),
                Stmt::Decl { .. }
                | Stmt::Assign { .. }
                | Stmt::ExprStmt(_)
                | Stmt::Assert(_)
                | Stmt::VarDecl { .. }
                | Stmt::FieldAssign { .. }
                | Stmt::FieldStore { .. }
                | Stmt::Store { .. }
                | Stmt::StaticAlloc { .. }
                | Stmt::SystemAlloc { .. }
                | Stmt::SystemDealloc { .. } => {
                    matches!(statement_kind, StatementPlanKind::Linear(_))
                }
            };
            if !structurally_matches {
                return Err(vec![control_plan_backend_error(PlanError {
                    span: anchor,
                    message: "LLVM statement disagrees with its retained structural role".into(),
                })]);
            }
            let scope = self
                .cleanup_scopes
                .last()
                .expect("statement has an active lexical scope")
                .id;
            let planned_field_assignment = match statement {
                Stmt::FieldAssign {
                    field,
                    field_span,
                    value,
                } => {
                    let destination = Place::field("self", field);
                    let action = self
                        .control
                        .field_assignment(scope, *field_span, &destination, value)
                        .map_err(|error| vec![control_plan_backend_error(error)])?
                        .clone();
                    if action.scope() != scope || action.destination() != &destination {
                        return Err(vec![control_plan_backend_error(PlanError {
                            span: *field_span,
                            message: "LLVM field assignment is detached from its retained action"
                                .into(),
                        })]);
                    }
                    let drop_plan = match action.drop_action().map(|drop| drop.recipe()) {
                        Some(ValueDropRecipe::DropClass(class_drop)) => {
                            Some(self.class_drop_for_action(class_drop, *field_span)?)
                        }
                        Some(ValueDropRecipe::ReleaseSlots { .. }) => {
                            return Err(vec![diag(
                                "backend.slots_cleanup_unsupported",
                                "LLVM cannot lower owner-slot field replacement cleanup",
                                *field_span,
                                "occupied-slot cleanup remains outside the native backend",
                            )]);
                        }
                        Some(ValueDropRecipe::ReleaseArray { .. })
                        | Some(ValueDropRecipe::DropPresent(_))
                        | None => None,
                    };
                    Some((action, drop_plan))
                }
                _ => None,
            };
            let planned_temporary_drop = match statement {
                Stmt::ExprStmt(expression) if matches!(expression.ty, Some(Ty::Class(_))) => {
                    let action = self
                        .control
                        .temporary_drop(scope, expression)
                        .map_err(|error| vec![control_plan_backend_error(error)])?
                        .clone();
                    let ValueDropRecipe::DropClass(class_drop) = action.drop_action().recipe()
                    else {
                        return Err(vec![control_plan_backend_error(PlanError {
                            span: expression.span,
                            message: "discarded class temporary lost its terminal class recipe"
                                .into(),
                        })]);
                    };
                    let drop_plan = self.class_drop_for_action(class_drop, expression.span)?;
                    Some((action, drop_plan))
                }
                _ => None,
            };
            self.consume_statement_trap_sites(statement)?;
            match statement {
                Stmt::Decl { ty, name, init, .. } => {
                    self.emit_decl(name, ty.clone(), init.as_ref())?;
                }
                Stmt::VarDecl { name, init, ty, .. } => {
                    self.emit_decl(
                        name,
                        ty.clone().expect("validated inferred type"),
                        Some(init),
                    )?;
                }
                Stmt::Assign {
                    name,
                    name_span,
                    value,
                } => {
                    let scope = self
                        .cleanup_scopes
                        .last()
                        .expect("assignment has an active lexical scope")
                        .id;
                    let destination = Place::local(name);
                    let action = self
                        .control
                        .assignment(scope, *name_span, &destination)
                        .map_err(|error| vec![control_plan_backend_error(error)])?
                        .clone();
                    if action.scope() != scope {
                        return Err(vec![diag(
                            "internal.control_plan_invalid",
                            "assignment has a mismatched lexical scope",
                            *name_span,
                            "the exact action must belong to the active structured scope",
                        )]);
                    }
                    if !action.destination().is_root() {
                        return Err(vec![diag(
                            "internal.control_plan_invalid",
                            "assignment destination is not a local",
                            *name_span,
                            format!("planned destination `{}`", action.destination().render()),
                        )]);
                    }
                    let planned_name = action.destination().root();
                    let Some(local) = self.locals.get(planned_name) else {
                        return Err(vec![unsupported(
                            *name_span,
                            format!("LLVM local `{planned_name}` was not declared"),
                        )]);
                    };
                    let local_ty = local.ty.clone();
                    let slot = local.slot.clone();
                    if action.ty() != &local_ty {
                        return Err(vec![diag(
                            "internal.control_plan_invalid",
                            "assignment type disagrees with its planned action",
                            *name_span,
                            format!(
                                "`{planned_name}` is lowered as `{}` but planned as `{}`",
                                local_ty.name(),
                                action.ty().clone().name()
                            ),
                        )]);
                    }
                    let ty = action.ty().clone();
                    if is_owned_bool_slots(&ty) {
                        let (Some(_), AssignmentStaging::Temporary(staging)) =
                            (action.previous(), action.staging())
                        else {
                            return Err(vec![diag(
                                "internal.control_plan_invalid",
                                "owner-slot assignment lacks its planned replacement phases",
                                *name_span,
                                "an owner-slot replacement must stage, release-if-live, then install",
                            )]);
                        };
                        let Some(scratch) = self.assignment_staging_slots.get(staging).cloned()
                        else {
                            return Err(vec![diag(
                                "internal.control_plan_invalid",
                                "owner-slot assignment has no planned staging slot",
                                *name_span,
                                format!("missing temporary `{}`", staging.render()),
                            )]);
                        };
                        let staged = self.emit_bool_slots_initializer(value)?;
                        self.instruction(format!(
                            "store {LLVM_SLOTS_BOOL} {}, ptr {scratch}",
                            staged.operand.expect("owner-slot assignment value")
                        ));
                        self.emit_assignment_previous(&action)?;
                        let installed = self.new_temp();
                        self.instruction(format!(
                            "{installed} = load {LLVM_SLOTS_BOOL}, ptr {scratch}"
                        ));
                        self.instruction(format!(
                            "store {LLVM_SLOTS_BOOL} {installed}, ptr {slot}"
                        ));
                        self.instruction(format!(
                            "store {LLVM_SLOTS_BOOL} zeroinitializer, ptr {scratch}"
                        ));
                        continue;
                    }
                    if let Ty::Class(class) = ty {
                        let (Some(_), AssignmentStaging::Temporary(staging)) =
                            (action.previous(), action.staging())
                        else {
                            return Err(vec![diag(
                                "internal.control_plan_invalid",
                                "class assignment lacks its planned replacement phases",
                                *name_span,
                                "a class replacement must stage, drop-if-live, then install",
                            )]);
                        };
                        let Some(scratch) = self.assignment_staging_slots.get(staging).cloned()
                        else {
                            return Err(vec![diag(
                                "internal.control_plan_invalid",
                                "class assignment has no planned staging slot",
                                *name_span,
                                format!("missing temporary `{}`", staging.render()),
                            )]);
                        };
                        // Evaluate completely before destroying the old value:
                        // real Nat assignments borrow their own destination.
                        self.emit_fixed_class_into(class, &scratch, value)?;
                        self.emit_assignment_previous(&action)?;
                        self.emit_fixed_class_move(class, &slot, &scratch);
                        continue;
                    }
                    if action.previous().is_some()
                        || !matches!(action.staging(), AssignmentStaging::Direct)
                    {
                        return Err(vec![diag(
                            "internal.control_plan_invalid",
                            "direct assignment has cleanup-bearing replacement phases",
                            *name_span,
                            format!("`{planned_name}` is not a cleanup-bearing LLVM local"),
                        )]);
                    }
                    let emitted = self.emit_expr(value)?;
                    let stored = require_llvm_ty(
                        ty,
                        value.span,
                        &format!("assignment to `{planned_name}`"),
                    )?;
                    self.instruction(format!(
                        "store {stored} {}, ptr {}",
                        emitted.operand.expect("assignment value is non-unit"),
                        slot
                    ));
                }
                Stmt::ExprStmt(expression) => {
                    if let Some((action, drop_plan)) = planned_temporary_drop {
                        return Err(vec![diag(
                            "backend.class_unsupported",
                            "discarded class temporary is outside the LLVM destination-passing subset",
                            action.span(),
                            format!(
                                "temporary `{}` has retained class-drop recipe `{}`; bind or return the owned result",
                                action.temporary().render(),
                                drop_plan.class_name()
                            ),
                        )]);
                    }
                    self.emit_expr(expression)?;
                }
                Stmt::Return { value, span } => {
                    if let Some(value) = value {
                        if let Ty::Class(class) = self.function.ret {
                            self.emit_fixed_class_into(class, "%result", value)?;
                            self.emit_return_cleanups(*span)?;
                            self.terminate("ret void");
                            continue;
                        }
                        let emitted = self.emit_expr(value)?;
                        if emitted.ty != self.function.ret {
                            return Err(vec![unsupported(
                                value.span,
                                format!(
                                    "return has checked type `{}` but function `{}` returns `{}`",
                                    emitted.ty.name(),
                                    self.function.name,
                                    self.function.ret.clone().name()
                                ),
                            )]);
                        }
                        if emitted.ty == Ty::Unit {
                            // A unit-returning call is still effectful.  Its
                            // absent LLVM operand is consumed by `ret void`,
                            // rather than being unwrapped as a scalar.
                            self.emit_return_cleanups(*span)?;
                            self.terminate("ret void");
                        } else {
                            let returned = require_llvm_ty(
                                emitted.ty,
                                self.function.name_span,
                                &format!("the return value of `{}`", self.function.name),
                            )?;
                            self.emit_return_cleanups(*span)?;
                            self.terminate(format!(
                                "ret {returned} {}",
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
                        self.emit_return_cleanups(*span)?;
                        self.terminate("ret void");
                    }
                }
                Stmt::Assert(_) => {}
                Stmt::Unsafe { body, .. } => {
                    let StatementPlanKind::Unsafe(child) = statement_kind else {
                        unreachable!("the structural guard above matched `unsafe`")
                    };
                    self.emit_block(body, child)?;
                }
                Stmt::If {
                    cond,
                    then_block,
                    else_block,
                } => self.emit_if(cond, then_block, else_block.as_deref())?,
                Stmt::While {
                    cond,
                    kw_span,
                    body,
                    ..
                } => self.emit_while(cond, *kw_span, body)?,
                Stmt::Store {
                    array,
                    index,
                    value,
                    ..
                } => self.emit_native_array_store(array, index, value)?,
                Stmt::FieldAssign {
                    field,
                    field_span,
                    value,
                    ..
                } => {
                    let (action, drop_plan) = planned_field_assignment
                        .expect("field-assignment preflight retained its exact action");
                    let class = self
                        .initializer_class
                        .or(self.method.map(|(class, _)| class))
                        .expect("validated field assignment is in a class member");
                    let (field_index, field_ty) = self.class_field(class, field);
                    if action.ty() != &field_ty {
                        return Err(vec![control_plan_backend_error(PlanError {
                            span: *field_span,
                            message:
                                "LLVM class-field layout type disagrees with its retained action"
                                    .into(),
                        })]);
                    }
                    let field_slot = self.emit_class_field_slot(class, "%self", field_index);
                    match field_ty {
                        Ty::Array(element) if element.as_ref() == &Ty::Int(IntTy::U32) => {
                            let AssignmentStaging::Temporary(staging) = action.staging() else {
                                return Err(vec![control_plan_backend_error(PlanError {
                                    span: *field_span,
                                    message: "cleanup-bearing array field assignment has no retained staging temporary"
                                        .into(),
                                })]);
                            };
                            let scratch = self
                                .assignment_staging_slots
                                .get(staging)
                                .cloned()
                                .ok_or_else(|| {
                                    vec![control_plan_backend_error(PlanError {
                                        span: *field_span,
                                        message:
                                            "LLVM field assignment has no allocated staging slot"
                                                .into(),
                                    })]
                                })?;
                            let staged = self.emit_fresh_u32_array(value)?;
                            self.instruction(format!(
                                "store {LLVM_ARRAY_U32} {}, ptr {scratch}",
                                staged.operand.expect("owned class field initializer")
                            ));
                            if !action.drop_if_present() || drop_plan.is_some() {
                                return Err(vec![control_plan_backend_error(PlanError {
                                    span: *field_span,
                                    message: "array field action has inconsistent retained cleanup phases"
                                        .into(),
                                })]);
                            }
                            self.emit_u32_array_drop_from_slot(&field_slot);
                            let installed = self.new_temp();
                            self.instruction(format!(
                                "{installed} = load {LLVM_ARRAY_U32}, ptr {scratch}"
                            ));
                            self.instruction(format!(
                                "store {LLVM_ARRAY_U32} {installed}, ptr {field_slot}"
                            ));
                            self.instruction(format!(
                                "store {LLVM_ARRAY_U32} zeroinitializer, ptr {scratch}"
                            ));
                        }
                        Ty::Class(child) => {
                            let AssignmentStaging::Temporary(staging) = action.staging() else {
                                return Err(vec![control_plan_backend_error(PlanError {
                                    span: *field_span,
                                    message:
                                        "class field assignment has no retained staging temporary"
                                            .into(),
                                })]);
                            };
                            let scratch = self
                                .assignment_staging_slots
                                .get(staging)
                                .cloned()
                                .ok_or_else(|| {
                                    vec![control_plan_backend_error(PlanError {
                                        span: *field_span,
                                        message:
                                            "LLVM class-field action has no allocated staging slot"
                                                .into(),
                                    })]
                                })?;
                            let drop_plan = drop_plan.as_ref().ok_or_else(|| {
                                vec![control_plan_backend_error(PlanError {
                                    span: *field_span,
                                    message: "class field action has no exact class-drop recipe"
                                        .into(),
                                })]
                            })?;
                            if !action.drop_if_present() || drop_plan.class() != child {
                                return Err(vec![control_plan_backend_error(PlanError {
                                    span: *field_span,
                                    message: "class field action has inconsistent retained cleanup phases"
                                        .into(),
                                })]);
                            }
                            self.emit_fixed_class_into(child, &scratch, value)?;
                            self.emit_fixed_class_drop_from_slot_with_plan(
                                &field_slot,
                                child,
                                drop_plan,
                            )?;
                            self.emit_fixed_class_move(child, &field_slot, &scratch);
                        }
                        Ty::Int(_) => {
                            if action.drop_if_present()
                                || !matches!(action.staging(), AssignmentStaging::Direct)
                                || drop_plan.is_some()
                            {
                                return Err(vec![control_plan_backend_error(PlanError {
                                    span: *field_span,
                                    message: "scalar field action retained cleanup-only phases"
                                        .into(),
                                })]);
                            }
                            let value = self.emit_expr(value)?;
                            let stored = require_llvm_ty(
                                field_ty,
                                *field_span,
                                &format!("class field `{field}`"),
                            )?;
                            self.instruction(format!(
                                "store {stored} {}, ptr {field_slot}",
                                value.operand.expect("scalar class field assignment")
                            ));
                        }
                        _ => unreachable!("validated native class field type"),
                    }
                }
                Stmt::FieldStore {
                    field,
                    index,
                    value,
                    ..
                } => {
                    self.emit_self_u32_field_store(field, index, value)?;
                }
                Stmt::Expose {
                    kw_span,
                    array,
                    mutable,
                    ptr,
                    res,
                    ..
                } => {
                    validate_llvm_exposure_plan_shape(
                        &self.control,
                        block,
                        self.active_scope(),
                        *kw_span,
                        array,
                        *mutable,
                        ptr,
                        res,
                    )
                    .map_err(|error| vec![control_plan_backend_error(error)])?;
                    return Err(vec![unsupported(
                        *kw_span,
                        "raw/resource storage is outside the scalar LLVM subset",
                    )]);
                }
                _ => unreachable!("validated before lowering"),
            }
        }
        if self.current_block.is_some() != flow.can_fall_through() {
            return Err(vec![control_plan_backend_error(PlanError {
                span: anchor,
                message: "LLVM block reachability disagrees with its retained flow".into(),
            })]);
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
            if let Ty::Class(class) = ty {
                self.emit_fixed_class_into(class, &slot, init)?;
                self.arm_cleanup(name)?;
                return Ok(());
            }
            let value = if is_owned_bool_slots(&ty) {
                self.emit_bool_slots_initializer(init)?
            } else if ty.is_owned_bool_array() {
                self.emit_fresh_bool_array(init)?
            } else if is_owned_u32_array(ty.clone()) {
                self.emit_fresh_u32_array(init)?
            } else if is_affine_bool_option(&ty.clone()) {
                self.emit_affine_bool_option_initializer(init)?
            } else {
                self.emit_expr(init)?
            };
            let stored = require_llvm_ty(
                ty.clone(),
                init.span,
                &format!("the initializer of local `{name}`"),
            )?;
            self.instruction(format!(
                "store {stored} {}, ptr {slot}",
                value.operand.expect("local initializer is non-unit")
            ));
            self.arm_cleanup(name)?;
        } else if let Ty::Class(class) = ty {
            // The admitted fixed-owner class layouts contain only integers,
            // owned u32-array descriptors, and recursively admitted classes,
            // with no executable `deinit`. Their aggregate zero value is
            // therefore a non-owner sentinel: recursive drop sees only null
            // array pointers and is a semantic no-op. Registering that neutral
            // slot now makes later assignment and every lexical exit safe even
            // when a branch or loop never performs the first assignment.
            self.instruction(format!(
                "store {} zeroinitializer, ptr {slot}",
                llvm_class_ty(class)
            ));
            self.arm_cleanup(name)?;
        }
        Ok(())
    }

    fn emit_if(
        &mut self,
        condition: &Expr,
        then_block: &[Stmt],
        else_block: Option<&[Stmt]>,
    ) -> Result<(), Vec<BackendError>> {
        let anchor = condition.span;
        let parent_scope = self.active_scope();
        let branch = self
            .control
            .branch(parent_scope, anchor, else_block.is_some())
            .map_err(|error| vec![control_plan_backend_error(error)])?
            .clone();
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
        let then_arm = branch.then_arm().clone();
        self.cleanup_scopes.push(ActiveCleanupScope {
            id: then_arm.scope(),
            reached: HashSet::new(),
        });
        self.emit_block(then_block, then_arm.block())?;
        if let Some(route) = then_arm.normal_exit() {
            self.emit_cleanup_route(route)?;
            self.terminate(format!("br label %{merge_label}"));
        }
        self.cleanup_scopes.pop();

        if let Some(else_block) = else_block {
            self.start_block(false_label);
            let Some(else_arm) = branch.else_arm().cloned() else {
                return Err(vec![control_plan_backend_error(PlanError {
                    span: anchor,
                    message: "retained LLVM branch lost its source else arm".into(),
                })]);
            };
            self.cleanup_scopes.push(ActiveCleanupScope {
                id: else_arm.scope(),
                reached: HashSet::new(),
            });
            self.emit_block(else_block, else_arm.block())?;
            if let Some(route) = else_arm.normal_exit() {
                self.emit_cleanup_route(route)?;
                self.terminate(format!("br label %{merge_label}"));
            }
            self.cleanup_scopes.pop();
        }

        if branch.flow().can_fall_through() {
            self.start_block(merge_label);
        }
        Ok(())
    }

    fn emit_while(
        &mut self,
        condition: &Expr,
        anchor: Span,
        body: &[Stmt],
    ) -> Result<(), Vec<BackendError>> {
        let loop_plan = self
            .control
            .loop_plan(self.active_scope(), anchor, condition.span)
            .map_err(|error| vec![control_plan_backend_error(error)])?
            .clone();
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
        self.cleanup_scopes.push(ActiveCleanupScope {
            id: loop_plan.body_scope(),
            reached: HashSet::new(),
        });
        self.emit_block(body, loop_plan.body())?;
        if let Some(route) = loop_plan.backedge() {
            self.emit_cleanup_route(route)?;
            self.terminate(format!("br label %{header_label}"));
        }
        self.cleanup_scopes.pop();

        // The header's false edge always reaches this block, even when every
        // body path returns.
        if loop_plan.flow().can_fall_through() {
            self.start_block(exit_label);
        }
        Ok(())
    }

    fn emit_constructor_into(
        &mut self,
        class: usize,
        destination: &str,
        expression: &Expr,
    ) -> Result<(), Vec<BackendError>> {
        let ExprKind::CtorCall { init, args, .. } = &expression.kind else {
            unreachable!("validated fixed-owner class initializer")
        };
        self.support.require_class(self.program, class);
        let initializer = self.program.classes[class]
            .inits
            .iter()
            .find(|candidate| candidate.name == *init)
            .expect("validated constructor exists");
        let mut lowered = Vec::with_capacity(args.len() + 1);
        lowered.push(format!("ptr {destination}"));
        lowered.extend(self.emit_call_arguments(&initializer.params, args)?);
        self.instruction(format!(
            "call void @{}({})",
            mangle_initializer(class, initializer)?,
            lowered.join(", ")
        ));
        Ok(())
    }

    fn emit_fixed_class_into(
        &mut self,
        class: usize,
        destination: &str,
        expression: &Expr,
    ) -> Result<(), Vec<BackendError>> {
        self.consume_expression_trap_sites(expression)?;
        match &expression.kind {
            ExprKind::CtorCall { .. } => self.emit_constructor_into(class, destination, expression),
            ExprKind::Call { callee, args, .. } => {
                let function = self
                    .program
                    .fns
                    .iter()
                    .find(|function| function.name == *callee)
                    .expect("validated class-returning callee");
                let mut lowered = Vec::with_capacity(args.len() + 1);
                lowered.push(format!("ptr {destination}"));
                lowered.extend(self.emit_call_arguments(&function.params, args)?);
                self.instruction(format!(
                    "call void @{}({})",
                    mangle(function)?,
                    lowered.join(", ")
                ));
                Ok(())
            }
            ExprKind::MethodCall {
                recv, method, args, ..
            } => {
                let (receiver_class, receiver) = self.class_base_pointer(recv);
                let declaration = &self.program.classes[receiver_class];
                let method = declaration
                    .methods
                    .iter()
                    .find(|candidate| candidate.f.name == *method)
                    .expect("validated class-returning native method")
                    .f
                    .clone();
                let mut lowered = Vec::with_capacity(args.len() + 2);
                lowered.push(format!("ptr {receiver}"));
                lowered.push(format!("ptr {destination}"));
                lowered.extend(self.emit_call_arguments(&method.params, args)?);
                self.instruction(format!(
                    "call void @{}({})",
                    mangle_method(receiver_class, &method)?,
                    lowered.join(", ")
                ));
                Ok(())
            }
            ExprKind::Var(source) => {
                let source_slot = self
                    .locals
                    .get(source)
                    .expect("validated class move source")
                    .slot
                    .clone();
                self.emit_fixed_class_move(class, destination, &source_slot);
                Ok(())
            }
            _ => unreachable!("validated fixed-owner class destination source"),
        }
    }

    fn emit_fixed_class_move(&mut self, class: usize, destination: &str, source: &str) {
        let moved = self.new_temp();
        self.instruction(format!(
            "{moved} = load {}, ptr {source}",
            llvm_class_ty(class)
        ));
        self.instruction(format!(
            "store {} {moved}, ptr {destination}",
            llvm_class_ty(class)
        ));
        self.instruction(format!(
            "store {} zeroinitializer, ptr {source}",
            llvm_class_ty(class)
        ));
    }

    fn emit_call_arguments(
        &mut self,
        parameters: &[crate::ast::Param],
        arguments: &[Expr],
    ) -> Result<Vec<String>, Vec<BackendError>> {
        let mut lowered = Vec::with_capacity(arguments.len());
        for (parameter, argument) in parameters.iter().zip(arguments) {
            let value = if let Ty::Class(class) = parameter.ty {
                self.emit_owned_class_argument(class, argument)?
            } else {
                self.emit_expr(argument)?
            };
            let passed = require_llvm_ty(
                parameter.ty.clone(),
                argument.span,
                &format!("argument for parameter `{}`", parameter.name),
            )?;
            lowered.push(format!(
                "{passed} {}",
                value.operand.expect("call argument is non-unit")
            ));
        }
        Ok(lowered)
    }

    fn emit_owned_class_argument(
        &mut self,
        class: usize,
        expression: &Expr,
    ) -> Result<Value, Vec<BackendError>> {
        let source = match &expression.kind {
            ExprKind::Var(name) => self
                .locals
                .get(name)
                .expect("validated owned class argument")
                .slot
                .clone(),
            ExprKind::CtorCall { .. } | ExprKind::Call { .. } | ExprKind::MethodCall { .. } => {
                let slot = self.new_slot();
                self.late_entry_allocas
                    .push(format!("  {slot} = alloca {}", llvm_class_ty(class)));
                self.emit_fixed_class_into(class, &slot, expression)?;
                slot
            }
            _ => unreachable!("validated owned class call argument"),
        };
        let moved = self.new_temp();
        self.instruction(format!(
            "{moved} = load {}, ptr {source}",
            llvm_class_ty(class)
        ));
        self.instruction(format!(
            "store {} zeroinitializer, ptr {source}",
            llvm_class_ty(class)
        ));
        Ok(Value {
            ty: Ty::Class(class),
            operand: Some(moved),
        })
    }

    fn class_field(&self, class: usize, field: &str) -> (usize, Ty) {
        self.program.classes[class]
            .fields
            .iter()
            .enumerate()
            .find(|(_, declaration_field)| declaration_field.name == field)
            .map(|(index, declaration_field)| (index, declaration_field.ty.clone()))
            .expect("validated native class field")
    }

    fn emit_class_field_slot(&mut self, class: usize, base: &str, field: usize) -> String {
        let field_slot = self.new_temp();
        self.instruction(format!(
            "{field_slot} = getelementptr {}, ptr {base}, i32 0, i32 {field}",
            llvm_class_ty(class)
        ));
        field_slot
    }

    fn class_base_pointer(&mut self, object: &str) -> (usize, String) {
        if object == "self" {
            if let Some(class) = self
                .initializer_class
                .or(self.method.map(|(class, _)| class))
            {
                return (class, "%self".into());
            }
        }
        let local = self
            .locals
            .get(object)
            .expect("validated fixed-owner class base");
        let ty = local.ty.clone();
        let slot = local.slot.clone();
        match (ty.class_index(), ty.binding_mode()) {
            (Some(class), BindingMode::Owned) => (class, slot),
            // A class borrow's slot holds the pointer, so the base is one
            // load further in.
            (Some(class), BindingMode::Shared | BindingMode::Mut) => {
                let pointer = self.new_temp();
                self.instruction(format!("{pointer} = load ptr, ptr {slot}"));
                (class, pointer)
            }
            (None, _) => unreachable!("validated fixed-owner class base type"),
        }
    }

    fn class_field_slot(&mut self, object: &str, field: &str) -> (Ty, String) {
        let (class, base) = self.class_base_pointer(object);
        let (field_index, field_ty) = self.class_field(class, field);
        let field_slot = self.emit_class_field_slot(class, &base, field_index);
        (field_ty, field_slot)
    }

    fn load_class_u32_array_parts(&mut self, object: &str, field: &str) -> (String, String) {
        let (_, field_slot) = self.class_field_slot(object, field);
        self.load_u32_array_parts_from_slot(&field_slot)
    }

    fn emit_self_u32_field_store(
        &mut self,
        field: &str,
        index: &Expr,
        value: &Expr,
    ) -> Result<(), Vec<BackendError>> {
        let index = self
            .emit_expr(index)?
            .operand
            .expect("validated class array-field store index");
        let value = self
            .emit_expr(value)?
            .operand
            .expect("validated class array-field store value");
        let class = self
            .initializer_class
            .expect("validated array field store is in an initializer");
        let (field_index, _) = self.class_field(class, field);
        let field_slot = self.emit_class_field_slot(class, "%self", field_index);
        let (ptr, len) = self.load_u32_array_parts_from_slot(&field_slot);
        self.emit_bool_array_bounds_guard(&index, &len);
        let address = self.new_temp();
        self.instruction(format!(
            "{address} = getelementptr i32, ptr {ptr}, i64 {index}"
        ));
        self.instruction(format!("store i32 {value}, ptr {address}, align 1"));
        Ok(())
    }

    fn emit_fresh_bool_array(&mut self, expression: &Expr) -> Result<Value, Vec<BackendError>> {
        self.consume_expression_trap_sites(expression)?;
        self.support.require_array_bool();
        match &expression.kind {
            ExprKind::ArrayLit(elements) => self.emit_bool_array_literal(elements),
            ExprKind::AllocArray { len, init, .. } => self.emit_bool_array_allocation(len, init),
            ExprKind::OptTake { option, .. } => self.emit_affine_option_take(option),
            _ => unreachable!("validated fresh Boolean-array initializer"),
        }
    }

    fn emit_fresh_u32_array(&mut self, expression: &Expr) -> Result<Value, Vec<BackendError>> {
        self.consume_expression_trap_sites(expression)?;
        self.support.require_array_u32();
        match &expression.kind {
            ExprKind::ArrayLit(elements) => self.emit_u32_array_literal(elements),
            ExprKind::AllocArray { len, init, .. } => self.emit_u32_array_allocation(len, init),
            _ => unreachable!("validated fresh `u32`-array initializer"),
        }
    }

    fn emit_affine_bool_option_initializer(
        &mut self,
        expression: &Expr,
    ) -> Result<Value, Vec<BackendError>> {
        self.support.require_affine_option_bool_array();
        let operand = match &expression.kind {
            ExprKind::NoneE => "zeroinitializer".to_string(),
            ExprKind::SomeE(payload) => {
                let payload = self
                    .emit_fresh_bool_array(payload)?
                    .operand
                    .expect("validated affine option payload");
                let with_payload = self.new_temp();
                self.instruction(format!(
                    "{with_payload} = insertvalue {LLVM_AFFINE_OPTION_BOOL_ARRAY} zeroinitializer, {LLVM_ARRAY_BOOL} {payload}, 1"
                ));
                let tagged = self.new_temp();
                self.instruction(format!(
                    "{tagged} = insertvalue {LLVM_AFFINE_OPTION_BOOL_ARRAY} {with_payload}, i8 1, 0"
                ));
                tagged
            }
            _ => unreachable!("validated affine-option initializer"),
        };
        Ok(Value {
            ty: affine_bool_option_ty(),
            operand: Some(operand),
        })
    }

    fn emit_affine_option_take(&mut self, option: &str) -> Result<Value, Vec<BackendError>> {
        self.support.require_affine_option_bool_array();
        let Some(source) = self.locals.get(option) else {
            return Err(vec![unsupported(
                self.function.name_span,
                format!("LLVM affine-option local `{option}` was not declared"),
            )]);
        };
        let source_slot = source.slot.clone();
        let aggregate = self.new_temp();
        self.instruction(format!(
            "{aggregate} = load {LLVM_AFFINE_OPTION_BOOL_ARRAY}, ptr {source_slot}"
        ));
        let tag = self.new_temp();
        self.instruction(format!(
            "{tag} = extractvalue {LLVM_AFFINE_OPTION_BOOL_ARRAY} {aggregate}, 0"
        ));
        let invalid = self.new_temp();
        self.instruction(format!("{invalid} = icmp ne i8 {tag}, 1"));
        self.emit_untyped_trap_guard(&invalid, TRAP_OPTION_NONE);

        // Keep extraction and the destination store dominated by the tag
        // guard. Clearing first makes the memory-state ownership transition
        // atomic: no installed destination can coexist with a live source.
        let payload = self.new_temp();
        self.instruction(format!(
            "{payload} = extractvalue {LLVM_AFFINE_OPTION_BOOL_ARRAY} {aggregate}, 1"
        ));
        self.instruction(format!(
            "store {LLVM_AFFINE_OPTION_BOOL_ARRAY} zeroinitializer, ptr {source_slot}"
        ));
        Ok(Value {
            ty: Ty::array(Ty::Bool),
            operand: Some(payload),
        })
    }

    fn emit_affine_option_is_some(&mut self, operand: &Expr) -> Result<Value, Vec<BackendError>> {
        self.support.require_affine_option_bool_array();
        let ExprKind::Var(name) = &operand.kind else {
            unreachable!("validated affine-option `.is_some` place")
        };
        let Some(local) = self.locals.get(name) else {
            return Err(vec![unsupported(
                operand.span,
                format!("LLVM affine-option local `{name}` was not declared"),
            )]);
        };
        let slot = local.slot.clone();
        let aggregate = self.new_temp();
        self.instruction(format!(
            "{aggregate} = load {LLVM_AFFINE_OPTION_BOOL_ARRAY}, ptr {slot}"
        ));
        let tag = self.new_temp();
        self.instruction(format!(
            "{tag} = extractvalue {LLVM_AFFINE_OPTION_BOOL_ARRAY} {aggregate}, 0"
        ));
        let present = self.new_temp();
        self.instruction(format!("{present} = icmp eq i8 {tag}, 1"));
        Ok(Value {
            ty: Ty::Bool,
            operand: Some(present),
        })
    }

    fn emit_bool_array_literal(&mut self, elements: &[Expr]) -> Result<Value, Vec<BackendError>> {
        // Finish every source element before attempting allocation. This is
        // observable when an element calls or traps, and matches the
        // interpreter's left-to-right literal construction order.
        let mut bytes = Vec::with_capacity(elements.len());
        for element in elements {
            let value = self.emit_expr(element)?;
            let byte = self.new_temp();
            self.instruction(format!(
                "{byte} = zext i1 {} to i8",
                value.operand.expect("validated Boolean literal element")
            ));
            bytes.push(byte);
        }

        let len = elements.len() as u64;
        if len == 0 {
            return Ok(Value {
                ty: Ty::array(Ty::Bool),
                operand: Some("zeroinitializer".into()),
            });
        }

        let ptr = self.emit_array_alloc_call(&len.to_string(), &len.to_string());
        for (index, byte) in bytes.iter().enumerate() {
            let address = self.new_temp();
            self.instruction(format!(
                "{address} = getelementptr i8, ptr {ptr}, i64 {index}"
            ));
            self.instruction(format!("store i8 {byte}, ptr {address}"));
        }
        Ok(self.bool_array_descriptor(ptr, len.to_string()))
    }

    fn emit_bool_array_allocation(
        &mut self,
        len: &Expr,
        init: &Expr,
    ) -> Result<Value, Vec<BackendError>> {
        // Sable evaluates both operands before deciding whether allocation
        // succeeds. Keep the cap/null checks after those effects.
        let len = self
            .emit_expr(len)?
            .operand
            .expect("validated Boolean allocation length");
        let init = self
            .emit_expr(init)?
            .operand
            .expect("validated Boolean allocation initializer");
        let byte = self.new_temp();
        self.instruction(format!("{byte} = zext i1 {init} to i8"));

        let over_cap = self.new_temp();
        self.instruction(format!("{over_cap} = icmp ugt i64 {len}, {ARRAY_CAPACITY}"));
        self.emit_trap_branch(&over_cap, TRAP_ARRAY_OOM, 0, &len, "0");

        let empty = self.new_temp();
        self.instruction(format!("{empty} = icmp eq i64 {len}, 0"));
        let zero_label = self.new_label("array.zero");
        let alloc_label = self.new_label("array.alloc");
        let merge_label = self.new_label("array.ready");
        self.terminate(format!(
            "br i1 {empty}, label %{zero_label}, label %{alloc_label}"
        ));

        self.start_block(zero_label.clone());
        self.terminate(format!("br label %{merge_label}"));

        self.start_block(alloc_label);
        let ptr = self.emit_array_alloc_call(&len, &len);
        let fill_predecessor = self.current_label().to_owned();
        let fill_head = self.new_label("array.fill.head");
        let fill_body = self.new_label("array.fill.body");
        let fill_end = self.new_label("array.fill.end");
        self.terminate(format!("br label %{fill_head}"));

        self.start_block(fill_head.clone());
        let index = self.new_temp();
        self.instruction(format!(
            "{index} = phi i64 [ 0, %{fill_predecessor} ], [ %array.fill.next.{}, %{fill_body} ]",
            self.next_temp
        ));
        // Reserve the human-readable backedge name before using ordinary
        // temporaries again, so the phi references a unique SSA definition.
        let next = format!("%array.fill.next.{}", self.next_temp);
        self.next_temp += 1;
        let more = self.new_temp();
        self.instruction(format!("{more} = icmp ult i64 {index}, {len}"));
        self.terminate(format!(
            "br i1 {more}, label %{fill_body}, label %{fill_end}"
        ));

        self.start_block(fill_body.clone());
        let address = self.new_temp();
        self.instruction(format!(
            "{address} = getelementptr i8, ptr {ptr}, i64 {index}"
        ));
        self.instruction(format!("store i8 {byte}, ptr {address}"));
        self.instruction(format!("{next} = add i64 {index}, 1"));
        self.terminate(format!("br label %{fill_head}"));

        self.start_block(fill_end.clone());
        self.terminate(format!("br label %{merge_label}"));

        self.start_block(merge_label);
        let merged_ptr = self.new_temp();
        self.instruction(format!(
            "{merged_ptr} = phi ptr [ null, %{zero_label} ], [ {ptr}, %{fill_end} ]"
        ));
        Ok(self.bool_array_descriptor(merged_ptr, len))
    }

    fn emit_u32_array_literal(&mut self, elements: &[Expr]) -> Result<Value, Vec<BackendError>> {
        // Array literal elements are fully evaluated left-to-right before the
        // allocation attempt, matching the interpreter's observable order.
        let mut values = Vec::with_capacity(elements.len());
        for element in elements {
            values.push(
                self.emit_expr(element)?
                    .operand
                    .expect("validated `u32` literal element"),
            );
        }
        let len = elements.len() as u64;
        if len == 0 {
            return Ok(Value {
                ty: Ty::array(Ty::Int(IntTy::U32)),
                operand: Some("zeroinitializer".into()),
            });
        }
        let bytes = len * 4;
        let ptr = self.emit_array_alloc_call(&bytes.to_string(), &len.to_string());
        for (index, value) in values.iter().enumerate() {
            let address = self.new_temp();
            self.instruction(format!(
                "{address} = getelementptr i32, ptr {ptr}, i64 {index}"
            ));
            self.instruction(format!("store i32 {value}, ptr {address}, align 1"));
        }
        Ok(self.u32_array_descriptor(ptr, len.to_string()))
    }

    fn emit_u32_array_allocation(
        &mut self,
        len: &Expr,
        init: &Expr,
    ) -> Result<Value, Vec<BackendError>> {
        // Evaluate both operands before the defined OOM decision. The logical
        // element cap proves the subsequent byte multiplication fits i64.
        let len = self
            .emit_expr(len)?
            .operand
            .expect("validated `u32` allocation length");
        let init = self
            .emit_expr(init)?
            .operand
            .expect("validated `u32` allocation initializer");
        let over_cap = self.new_temp();
        self.instruction(format!("{over_cap} = icmp ugt i64 {len}, {ARRAY_CAPACITY}"));
        self.emit_trap_branch(&over_cap, TRAP_ARRAY_OOM, 0, &len, "0");

        let empty = self.new_temp();
        self.instruction(format!("{empty} = icmp eq i64 {len}, 0"));
        let zero_label = self.new_label("array.u32.zero");
        let alloc_label = self.new_label("array.u32.alloc");
        let merge_label = self.new_label("array.u32.ready");
        self.terminate(format!(
            "br i1 {empty}, label %{zero_label}, label %{alloc_label}"
        ));

        self.start_block(zero_label.clone());
        self.terminate(format!("br label %{merge_label}"));

        self.start_block(alloc_label);
        let bytes = self.new_temp();
        self.instruction(format!("{bytes} = mul i64 {len}, 4"));
        let ptr = self.emit_array_alloc_call(&bytes, &len);
        let fill_predecessor = self.current_label().to_owned();
        let fill_head = self.new_label("array.u32.fill.head");
        let fill_body = self.new_label("array.u32.fill.body");
        let fill_end = self.new_label("array.u32.fill.end");
        self.terminate(format!("br label %{fill_head}"));

        self.start_block(fill_head.clone());
        let index = self.new_temp();
        let next = format!("%array.u32.fill.next.{}", self.next_temp);
        self.next_temp += 1;
        self.instruction(format!(
            "{index} = phi i64 [ 0, %{fill_predecessor} ], [ {next}, %{fill_body} ]"
        ));
        let more = self.new_temp();
        self.instruction(format!("{more} = icmp ult i64 {index}, {len}"));
        self.terminate(format!(
            "br i1 {more}, label %{fill_body}, label %{fill_end}"
        ));

        self.start_block(fill_body.clone());
        let address = self.new_temp();
        self.instruction(format!(
            "{address} = getelementptr i32, ptr {ptr}, i64 {index}"
        ));
        self.instruction(format!("store i32 {init}, ptr {address}, align 1"));
        self.instruction(format!("{next} = add i64 {index}, 1"));
        self.terminate(format!("br label %{fill_head}"));

        self.start_block(fill_end.clone());
        self.terminate(format!("br label %{merge_label}"));
        self.start_block(merge_label);
        let merged_ptr = self.new_temp();
        self.instruction(format!(
            "{merged_ptr} = phi ptr [ null, %{zero_label} ], [ {ptr}, %{fill_end} ]"
        ));
        Ok(self.u32_array_descriptor(merged_ptr, len))
    }

    fn emit_array_alloc_call(&mut self, bytes: &str, logical_len: &str) -> String {
        let ptr = self.new_temp();
        self.instruction(format!(
            "{ptr} = call ptr @__sable_rt_array_alloc_v1(i64 {bytes})"
        ));
        let failed = self.new_temp();
        self.instruction(format!("{failed} = icmp eq ptr {ptr}, null"));
        self.emit_trap_branch(&failed, TRAP_ARRAY_OOM, 0, logical_len, "0");
        ptr
    }

    fn bool_array_descriptor(&mut self, ptr: String, len: String) -> Value {
        let with_ptr = self.new_temp();
        self.instruction(format!(
            "{with_ptr} = insertvalue {LLVM_ARRAY_BOOL} zeroinitializer, ptr {ptr}, 0"
        ));
        let descriptor = self.new_temp();
        self.instruction(format!(
            "{descriptor} = insertvalue {LLVM_ARRAY_BOOL} {with_ptr}, i64 {len}, 1"
        ));
        Value {
            ty: Ty::array(Ty::Bool),
            operand: Some(descriptor),
        }
    }

    fn u32_array_descriptor(&mut self, ptr: String, len: String) -> Value {
        let with_ptr = self.new_temp();
        self.instruction(format!(
            "{with_ptr} = insertvalue {LLVM_ARRAY_U32} zeroinitializer, ptr {ptr}, 0"
        ));
        let descriptor = self.new_temp();
        self.instruction(format!(
            "{descriptor} = insertvalue {LLVM_ARRAY_U32} {with_ptr}, i64 {len}, 1"
        ));
        Value {
            ty: Ty::array(Ty::Int(IntTy::U32)),
            operand: Some(descriptor),
        }
    }

    fn bool_slots_descriptor(&mut self, ptr: String, len: String) -> Value {
        let with_ptr = self.new_temp();
        self.instruction(format!(
            "{with_ptr} = insertvalue {LLVM_SLOTS_BOOL} zeroinitializer, ptr {ptr}, 0"
        ));
        let descriptor = self.new_temp();
        self.instruction(format!(
            "{descriptor} = insertvalue {LLVM_SLOTS_BOOL} {with_ptr}, i64 {len}, 1"
        ));
        Value {
            ty: Ty::slots(Ty::Bool),
            operand: Some(descriptor),
        }
    }

    fn emit_bool_slots_initializer(
        &mut self,
        expression: &Expr,
    ) -> Result<Value, Vec<BackendError>> {
        match &expression.kind {
            ExprKind::SlotOp {
                op: SlotOp::Alloc { .. },
                ..
            } => self.emit_expr(expression),
            ExprKind::Var(source) => {
                let Some(local) = self.locals.get(source) else {
                    return Err(vec![diag(
                        "internal.control_plan_invalid",
                        "native owner-slot move source has no local storage",
                        expression.span,
                        format!("missing local `{source}`"),
                    )]);
                };
                if !is_owned_bool_slots(&local.ty) {
                    return Err(vec![slots_unsupported(
                        expression.span,
                        format!("whole-owner move from `{source}`"),
                    )]);
                }
                let source_slot = local.slot.clone();
                let descriptor = self.new_temp();
                self.instruction(format!(
                    "{descriptor} = load {LLVM_SLOTS_BOOL}, ptr {source_slot}"
                ));
                // The source retains its exact cleanup candidate. Neutralize
                // its runtime storage immediately so that candidate is a
                // no-op and the allocation has exactly one executable owner.
                self.instruction(format!(
                    "store {LLVM_SLOTS_BOOL} zeroinitializer, ptr {source_slot}"
                ));
                Ok(Value {
                    ty: Ty::slots(Ty::Bool),
                    operand: Some(descriptor),
                })
            }
            _ => Err(vec![diag(
                "internal.control_plan_invalid",
                "native owner-slot initializer changed after validation",
                expression.span,
                "expected a retained allocation or direct local move",
            )]),
        }
    }

    fn emit_bool_slots_allocation(&mut self, len: &Expr) -> Result<Value, Vec<BackendError>> {
        let len = self
            .emit_expr(len)?
            .operand
            .expect("validated Boolean-slot allocation length");
        let over_cap = self.new_temp();
        self.instruction(format!("{over_cap} = icmp ugt i64 {len}, {ARRAY_CAPACITY}"));
        self.emit_trap_branch(&over_cap, TRAP_SLOTS_OOM, 0, &len, "0");

        let empty = self.new_temp();
        self.instruction(format!("{empty} = icmp eq i64 {len}, 0"));
        let zero_label = self.new_label("slots.bool.zero");
        let alloc_label = self.new_label("slots.bool.alloc");
        let merge_label = self.new_label("slots.bool.ready");
        self.terminate(format!(
            "br i1 {empty}, label %{zero_label}, label %{alloc_label}"
        ));

        self.start_block(zero_label.clone());
        self.terminate(format!("br label %{merge_label}"));

        self.start_block(alloc_label);
        // The logical cap makes this multiplication exact in i64. A cell is
        // two bytes because both fields are i8 and therefore have alignment 1.
        let bytes = self.new_temp();
        self.instruction(format!("{bytes} = mul i64 {len}, 2"));
        let ptr = self.new_temp();
        self.instruction(format!(
            "{ptr} = call ptr @__sable_rt_array_alloc_v1(i64 {bytes})"
        ));
        let failed = self.new_temp();
        self.instruction(format!("{failed} = icmp eq ptr {ptr}, null"));
        self.emit_trap_branch(&failed, TRAP_SLOTS_OOM, 0, &len, "0");

        let fill_predecessor = self.current_label().to_owned();
        let fill_head = self.new_label("slots.bool.fill.head");
        let fill_body = self.new_label("slots.bool.fill.body");
        let fill_end = self.new_label("slots.bool.fill.end");
        self.terminate(format!("br label %{fill_head}"));

        self.start_block(fill_head.clone());
        let index = self.new_temp();
        let next = format!("%slots.bool.fill.next.{}", self.next_temp);
        self.next_temp += 1;
        self.instruction(format!(
            "{index} = phi i64 [ 0, %{fill_predecessor} ], [ {next}, %{fill_body} ]"
        ));
        let more = self.new_temp();
        self.instruction(format!("{more} = icmp ult i64 {index}, {len}"));
        self.terminate(format!(
            "br i1 {more}, label %{fill_body}, label %{fill_end}"
        ));

        self.start_block(fill_body.clone());
        let cell = self.new_temp();
        self.instruction(format!(
            "{cell} = getelementptr {LLVM_SLOT_BOOL_CELL}, ptr {ptr}, i64 {index}"
        ));
        self.instruction(format!(
            "store {LLVM_SLOT_BOOL_CELL} zeroinitializer, ptr {cell}, align 1"
        ));
        self.instruction(format!("{next} = add i64 {index}, 1"));
        self.terminate(format!("br label %{fill_head}"));

        self.start_block(fill_end.clone());
        self.terminate(format!("br label %{merge_label}"));
        self.start_block(merge_label);
        let merged_ptr = self.new_temp();
        self.instruction(format!(
            "{merged_ptr} = phi ptr [ null, %{zero_label} ], [ {ptr}, %{fill_end} ]"
        ));
        Ok(self.bool_slots_descriptor(merged_ptr, len))
    }

    fn load_bool_slots_parts(&mut self, owner: &str) -> (String, String) {
        let slot = self
            .locals
            .get(owner)
            .expect("validated Boolean-slot local")
            .slot
            .clone();
        self.load_bool_slots_parts_from_slot(&slot)
    }

    fn load_bool_slots_parts_from_slot(&mut self, slot: &str) -> (String, String) {
        let descriptor = self.new_temp();
        self.instruction(format!("{descriptor} = load {LLVM_SLOTS_BOOL}, ptr {slot}"));
        let ptr = self.new_temp();
        self.instruction(format!(
            "{ptr} = extractvalue {LLVM_SLOTS_BOOL} {descriptor}, 0"
        ));
        let len = self.new_temp();
        self.instruction(format!(
            "{len} = extractvalue {LLVM_SLOTS_BOOL} {descriptor}, 1"
        ));
        (ptr, len)
    }

    fn emit_bool_slots_bounds_guard(&mut self, index: &str, len: &str) {
        let outside = self.new_temp();
        self.instruction(format!("{outside} = icmp uge i64 {index}, {len}"));
        self.emit_trap_branch(&outside, TRAP_SLOTS_OOB, 0, index, len);
    }

    fn bool_slot_cell_parts(&mut self, ptr: &str, index: &str) -> (String, String) {
        let cell = self.new_temp();
        self.instruction(format!(
            "{cell} = getelementptr {LLVM_SLOT_BOOL_CELL}, ptr {ptr}, i64 {index}"
        ));
        let tag = self.new_temp();
        self.instruction(format!(
            "{tag} = getelementptr {LLVM_SLOT_BOOL_CELL}, ptr {cell}, i32 0, i32 0"
        ));
        let payload = self.new_temp();
        self.instruction(format!(
            "{payload} = getelementptr {LLVM_SLOT_BOOL_CELL}, ptr {cell}, i32 0, i32 1"
        ));
        (tag, payload)
    }

    fn retained_bool_slot_owner(
        &self,
        action: &SlotAction,
        argument: &Expr,
        operation: &str,
    ) -> Result<String, Vec<BackendError>> {
        if action.payload() != &Ty::Bool {
            return Err(vec![slots_unsupported(
                action.span(),
                format!(
                    "retained `{operation}` payload `{}`",
                    action.payload().name()
                ),
            )]);
        }
        let Some(place) = action.container() else {
            return Err(vec![control_plan_backend_error(PlanError {
                span: action.span(),
                message: format!("retained `{operation}` action has no container"),
            })]);
        };
        let ExprKind::Borrow {
            array,
            field: None,
            mutable: true,
        } = &argument.kind
        else {
            return Err(vec![control_plan_backend_error(PlanError {
                span: argument.span,
                message: format!(
                    "retained `{operation}` container is not a direct mutable local borrow"
                ),
            })]);
        };
        if !place.is_root() || place.root() != array {
            return Err(vec![control_plan_backend_error(PlanError {
                span: action.span(),
                message: format!(
                    "retained `{operation}` container `{}` does not match local `{array}`",
                    place.render()
                ),
            })]);
        }
        let Some(local) = self.locals.get(array) else {
            return Err(vec![control_plan_backend_error(PlanError {
                span: argument.span,
                message: format!("retained `{operation}` local `{array}` has no LLVM slot"),
            })]);
        };
        if !is_owned_bool_slots(&local.ty) {
            return Err(vec![slots_unsupported(
                argument.span,
                format!("retained `{operation}` container `{array}`"),
            )]);
        }
        Ok(array.clone())
    }

    fn emit_bool_slot_operation(
        &mut self,
        expression: &Expr,
        action: &SlotAction,
    ) -> Result<Value, Vec<BackendError>> {
        let ExprKind::SlotOp { op, args, .. } = &expression.kind else {
            unreachable!("slot lowering is called only for slot operations")
        };
        match (op, action.kind()) {
            (SlotOp::Alloc { elem }, SlotActionKind::Alloc { .. }) => {
                if elem != &Ty::Bool || action.payload() != &Ty::Bool || args.len() != 1 {
                    return Err(vec![control_plan_backend_error(PlanError {
                        span: action.span(),
                        message:
                            "native slot allocation disagrees with its retained Boolean action"
                                .into(),
                    })]);
                }
                self.emit_bool_slots_allocation(&args[0])
            }
            (SlotOp::Take, SlotActionKind::Take { .. }) => {
                if args.len() != 2 || action.result_ty() != &Ty::Bool {
                    return Err(vec![control_plan_backend_error(PlanError {
                        span: action.span(),
                        message: "native slot take disagrees with its retained result or arity"
                            .into(),
                    })]);
                }
                // The container expression is first in source order. Resolve
                // and load its descriptor before evaluating the index.
                let owner = self.retained_bool_slot_owner(action, &args[0], "slot_take")?;
                let (ptr, len) = self.load_bool_slots_parts(&owner);
                let index = self
                    .emit_expr(&args[1])?
                    .operand
                    .expect("validated slot-take index");
                self.emit_bool_slots_bounds_guard(&index, &len);
                let (tag_ptr, payload_ptr) = self.bool_slot_cell_parts(&ptr, &index);
                let tag = self.new_temp();
                self.instruction(format!("{tag} = load i8, ptr {tag_ptr}, align 1"));
                let empty = self.new_temp();
                self.instruction(format!("{empty} = icmp eq i8 {tag}, 0"));
                self.emit_trap_branch(&empty, TRAP_SLOTS_EMPTY, 0, &index, &len);
                let payload = self.new_temp();
                self.instruction(format!("{payload} = load i8, ptr {payload_ptr}, align 1"));
                self.instruction(format!("store i8 0, ptr {tag_ptr}, align 1"));
                let value = self.new_temp();
                self.instruction(format!("{value} = trunc i8 {payload} to i1"));
                Ok(Value {
                    ty: Ty::Bool,
                    operand: Some(value),
                })
            }
            (SlotOp::Put, SlotActionKind::Put { staging, .. }) => {
                if args.len() != 3 || action.result_ty() != &Ty::Unit || !staging.is_root() {
                    return Err(vec![control_plan_backend_error(PlanError {
                        span: action.span(),
                        message: "native slot put disagrees with its retained result, arity, or staging identity"
                            .into(),
                    })]);
                }
                // Source order is container, index, incoming value. The value
                // enters the exact plan-owned scratch slot before either
                // bounds or occupancy is consulted.
                let owner = self.retained_bool_slot_owner(action, &args[0], "slot_put")?;
                let (ptr, len) = self.load_bool_slots_parts(&owner);
                let index = self
                    .emit_expr(&args[1])?
                    .operand
                    .expect("validated slot-put index");
                let incoming = self
                    .emit_expr(&args[2])?
                    .operand
                    .expect("validated slot-put value");
                let Some(scratch) = self.slot_put_staging_slots.get(staging).cloned() else {
                    return Err(vec![control_plan_backend_error(PlanError {
                        span: action.span(),
                        message: format!(
                            "native slot put has no storage for retained temporary `{}`",
                            staging.render()
                        ),
                    })]);
                };
                self.instruction(format!("store i1 {incoming}, ptr {scratch}"));
                self.emit_bool_slots_bounds_guard(&index, &len);
                let (tag_ptr, payload_ptr) = self.bool_slot_cell_parts(&ptr, &index);
                let tag = self.new_temp();
                self.instruction(format!("{tag} = load i8, ptr {tag_ptr}, align 1"));
                let occupied = self.new_temp();
                self.instruction(format!("{occupied} = icmp ne i8 {tag}, 0"));
                self.emit_trap_branch(&occupied, TRAP_SLOTS_OCCUPIED, 0, &index, &len);
                let staged = self.new_temp();
                self.instruction(format!("{staged} = load i1, ptr {scratch}"));
                let payload = self.new_temp();
                self.instruction(format!("{payload} = zext i1 {staged} to i8"));
                self.instruction(format!("store i8 {payload}, ptr {payload_ptr}, align 1"));
                self.instruction(format!("store i8 1, ptr {tag_ptr}, align 1"));
                Ok(Value {
                    ty: Ty::Unit,
                    operand: None,
                })
            }
            _ => Err(vec![control_plan_backend_error(PlanError {
                span: action.span(),
                message: "native owner-slot syntax no longer matches its retained action".into(),
            })]),
        }
    }

    fn emit_native_array_store(
        &mut self,
        array: &str,
        index: &Expr,
        value: &Expr,
    ) -> Result<(), Vec<BackendError>> {
        let ty = self
            .locals
            .get(array)
            .expect("validated native array local")
            .ty
            .clone();
        if ty.is_bool_array() {
            return self.emit_bool_array_store(array, index, value);
        }
        self.emit_u32_array_store(array, index, value)
    }

    fn emit_bool_array_store(
        &mut self,
        array: &str,
        index: &Expr,
        value: &Expr,
    ) -> Result<(), Vec<BackendError>> {
        // Store order is index, value, then bounds/place access.
        let index = self
            .emit_expr(index)?
            .operand
            .expect("validated Boolean array store index");
        let value = self
            .emit_expr(value)?
            .operand
            .expect("validated Boolean array store value");
        let byte = self.new_temp();
        self.instruction(format!("{byte} = zext i1 {value} to i8"));
        let (ptr, len) = self.load_bool_array_parts(array);
        self.emit_bool_array_bounds_guard(&index, &len);
        let address = self.new_temp();
        self.instruction(format!(
            "{address} = getelementptr i8, ptr {ptr}, i64 {index}"
        ));
        self.instruction(format!("store i8 {byte}, ptr {address}"));
        Ok(())
    }

    fn emit_u32_array_store(
        &mut self,
        array: &str,
        index: &Expr,
        value: &Expr,
    ) -> Result<(), Vec<BackendError>> {
        let index = self
            .emit_expr(index)?
            .operand
            .expect("validated `u32` array store index");
        let value = self
            .emit_expr(value)?
            .operand
            .expect("validated `u32` array store value");
        let (ptr, len) = self.load_u32_array_parts(array);
        self.emit_bool_array_bounds_guard(&index, &len);
        let address = self.new_temp();
        self.instruction(format!(
            "{address} = getelementptr i32, ptr {ptr}, i64 {index}"
        ));
        self.instruction(format!("store i32 {value}, ptr {address}, align 1"));
        Ok(())
    }

    fn load_bool_array_parts(&mut self, array: &str) -> (String, String) {
        let slot = self
            .locals
            .get(array)
            .expect("validated Boolean array local")
            .slot
            .clone();
        let descriptor = self.new_temp();
        self.instruction(format!("{descriptor} = load {LLVM_ARRAY_BOOL}, ptr {slot}"));
        let ptr = self.new_temp();
        self.instruction(format!(
            "{ptr} = extractvalue {LLVM_ARRAY_BOOL} {descriptor}, 0"
        ));
        let len = self.new_temp();
        self.instruction(format!(
            "{len} = extractvalue {LLVM_ARRAY_BOOL} {descriptor}, 1"
        ));
        (ptr, len)
    }

    fn load_u32_array_parts(&mut self, array: &str) -> (String, String) {
        let slot = self
            .locals
            .get(array)
            .expect("validated `u32` array local")
            .slot
            .clone();
        self.load_u32_array_parts_from_slot(&slot)
    }

    fn load_u32_array_parts_from_slot(&mut self, slot: &str) -> (String, String) {
        let descriptor = self.new_temp();
        self.instruction(format!("{descriptor} = load {LLVM_ARRAY_U32}, ptr {slot}"));
        let ptr = self.new_temp();
        self.instruction(format!(
            "{ptr} = extractvalue {LLVM_ARRAY_U32} {descriptor}, 0"
        ));
        let len = self.new_temp();
        self.instruction(format!(
            "{len} = extractvalue {LLVM_ARRAY_U32} {descriptor}, 1"
        ));
        (ptr, len)
    }

    fn emit_bool_array_bounds_guard(&mut self, index: &str, len: &str) {
        let outside = self.new_temp();
        self.instruction(format!("{outside} = icmp uge i64 {index}, {len}"));
        self.emit_trap_branch(&outside, TRAP_ARRAY_OOB, 0, index, len);
    }

    fn arm_cleanup(&mut self, name: &str) -> Result<(), Vec<BackendError>> {
        let place = Place::local(name);
        let Some(candidate) = self.control.candidate_for_place(&place) else {
            return Ok(());
        };
        let id = candidate.id();
        let scope = candidate.scope();
        let span = candidate.span();
        let Some(active) = self
            .cleanup_scopes
            .iter_mut()
            .find(|active| active.id == scope)
        else {
            return Err(vec![diag(
                "internal.control_plan_invalid",
                "cleanup candidate is outside the active lexical scopes",
                span,
                format!("`{name}` was assigned a non-active scope"),
            )]);
        };
        if !active.reached.insert(id) {
            return Err(vec![diag(
                "internal.control_plan_invalid",
                "cleanup candidate was armed twice",
                span,
                format!("`{name}` has one declaration and must have one cleanup identity"),
            )]);
        }
        Ok(())
    }

    fn emit_return_cleanups(&mut self, span: Span) -> Result<(), Vec<BackendError>> {
        let scope = self
            .cleanup_scopes
            .last()
            .expect("return has an active lexical scope")
            .id;
        let routes = self
            .control
            .explicit_return(span, scope)
            .map_err(|error| vec![control_plan_backend_error(error)])?;
        let lexical = routes.lexical().clone();
        let frame = routes.frame().clone();
        self.emit_cleanup_route(&lexical)?;
        self.emit_cleanup_route(&frame)?;
        Ok(())
    }

    fn emit_implicit_return_cleanups(&mut self) -> Result<(), Vec<BackendError>> {
        let routes = self.control.implicit_return();
        let lexical = routes.lexical().clone();
        let frame = routes.frame().clone();
        self.emit_cleanup_route(&lexical)?;
        self.emit_cleanup_route(&frame)
    }

    fn emit_assignment_previous(
        &mut self,
        action: &AssignmentAction,
    ) -> Result<(), Vec<BackendError>> {
        let Some(drop) = action.previous() else {
            return Ok(());
        };
        if !self
            .cleanup_scopes
            .iter()
            .rev()
            .any(|scope| scope.reached.contains(&drop))
        {
            return Err(vec![diag(
                "internal.control_plan_invalid",
                "assignment reached an inactive cleanup candidate",
                action.span(),
                format!(
                    "old destination `{}` was not reached on this structured path",
                    action.destination().render()
                ),
            )]);
        }
        let candidate = self.control.candidate(drop);
        if candidate.place() != action.destination() || candidate.ty() != action.ty() {
            return Err(vec![diag(
                "internal.control_plan_invalid",
                "assignment disagrees with its prior cleanup candidate",
                action.span(),
                "destination place and type must match the candidate exactly",
            )]);
        }
        self.emit_drop_candidate(drop)
    }

    fn emit_cleanup_route(&mut self, route: &ExitRoute) -> Result<(), Vec<BackendError>> {
        // The active registry is path-sensitive but stores reachability only;
        // the plan is the sole source of candidate identity, place, type, and
        // order. Candidates after an early return are absent here, and moved
        // places remain registered for their null-safe no-op drop.
        let candidates = route
            .drops()
            .iter()
            .filter(|drop| {
                self.cleanup_scopes
                    .iter()
                    .rev()
                    .any(|scope| scope.reached.contains(*drop))
            })
            .copied()
            .collect::<Vec<_>>();
        for candidate in candidates {
            self.emit_drop_candidate(candidate)?;
        }
        Ok(())
    }

    fn emit_drop_candidate(&mut self, drop: DropId) -> Result<(), Vec<BackendError>> {
        let candidate = self.control.candidate(drop);
        let place = candidate.place().clone();
        let action = candidate.drop_action().clone();
        let span = candidate.span();
        if !place.is_root() {
            return Err(vec![diag(
                "internal.control_plan_invalid",
                "LLVM cleanup candidate is not a local",
                span,
                format!("planned cleanup `{}` is not a root place", place.render()),
            )]);
        }
        let name = place.root();
        match action.recipe() {
            ValueDropRecipe::DropClass(class) => self.emit_fixed_class_drop(name, class.class())?,
            ValueDropRecipe::ReleaseArray { element } if element == &Ty::Bool => {
                self.emit_bool_array_drop(name)
            }
            ValueDropRecipe::ReleaseArray { element } if element == &Ty::Int(IntTy::U32) => {
                self.emit_u32_array_drop(name)
            }
            ValueDropRecipe::ReleaseSlots { payload, occupied }
                if payload == &Ty::Bool
                    && occupied.is_none()
                    && is_owned_bool_slots(action.ty()) =>
            {
                self.emit_bool_slots_drop(name)
            }
            ValueDropRecipe::ReleaseSlots { .. } => {
                return Err(vec![diag(
                    "backend.slots_cleanup_unsupported",
                    "LLVM cannot lower this owner-slot cleanup recipe",
                    span,
                    format!(
                        "`{name}` has cleanup-bearing type `{}`; only scalar Boolean occupied cells are admitted",
                        action.ty().name()
                    ),
                )]);
            }
            ValueDropRecipe::DropPresent(payload)
                if matches!(
                    payload.recipe(),
                    ValueDropRecipe::ReleaseArray { element } if element == &Ty::Bool
                ) && is_affine_bool_option(action.ty()) =>
            {
                self.emit_affine_bool_option_drop(name)
            }
            ValueDropRecipe::ReleaseArray { .. } | ValueDropRecipe::DropPresent(_) => {
                return Err(vec![diag(
                    "backend.control_plan_unsupported",
                    "LLVM cannot lower a planned cleanup candidate",
                    span,
                    format!("`{name}` has cleanup-bearing type `{}`", action.ty().name()),
                )]);
            }
        }
        Ok(())
    }

    fn emit_bool_array_drop(&mut self, array: &str) {
        let (ptr, _) = self.load_bool_array_parts(array);
        let empty = self.new_temp();
        self.instruction(format!("{empty} = icmp eq ptr {ptr}, null"));
        let free_label = self.new_label("array.free");
        let done_label = self.new_label("array.free.done");
        self.terminate(format!(
            "br i1 {empty}, label %{done_label}, label %{free_label}"
        ));
        self.start_block(free_label);
        self.instruction(format!("call void @__sable_rt_array_free_v1(ptr {ptr})"));
        self.terminate(format!("br label %{done_label}"));
        self.start_block(done_label);
    }

    fn emit_u32_array_drop(&mut self, array: &str) {
        let (ptr, _) = self.load_u32_array_parts(array);
        let empty = self.new_temp();
        self.instruction(format!("{empty} = icmp eq ptr {ptr}, null"));
        let free_label = self.new_label("array.u32.free");
        let done_label = self.new_label("array.u32.free.done");
        self.terminate(format!(
            "br i1 {empty}, label %{done_label}, label %{free_label}"
        ));
        self.start_block(free_label);
        self.instruction(format!("call void @__sable_rt_array_free_v1(ptr {ptr})"));
        self.terminate(format!("br label %{done_label}"));
        self.start_block(done_label);
    }

    fn emit_bool_slots_drop(&mut self, owner: &str) {
        let slot = self
            .locals
            .get(owner)
            .expect("validated Boolean-slot cleanup local")
            .slot
            .clone();
        let (ptr, len) = self.load_bool_slots_parts_from_slot(&slot);
        let absent = self.new_temp();
        self.instruction(format!("{absent} = icmp eq ptr {ptr}, null"));
        let scan_start = self.new_label("slots.bool.drop.start");
        let scan_head = self.new_label("slots.bool.drop.head");
        let scan_body = self.new_label("slots.bool.drop.body");
        let clear = self.new_label("slots.bool.drop.clear");
        let latch = self.new_label("slots.bool.drop.latch");
        let free = self.new_label("slots.bool.drop.free");
        let done = self.new_label("slots.bool.drop.done");
        self.terminate(format!(
            "br i1 {absent}, label %{done}, label %{scan_start}"
        ));

        self.start_block(scan_start.clone());
        self.terminate(format!("br label %{scan_head}"));

        self.start_block(scan_head.clone());
        let cursor = self.new_temp();
        let next = format!("%slots.bool.drop.next.{}", self.next_temp);
        self.next_temp += 1;
        self.instruction(format!(
            "{cursor} = phi i64 [ {len}, %{scan_start} ], [ {next}, %{latch} ]"
        ));
        let more = self.new_temp();
        self.instruction(format!("{more} = icmp ugt i64 {cursor}, 0"));
        self.terminate(format!("br i1 {more}, label %{scan_body}, label %{free}"));

        self.start_block(scan_body);
        self.instruction(format!("{next} = sub i64 {cursor}, 1"));
        let cell = self.new_temp();
        self.instruction(format!(
            "{cell} = getelementptr {LLVM_SLOT_BOOL_CELL}, ptr {ptr}, i64 {next}"
        ));
        let tag_ptr = self.new_temp();
        self.instruction(format!(
            "{tag_ptr} = getelementptr {LLVM_SLOT_BOOL_CELL}, ptr {cell}, i32 0, i32 0"
        ));
        let tag = self.new_temp();
        self.instruction(format!("{tag} = load i8, ptr {tag_ptr}, align 1"));
        let occupied = self.new_temp();
        self.instruction(format!("{occupied} = icmp ne i8 {tag}, 0"));
        self.terminate(format!("br i1 {occupied}, label %{clear}, label %{latch}"));

        self.start_block(clear);
        // Neutralize before recursively destroying the payload. Boolean has
        // no child action, but retaining this order makes the cell lifecycle
        // identical to the recursive recipe and keeps later widening honest.
        self.instruction(format!("store i8 0, ptr {tag_ptr}, align 1"));
        self.terminate(format!("br label %{latch}"));

        self.start_block(latch.clone());
        self.terminate(format!("br label %{scan_head}"));

        self.start_block(free);
        self.instruction(format!("call void @__sable_rt_array_free_v1(ptr {ptr})"));
        self.terminate(format!("br label %{done}"));

        self.start_block(done);
        self.instruction(format!(
            "store {LLVM_SLOTS_BOOL} zeroinitializer, ptr {slot}"
        ));
    }

    fn emit_fixed_class_drop(
        &mut self,
        object: &str,
        class: usize,
    ) -> Result<(), Vec<BackendError>> {
        let slot = self
            .locals
            .get(object)
            .expect("validated fixed-owner class local")
            .slot
            .clone();
        self.emit_fixed_class_drop_from_slot(&slot, class)
    }

    fn emit_fixed_class_drop_from_slot(
        &mut self,
        slot: &str,
        class: usize,
    ) -> Result<(), Vec<BackendError>> {
        let Some(declaration) = self.program.classes.get(class) else {
            return Err(vec![diag(
                "backend.control_plan_unsupported",
                "LLVM cannot resolve a planned concrete-class cleanup",
                self.function.name_span,
                format!("class index {class} is outside the checked program"),
            )]);
        };
        let Some(drop_plan) = self.class_drop_plans.get(class).cloned() else {
            return Err(vec![control_plan_backend_error(PlanError {
                span: declaration.name_span,
                message: format!(
                    "control program has no class-drop plan for concrete class index {class}"
                ),
            })]);
        };
        self.emit_fixed_class_drop_from_slot_with_plan(slot, class, &drop_plan)
    }

    fn class_drop_for_action(
        &self,
        action: &ClassDropAction,
        use_span: Span,
    ) -> Result<ClassDropPlan, Vec<BackendError>> {
        let Some(declaration) = self.program.classes.get(action.class()) else {
            return Err(vec![control_plan_backend_error(PlanError {
                span: use_span,
                message: format!(
                    "cleanup action names missing concrete class index {}",
                    action.class()
                ),
            })]);
        };
        let Some(drop_plan) = self.class_drop_plans.get(action.class()).cloned() else {
            return Err(vec![control_plan_backend_error(PlanError {
                span: use_span,
                message: format!(
                    "control program has no class-drop plan for cleanup action index {}",
                    action.class()
                ),
            })]);
        };
        drop_plan
            .validate(action.class(), declaration)
            .and_then(|()| drop_plan.validate_terminal_trap_route())
            .map_err(|error| vec![control_plan_backend_error(error)])?;
        if action.terminal_trap_route() != drop_plan.terminal_trap_route() {
            return Err(vec![control_plan_backend_error(PlanError {
                span: use_span,
                message: "LLVM cleanup action no longer links its exact terminal class-drop recipe"
                    .into(),
            })]);
        }
        Ok(drop_plan)
    }

    fn emit_fixed_class_drop_from_slot_with_plan(
        &mut self,
        slot: &str,
        class: usize,
        drop_plan: &ClassDropPlan,
    ) -> Result<(), Vec<BackendError>> {
        let Some(declaration) = self.program.classes.get(class) else {
            return Err(vec![diag(
                "backend.control_plan_unsupported",
                "LLVM cannot resolve a planned concrete-class cleanup",
                self.function.name_span,
                format!("class index {class} is outside the checked program"),
            )]);
        };
        drop_plan
            .validate(class, declaration)
            .and_then(|()| drop_plan.validate_terminal_trap_route())
            .map_err(|error| vec![control_plan_backend_error(error)])?;

        // No phase may unwind into the remaining suffix. The invariant and
        // empty-deinitializer phases below are erased, while recursive field
        // cleanup emits only native null-safe cleanup; any unsupported phase
        // is rejected instead of being silently skipped.
        for phase in drop_plan.phases() {
            match phase {
                ClassDropPhase::CheckInvariant => {
                    self.instruction(format!(
                        "; class-drop invariant for `{}` erased after verification",
                        drop_plan.class_name()
                    ));
                }
                ClassDropPhase::RunDeinitializer(owner) => {
                    let body = declaration.deinit.as_deref().ok_or_else(|| {
                        vec![control_plan_backend_error(PlanError {
                            span: declaration.span,
                            message: format!(
                                "class-drop phase {} no longer has a deinitializer body",
                                owner.render()
                            ),
                        })]
                    })?;
                    if !body.is_empty() {
                        return Err(vec![diag(
                            "backend.control_plan_unsupported",
                            "LLVM cannot execute a planned class deinitializer",
                            declaration.span,
                            format!(
                                "{} has a non-empty body; the fixed native class subset admits only absent or empty destruction",
                                owner.render()
                            ),
                        )]);
                    }
                    self.instruction(format!(
                        "; empty class-drop deinitializer {}",
                        owner.render()
                    ));
                }
                ClassDropPhase::DropField(field) => {
                    if field.must_consume() {
                        return Err(vec![diag(
                            "backend.control_plan_unsupported",
                            "LLVM cannot lower a must-consume class field cleanup",
                            field.span(),
                            format!(
                                "planned field `{}` carries an erased authority",
                                field.name()
                            ),
                        )]);
                    }
                    let field_slot = self.emit_class_field_slot(class, slot, field.index());
                    match field.drop_action().map(|action| action.recipe()) {
                        Some(ValueDropRecipe::ReleaseArray { element })
                            if element == &Ty::Int(IntTy::U32) =>
                        {
                            self.emit_u32_array_drop_from_slot(&field_slot);
                        }
                        Some(ValueDropRecipe::DropClass(child)) => {
                            self.emit_fixed_class_drop_from_slot(&field_slot, child.class())?;
                        }
                        Some(ValueDropRecipe::ReleaseSlots { .. }) => {
                            return Err(vec![diag(
                                "backend.slots_cleanup_unsupported",
                                "LLVM cannot lower owner-slot class-field cleanup",
                                field.span(),
                                format!(
                                    "field `{}` has cleanup-bearing type `{}`",
                                    field.name(),
                                    field.ty().name()
                                ),
                            )]);
                        }
                        None if matches!(field.ty(), Ty::Int(_)) => {}
                        Some(ValueDropRecipe::ReleaseArray { .. })
                        | Some(ValueDropRecipe::DropPresent(_))
                        | None => {
                            return Err(vec![diag(
                                "backend.control_plan_unsupported",
                                "LLVM cannot lower a planned class-field cleanup",
                                field.span(),
                                format!(
                                    "field `{}` has unsupported cleanup type `{}`",
                                    field.name(),
                                    field.ty().name()
                                ),
                            )]);
                        }
                    }
                }
            }
        }
        self.instruction(format!(
            "store {} zeroinitializer, ptr {slot}",
            llvm_class_ty(class)
        ));
        Ok(())
    }

    fn emit_u32_array_drop_from_slot(&mut self, field_slot: &str) {
        let (ptr, _) = self.load_u32_array_parts_from_slot(field_slot);
        let empty = self.new_temp();
        self.instruction(format!("{empty} = icmp eq ptr {ptr}, null"));
        let free_label = self.new_label("class.free");
        let done_label = self.new_label("class.free.done");
        self.terminate(format!(
            "br i1 {empty}, label %{done_label}, label %{free_label}"
        ));
        self.start_block(free_label);
        self.instruction(format!("call void @__sable_rt_array_free_v1(ptr {ptr})"));
        self.terminate(format!("br label %{done_label}"));
        self.start_block(done_label);
        self.instruction(format!(
            "store {LLVM_ARRAY_U32} zeroinitializer, ptr {field_slot}"
        ));
    }

    fn emit_affine_bool_option_drop(&mut self, option: &str) {
        let slot = self
            .locals
            .get(option)
            .expect("validated affine-option local")
            .slot
            .clone();
        let aggregate = self.new_temp();
        self.instruction(format!(
            "{aggregate} = load {LLVM_AFFINE_OPTION_BOOL_ARRAY}, ptr {slot}"
        ));
        let tag = self.new_temp();
        self.instruction(format!(
            "{tag} = extractvalue {LLVM_AFFINE_OPTION_BOOL_ARRAY} {aggregate}, 0"
        ));
        let present = self.new_temp();
        self.instruction(format!("{present} = icmp eq i8 {tag}, 1"));
        let inspect_label = self.new_label("option.drop.present");
        let free_label = self.new_label("option.drop.free");
        let done_label = self.new_label("option.drop.done");
        self.terminate(format!(
            "br i1 {present}, label %{inspect_label}, label %{done_label}"
        ));

        self.start_block(inspect_label);
        let payload = self.new_temp();
        self.instruction(format!(
            "{payload} = extractvalue {LLVM_AFFINE_OPTION_BOOL_ARRAY} {aggregate}, 1"
        ));
        let ptr = self.new_temp();
        self.instruction(format!(
            "{ptr} = extractvalue {LLVM_ARRAY_BOOL} {payload}, 0"
        ));
        let empty = self.new_temp();
        self.instruction(format!("{empty} = icmp eq ptr {ptr}, null"));
        self.terminate(format!(
            "br i1 {empty}, label %{done_label}, label %{free_label}"
        ));

        self.start_block(free_label);
        self.instruction(format!("call void @__sable_rt_array_free_v1(ptr {ptr})"));
        self.terminate(format!("br label %{done_label}"));
        self.start_block(done_label);
    }

    fn emit_expr(&mut self, expression: &Expr) -> Result<Value, Vec<BackendError>> {
        let slot_action = if matches!(expression.kind, ExprKind::SlotOp { .. }) {
            Some(self.slot_action_preflight(expression)?)
        } else {
            self.consume_expression_trap_sites(expression)?;
            None
        };
        match &expression.kind {
            ExprKind::SlotOp { .. } => self.emit_bool_slot_operation(
                expression,
                slot_action
                    .as_ref()
                    .expect("slot-operation preflight produced its exact action"),
            ),
            ExprKind::IntLit(value) => Ok(Value {
                ty: expression.ty.clone().expect("validated literal type"),
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
                let ty = local.ty.clone();
                let slot = local.slot.clone();
                let temp = self.new_temp();
                let loaded =
                    require_llvm_ty(ty.clone(), expression.span, &format!("local `{name}`"))?;
                self.instruction(format!("{temp} = load {loaded}, ptr {slot}"));
                Ok(Value {
                    ty,
                    operand: Some(temp),
                })
            }
            ExprKind::Index { array, index, .. } => {
                // Index expression effects precede place access and its
                // language-defined bounds trap.
                let index = self
                    .emit_expr(index)?
                    .operand
                    .expect("validated Boolean array index");
                let ty = self.locals[array].ty.clone();
                if ty.is_bool_array() {
                    let (ptr, len) = self.load_bool_array_parts(array);
                    self.emit_bool_array_bounds_guard(&index, &len);
                    let address = self.new_temp();
                    self.instruction(format!(
                        "{address} = getelementptr i8, ptr {ptr}, i64 {index}"
                    ));
                    let byte = self.new_temp();
                    self.instruction(format!("{byte} = load i8, ptr {address}"));
                    let value = self.new_temp();
                    self.instruction(format!("{value} = trunc i8 {byte} to i1"));
                    Ok(Value {
                        ty: Ty::Bool,
                        operand: Some(value),
                    })
                } else {
                    let (ptr, len) = self.load_u32_array_parts(array);
                    self.emit_bool_array_bounds_guard(&index, &len);
                    let address = self.new_temp();
                    self.instruction(format!(
                        "{address} = getelementptr i32, ptr {ptr}, i64 {index}"
                    ));
                    let value = self.new_temp();
                    self.instruction(format!("{value} = load i32, ptr {address}, align 1"));
                    Ok(Value {
                        ty: Ty::Int(IntTy::U32),
                        operand: Some(value),
                    })
                }
            }
            ExprKind::Len { array } => {
                let ty = self.locals[array].ty.clone();
                let (_, len) = if is_owned_bool_slots(&ty) {
                    self.load_bool_slots_parts(array)
                } else if ty.is_bool_array() {
                    self.load_bool_array_parts(array)
                } else {
                    self.load_u32_array_parts(array)
                };
                Ok(Value {
                    ty: Ty::Int(IntTy::U64),
                    operand: Some(len),
                })
            }
            ExprKind::ClassFieldLen { obj, field } => {
                let (_, len) = self.load_class_u32_array_parts(obj, field);
                Ok(Value {
                    ty: Ty::Int(IntTy::U64),
                    operand: Some(len),
                })
            }
            ExprKind::ClassFieldIndex {
                obj, field, index, ..
            } => {
                let index = self
                    .emit_expr(index)?
                    .operand
                    .expect("validated class array-field index");
                let (ptr, len) = self.load_class_u32_array_parts(obj, field);
                self.emit_bool_array_bounds_guard(&index, &len);
                let address = self.new_temp();
                self.instruction(format!(
                    "{address} = getelementptr i32, ptr {ptr}, i64 {index}"
                ));
                let value = self.new_temp();
                self.instruction(format!("{value} = load i32, ptr {address}, align 1"));
                Ok(Value {
                    ty: Ty::Int(IntTy::U32),
                    operand: Some(value),
                })
            }
            ExprKind::ClassField { obj, field, .. } => {
                let (field_ty, field_slot) = self.class_field_slot(obj, field);
                let loaded = require_llvm_ty(
                    field_ty.clone(),
                    expression.span,
                    &format!("class field `{field}`"),
                )?;
                let value = self.new_temp();
                self.instruction(format!("{value} = load {loaded}, ptr {field_slot}"));
                Ok(Value {
                    ty: field_ty,
                    operand: Some(value),
                })
            }
            ExprKind::SelfField { field } => {
                let (field_ty, field_slot) = self.class_field_slot("self", field);
                let loaded = require_llvm_ty(
                    field_ty.clone(),
                    expression.span,
                    &format!("class field `{field}`"),
                )?;
                let value = self.new_temp();
                self.instruction(format!("{value} = load {loaded}, ptr {field_slot}"));
                Ok(Value {
                    ty: field_ty,
                    operand: Some(value),
                })
            }
            ExprKind::RecordLit { record, args, .. } => {
                let Ty::Record(record_index) = expression
                    .ty
                    .clone()
                    .expect("validated record construction has a nominal type")
                else {
                    unreachable!("validated record construction type")
                };
                self.support.require_record(record_index);
                let declaration = self.program.records[record_index].clone();
                debug_assert_eq!(declaration.name.as_str(), record.as_str());

                // Every lowered record field is an integer, so zero is a valid defined
                // seed. Every declared field is then overwritten in source
                // order; evaluating each argument before the next preserves
                // Sable's left-to-right call/trap order.
                let record_ty = llvm_record_ty(record_index);
                let mut aggregate = "zeroinitializer".to_string();
                for (index, (argument, field)) in args.iter().zip(&declaration.fields).enumerate() {
                    let value = self.emit_expr(argument)?;
                    let field_ty = require_llvm_ty(
                        field.ty.clone(),
                        argument.span,
                        &format!("record field `{}`", field.name),
                    )?;
                    let next = self.new_temp();
                    self.instruction(format!(
                        "{next} = insertvalue {record_ty} {aggregate}, {field_ty} {}, {index}",
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
                let (record_index, slot) = match &local.ty {
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
                self.support.require_record(*record_index);
                let declaration = self.program.records[*record_index].clone();
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
                if expression.ty.as_ref() != Some(&declaration_field.ty) {
                    return Err(vec![unsupported(
                        expression.span,
                        format!(
                            "record `{}.{field}` is annotated `{}` instead of `{}`",
                            declaration.name,
                            expression
                                .ty
                                .as_ref()
                                .map_or_else(|| "<missing>".to_string(), |ty| ty.name()),
                            declaration_field.ty.name()
                        ),
                    )]);
                }
                let record_ty = llvm_record_ty(*record_index);
                let aggregate = self.new_temp();
                self.instruction(format!("{aggregate} = load {record_ty}, ptr {slot}"));
                let value = self.new_temp();
                self.instruction(format!(
                    "{value} = extractvalue {record_ty} {aggregate}, {field_index}"
                ));
                Ok(Value {
                    ty: declaration_field.ty.clone(),
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
                    ty: Ty::option(Ty::Bool),
                    operand: Some(result),
                })
            }
            ExprKind::NoneE => {
                self.support.require_option_bool();
                Ok(Value {
                    ty: Ty::option(Ty::Bool),
                    operand: Some("zeroinitializer".into()),
                })
            }
            ExprKind::IsSome { operand } => {
                if operand.ty.as_ref().is_some_and(Ty::is_affine_option) {
                    return self.emit_affine_option_is_some(operand);
                }
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
                let lowered = self.emit_call_arguments(&function.params, args)?;
                let returned = require_llvm_ty(
                    function.ret.clone(),
                    expression.span,
                    &format!("the return type of `{}`", function.name),
                )?;
                let call = format!(
                    "call {returned} @{}({})",
                    mangle(function)?,
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
                        ty: function.ret.clone(),
                        operand: Some(temp),
                    })
                }
            }
            ExprKind::MethodCall {
                recv, method, args, ..
            } => {
                let (class, receiver) = self.class_base_pointer(recv);
                let declaration = &self.program.classes[class];
                let method = declaration
                    .methods
                    .iter()
                    .find(|candidate| candidate.f.name == *method)
                    .expect("validated native method")
                    .f
                    .clone();
                debug_assert!(!matches!(method.ret, Ty::Class(_)));
                let mut lowered = Vec::with_capacity(args.len() + 1);
                lowered.push(format!("ptr {receiver}"));
                lowered.extend(self.emit_call_arguments(&method.params, args)?);
                let returned = require_llvm_ty(
                    method.ret.clone(),
                    expression.span,
                    &format!("the result of method `{}`", method.name),
                )?;
                let call = format!(
                    "call {returned} @{}({})",
                    mangle_method(class, &method)?,
                    lowered.join(", ")
                );
                if method.ret == Ty::Unit {
                    self.instruction(call);
                    Ok(Value {
                        ty: Ty::Unit,
                        operand: None,
                    })
                } else {
                    let result = self.new_temp();
                    self.instruction(format!("{result} = {call}"));
                    Ok(Value {
                        ty: method.ret,
                        operand: Some(result),
                    })
                }
            }
            ExprKind::Borrow { array, field, .. }
                if expression
                    .ty
                    .as_ref()
                    .is_some_and(|ty| ty.as_class_borrow().is_some()) =>
            {
                let (_, pointer) = if let Some(field) = field {
                    let (field_ty, slot) = self.class_field_slot(array, field);
                    let Ty::Class(class) = field_ty else {
                        unreachable!("validated class-valued field borrow")
                    };
                    (class, slot)
                } else {
                    self.class_base_pointer(array)
                };
                Ok(Value {
                    ty: expression.ty.clone().expect("validated class borrow type"),
                    operand: Some(pointer),
                })
            }
            ExprKind::Borrow { array, field, .. } => {
                let slot = if let Some(field) = field {
                    self.class_field_slot(array, field).1
                } else {
                    self.locals
                        .get(array)
                        .expect("validated named array borrow")
                        .slot
                        .clone()
                };
                let borrowed = expression.ty.clone().expect("validated borrow type");
                let descriptor_ty =
                    require_llvm_ty(borrowed.clone(), expression.span, "array borrow")?;
                let descriptor = self.new_temp();
                self.instruction(format!("{descriptor} = load {descriptor_ty}, ptr {slot}"));
                Ok(Value {
                    ty: borrowed,
                    operand: Some(descriptor),
                })
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
                let compared = require_llvm_ty(lhs.ty, expression.span, "comparison operand")?;
                let temp = self.new_temp();
                self.instruction(format!(
                    "{temp} = icmp {predicate} {compared} {}, {}",
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
                        integer_llvm_ty(source),
                        integer_llvm_ty(*target)
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
            ExprKind::OptTake { option, .. } => Err(vec![affine_option_take_position(
                expression.span,
                option,
                "expression",
            )]),
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
        let llvm_integer = integer_llvm_ty(integer);
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
        let llvm_integer = integer_llvm_ty(integer);
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
        let llvm_integer = integer_llvm_ty(integer);

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
        let llvm_integer = integer_llvm_ty(integer);
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
        let llvm_integer = integer_llvm_ty(integer);
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
        let source_ty = integer_llvm_ty(source);
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
            integer_llvm_ty(target)
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
                integer_llvm_ty(integer)
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
            Stmt::Decl { name, ty, .. } => declarations.push((name.clone(), ty.clone())),
            Stmt::VarDecl { name, ty, .. } => {
                declarations.push((name.clone(), ty.clone().expect("validated inferred type")));
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

fn find_declared_type(statements: &[Stmt], target: &str) -> Option<Ty> {
    for statement in statements {
        match statement {
            Stmt::Decl { name, ty, .. } if name == target => return Some(ty.clone()),
            Stmt::VarDecl { name, ty, .. } if name == target => return ty.clone(),
            Stmt::If {
                then_block,
                else_block,
                ..
            } => {
                if let Some(ty) = find_declared_type(then_block, target) {
                    return Some(ty);
                }
                if let Some(ty) = else_block
                    .as_deref()
                    .and_then(|block| find_declared_type(block, target))
                {
                    return Some(ty);
                }
            }
            Stmt::While { body, .. } | Stmt::Unsafe { body, .. } => {
                if let Some(ty) = find_declared_type(body, target) {
                    return Some(ty);
                }
            }
            _ => {}
        }
    }
    None
}

fn emit_main_bridge(function: &Fn, out: &mut String) -> Result<(), Vec<BackendError>> {
    let symbol = mangle(function)?;
    out.push_str("define i32 @main() {\nentry:\n");
    if function.ret == Ty::Unit {
        out.push_str(&format!("  call void @{symbol}()\n  ret i32 0\n"));
    } else {
        out.push_str(&format!(
            "  %result = call i32 @{symbol}()\n  ret i32 %result\n"
        ));
    }
    out.push_str("}\n");
    Ok(())
}

/// The name of the disagreement between a backend gate and a backend
/// lowering: the gate admitted a shape the lowering has no spelling for.
///
/// It is `internal.` because no source program reaches it — the `require_*`
/// gates refuse first, under their own names and with their own spans. What
/// it buys is that when the two do disagree, the compile ends in a
/// diagnostic naming the shape and pointing at the declaration, rather than
/// in a process abort that says neither.
const LOWERING_GAP: &str = "internal.backend.type_lowering";

fn lowering_gap(span: Span, role: &str, ty: &Ty, what: &str) -> BackendError {
    diag(
        LOWERING_GAP,
        format!("no LLVM {what} for a shape the backend admitted"),
        span,
        format!(
            "{role} has type `{}`, which a backend gate accepted and the {what} lowering cannot spell",
            ty.name()
        ),
    )
}

/// The LLVM value type for a shape, or `None` for one the backend does not
/// represent.
///
/// Total, so that the answer for an unrepresented shape is a value rather
/// than a panic. `require_llvm_ty` turns that answer into a spanned
/// diagnostic; the `require_*` gates are what a source program actually
/// meets.
pub(crate) fn llvm_ty(ty: Ty) -> Option<String> {
    Some(match ty {
        Ty::Int(IntTy::TParam(_)) => return None,
        Ty::Int(integer) => format!("i{}", integer.bits()),
        Ty::Bool => "i1".into(),
        Ty::Unit => "void".into(),
        Ty::Option(payload) if payload.as_ref() == &Ty::Bool => LLVM_OPTION_BOOL.into(),
        ty if ty.is_bool_array() => LLVM_ARRAY_BOOL.into(),
        ty if is_u32_array(&ty.clone()) => LLVM_ARRAY_U32.into(),
        ty if is_affine_bool_option(&ty.clone()) => LLVM_AFFINE_OPTION_BOOL_ARRAY.into(),
        ref ty if is_owned_bool_slots(ty) => LLVM_SLOTS_BOOL.into(),
        Ty::Class(class) => llvm_class_ty(class),
        // A class borrow is a pointer whichever way it is bound: the IR type
        // is blind to mutability, and only the mangled symbol distinguishes
        // the two (see `type_code`).
        ref borrowed if borrowed.as_class_borrow().is_some() => "ptr".into(),
        Ty::Record(record) => llvm_record_ty(record),
        _ => return None,
    })
}

fn require_llvm_ty(ty: Ty, span: Span, role: &str) -> Result<String, Vec<BackendError>> {
    llvm_ty(ty.clone()).ok_or_else(|| vec![lowering_gap(span, role, &ty, "value type")])
}

/// The LLVM type of a checked integer width.
///
/// Concrete widths only, the same post-monomorphization contract `IntTy::bits`
/// and `integer_type_code` carry: `require_concrete_integer` is the gate that
/// keeps an unsubstituted parameter from reaching any of the three.
fn integer_llvm_ty(integer: IntTy) -> String {
    format!("i{}", integer.bits())
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

/// The mangled component for a shape, or `None` for one the backend does not
/// name in a symbol. Total for the same reason `llvm_ty` is.
pub(crate) fn type_code(ty: Ty) -> Option<String> {
    Some(match ty {
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
        Ty::Option(payload) if payload.as_ref() == &Ty::Bool => "ob".into(),
        // The mangled symbol *is* mutability-sensitive, unlike the IR type:
        // two functions differing only in a parameter's borrow mutability are
        // two different native entry points.
        ref borrowed
            if matches!(
                borrowed.as_array_borrow(),
                Some((&Ty::Int(IntTy::U32), _)) | Some((&Ty::Bool, _))
            ) =>
        {
            let (element, mutability) = borrowed
                .as_array_borrow()
                .expect("the arm's guard already matched this shape");
            let mutability = match mutability {
                Mutability::Shared => "s",
                Mutability::Mut => "m",
            };
            format!("a{}{mutability}", type_code(element.clone())?)
        }
        ref borrowed if borrowed.as_class_borrow().is_some() => {
            let (class, mutability) = borrowed
                .as_class_borrow()
                .expect("the arm's guard already matched this shape");
            match mutability {
                Mutability::Shared => format!("c{class}s"),
                Mutability::Mut => format!("c{class}m"),
            }
        }
        Ty::Class(class) => format!("c{class}o"),
        Ty::Record(record) => format!("r{record}"),
        _ => return None,
    })
}

/// The mangled components of a signature, or the first shape that has none.
fn signature_codes(function: &Fn, ret: Option<&Ty>) -> Result<(String, String), Vec<BackendError>> {
    let mut params = Vec::with_capacity(function.params.len());
    for parameter in &function.params {
        let code = type_code(parameter.ty.clone()).ok_or_else(|| {
            vec![lowering_gap(
                parameter.span,
                &format!("parameter `{}`", parameter.name),
                &parameter.ty,
                "symbol type code",
            )]
        })?;
        params.push(code);
    }
    let ret = match ret {
        Some(ret) => type_code(ret.clone()).ok_or_else(|| {
            vec![lowering_gap(
                function.name_span,
                &format!("the return type of `{}`", function.name),
                ret,
                "symbol type code",
            )]
        })?,
        None => String::new(),
    };
    Ok((params.join("_"), ret))
}

fn mangle(function: &Fn) -> Result<String, Vec<BackendError>> {
    let (params, ret) = signature_codes(function, Some(&function.ret))?;
    Ok(format!(
        "__sable_v0_f_{}_{}__p_{}__r_{}",
        function.name.len(),
        function.name,
        params,
        ret
    ))
}

fn mangle_initializer(class: usize, initializer: &Fn) -> Result<String, Vec<BackendError>> {
    let (params, _) = signature_codes(initializer, None)?;
    Ok(format!(
        "__sable_v0_c{class}_i_{}_{}__p_{params}",
        initializer.name.len(),
        initializer.name
    ))
}

fn mangle_method(class: usize, method: &Fn) -> Result<String, Vec<BackendError>> {
    let (params, ret) = signature_codes(method, Some(&method.ret))?;
    Ok(format!(
        "__sable_v0_c{class}_m_{}_{}__p_{params}__r_{ret}",
        method.name.len(),
        method.name
    ))
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
        | ExprKind::SlotOp { args, .. }
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
        | ExprKind::OptTake { .. }
        | ExprKind::Borrow { .. } => {}
    }
}

fn collect_method_calls_block(statements: &[Stmt], methods: &mut Vec<(String, String, Span)>) {
    for statement in statements {
        match statement {
            Stmt::Decl { init, .. } => {
                if let Some(init) = init {
                    collect_method_calls_expr(init, methods);
                }
            }
            Stmt::Assign { value, .. }
            | Stmt::ExprStmt(value)
            | Stmt::Return {
                value: Some(value), ..
            }
            | Stmt::VarDecl { init: value, .. }
            | Stmt::FieldAssign { value, .. } => collect_method_calls_expr(value, methods),
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                collect_method_calls_expr(cond, methods);
                collect_method_calls_block(then_block, methods);
                if let Some(block) = else_block {
                    collect_method_calls_block(block, methods);
                }
            }
            Stmt::FieldStore { index, value, .. } | Stmt::Store { index, value, .. } => {
                collect_method_calls_expr(index, methods);
                collect_method_calls_expr(value, methods);
            }
            Stmt::While { cond, body, .. } => {
                collect_method_calls_expr(cond, methods);
                collect_method_calls_block(body, methods);
            }
            Stmt::Unsafe { body, .. } | Stmt::Expose { body, .. } => {
                collect_method_calls_block(body, methods)
            }
            Stmt::StaticAlloc { size, .. } | Stmt::SystemAlloc { size, .. } => {
                collect_method_calls_expr(size, methods)
            }
            Stmt::SystemDealloc {
                ptr, res, release, ..
            } => {
                collect_method_calls_expr(ptr, methods);
                collect_method_calls_expr(res, methods);
                collect_method_calls_expr(release, methods);
            }
            Stmt::Return { value: None, .. } | Stmt::Assert(_) => {}
        }
    }
}

fn collect_method_calls_expr(expression: &Expr, methods: &mut Vec<(String, String, Span)>) {
    match &expression.kind {
        ExprKind::MethodCall {
            recv,
            method,
            method_span,
            args,
            ..
        } => {
            methods.push((recv.clone(), method.clone(), *method_span));
            for argument in args {
                collect_method_calls_expr(argument, methods);
            }
        }
        ExprKind::Call { args, .. }
        | ExprKind::RawOp { args, .. }
        | ExprKind::DeviceOp { args, .. }
        | ExprKind::ResOp { args, .. }
        | ExprKind::SlotOp { args, .. }
        | ExprKind::CtorCall { args, .. }
        | ExprKind::TraitCall { args, .. }
        | ExprKind::RecordLit { args, .. }
        | ExprKind::ArrayLit(args) => {
            for argument in args {
                collect_method_calls_expr(argument, methods);
            }
        }
        ExprKind::Unary { operand, .. }
        | ExprKind::Widen { arg: operand, .. }
        | ExprKind::Narrow { arg: operand, .. }
        | ExprKind::IsSome { operand }
        | ExprKind::OptValue { operand }
        | ExprKind::SomeE(operand) => collect_method_calls_expr(operand, methods),
        ExprKind::Binary { lhs, rhs, .. } => {
            collect_method_calls_expr(lhs, methods);
            collect_method_calls_expr(rhs, methods);
        }
        ExprKind::Index { index, .. }
        | ExprKind::SelfFieldIndex { index, .. }
        | ExprKind::ClassFieldIndex { index, .. } => collect_method_calls_expr(index, methods),
        ExprKind::AllocArray { len, init, .. } => {
            collect_method_calls_expr(len, methods);
            collect_method_calls_expr(init, methods);
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
        | ExprKind::OptTake { .. }
        | ExprKind::Borrow { .. } => {}
    }
}

fn collect_constructors_block(
    statements: &[Stmt],
    constructors: &mut Vec<(String, String, Option<usize>, Span)>,
) {
    for statement in statements {
        match statement {
            Stmt::Decl { init, .. } => {
                if let Some(init) = init {
                    collect_constructors_expr(init, constructors);
                }
            }
            Stmt::Assign { value, .. }
            | Stmt::ExprStmt(value)
            | Stmt::Return {
                value: Some(value), ..
            }
            | Stmt::VarDecl { init: value, .. }
            | Stmt::FieldAssign { value, .. } => {
                collect_constructors_expr(value, constructors);
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                collect_constructors_expr(cond, constructors);
                collect_constructors_block(then_block, constructors);
                if let Some(block) = else_block {
                    collect_constructors_block(block, constructors);
                }
            }
            Stmt::FieldStore { index, value, .. } | Stmt::Store { index, value, .. } => {
                collect_constructors_expr(index, constructors);
                collect_constructors_expr(value, constructors);
            }
            Stmt::While { cond, body, .. } => {
                collect_constructors_expr(cond, constructors);
                collect_constructors_block(body, constructors);
            }
            Stmt::Unsafe { body, .. } | Stmt::Expose { body, .. } => {
                collect_constructors_block(body, constructors);
            }
            Stmt::StaticAlloc { size, .. } | Stmt::SystemAlloc { size, .. } => {
                collect_constructors_expr(size, constructors);
            }
            Stmt::SystemDealloc {
                ptr, res, release, ..
            } => {
                collect_constructors_expr(ptr, constructors);
                collect_constructors_expr(res, constructors);
                collect_constructors_expr(release, constructors);
            }
            Stmt::Return { value: None, .. } | Stmt::Assert(_) => {}
        }
    }
}

fn collect_constructors_expr(
    expression: &Expr,
    constructors: &mut Vec<(String, String, Option<usize>, Span)>,
) {
    match &expression.kind {
        ExprKind::CtorCall {
            class,
            class_span,
            init,
            args,
            ..
        } => {
            let checked_class = match expression.ty {
                Some(Ty::Class(class)) => Some(class),
                _ => None,
            };
            constructors.push((class.clone(), init.clone(), checked_class, *class_span));
            for argument in args {
                collect_constructors_expr(argument, constructors);
            }
        }
        ExprKind::Call { args, .. }
        | ExprKind::RawOp { args, .. }
        | ExprKind::DeviceOp { args, .. }
        | ExprKind::ResOp { args, .. }
        | ExprKind::SlotOp { args, .. }
        | ExprKind::TraitCall { args, .. }
        | ExprKind::MethodCall { args, .. }
        | ExprKind::RecordLit { args, .. }
        | ExprKind::ArrayLit(args) => {
            for argument in args {
                collect_constructors_expr(argument, constructors);
            }
        }
        ExprKind::Unary { operand, .. }
        | ExprKind::Widen { arg: operand, .. }
        | ExprKind::Narrow { arg: operand, .. }
        | ExprKind::IsSome { operand }
        | ExprKind::OptValue { operand }
        | ExprKind::SomeE(operand) => collect_constructors_expr(operand, constructors),
        ExprKind::Binary { lhs, rhs, .. } => {
            collect_constructors_expr(lhs, constructors);
            collect_constructors_expr(rhs, constructors);
        }
        ExprKind::Index { index, .. }
        | ExprKind::SelfFieldIndex { index, .. }
        | ExprKind::ClassFieldIndex { index, .. } => {
            collect_constructors_expr(index, constructors);
        }
        ExprKind::AllocArray { len, init, .. } => {
            collect_constructors_expr(len, constructors);
            collect_constructors_expr(init, constructors);
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
        | ExprKind::OptTake { .. }
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

fn slots_unsupported(span: Span, role: impl AsRef<str>) -> BackendError {
    diag(
        "backend.slots_unsupported",
        "owner slots are outside the native Boolean-local subset",
        span,
        format!(
            "{}; LLVM lowering admits only direct local `slots<bool>` storage and keeps slot call ABIs, class/record fields, other payloads, and Vec/class transport closed",
            role.as_ref()
        ),
    )
}

fn affine_option_unsupported(span: Span, role: &str, ty: Ty) -> BackendError {
    debug_assert!(ty.is_affine_option());
    diag(
        "backend.affine_option_unsupported",
        "affine option is outside the locals the LLVM backend lowers",
        span,
        format!(
            "{role} has type `{}`; native lowering admits only explicit mutable local `option<[bool]>` construction, named `.is_some`, and atomic `.take` into an explicit owned Boolean-array local",
            ty.name()
        ),
    )
}

fn affine_option_take_position(span: Span, option: &str, role: &str) -> BackendError {
    diag(
        "backend.affine_option_unsupported",
        "affine option is outside the locals the LLVM backend lowers",
        span,
        format!(
            "{role} cannot receive `.take` of affine option local `{option}`; `.take` must directly initialize an explicit owned Boolean-array local"
        ),
    )
}

fn affine_option_initializer_unsupported(span: Span, local: &str) -> BackendError {
    diag(
        "backend.affine_option_unsupported",
        "affine option is outside the locals the LLVM backend lowers",
        span,
        format!(
            "affine option local `{local}` must be initialized by `none` or `some(alloc_array<bool>(...))`"
        ),
    )
}

fn control_plan_backend_error(error: PlanError) -> BackendError {
    diag(
        "internal.control_plan_invalid",
        "LLVM rejected the checked lexical control plan",
        error.span,
        error.message,
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
        ExternInfo, Field, GenericTy, Method, Param, Program, ProofReuse, RecordField, SelfKind,
        StorageLayout, Ty, TypeArg,
    };
    use crate::scan::{Clause, ClauseKind};

    #[test]
    fn non_boolean_owner_slot_operations_stop_at_the_native_backend_boundary() {
        let operation = expression(
            ExprKind::SlotOp {
                op: crate::ast::SlotOp::Alloc {
                    elem: Ty::Int(IntTy::U64),
                },
                op_span: Span::new(0, 1),
                args: Vec::new(),
            },
            Ty::slots(Ty::Int(IntTy::U64)),
        );
        let mut locals = ValidationLocals::new();
        let errors = validate_expr(&program(Vec::new()), &operation, 1, &mut locals).expect_err(
            "non-Boolean owner slots have no native representation or operation semantics",
        );
        assert_eq!(errors[0].name, "backend.slots_unsupported");
    }

    fn expression(kind: ExprKind, ty: Ty) -> Expr {
        Expr {
            kind,
            span: Span::new(0, 1),
            ty: Some(ty),
        }
    }

    fn expression_at(kind: ExprKind, ty: Ty, start: usize) -> Expr {
        Expr {
            kind,
            span: Span::new(start, start + 1),
            ty: Some(ty),
        }
    }

    fn bool_slots_alloc(start: usize, len: i128) -> Expr {
        Expr {
            kind: ExprKind::SlotOp {
                op: SlotOp::Alloc { elem: Ty::Bool },
                op_span: Span::new(start, start + 1),
                args: vec![expression_at(
                    ExprKind::IntLit(len),
                    Ty::Int(IntTy::U64),
                    start + 1,
                )],
            },
            span: Span::new(start, start + 3),
            ty: Some(Ty::slots(Ty::Bool)),
        }
    }

    fn bool_slots_borrow(name: &str, start: usize) -> Expr {
        expression_at(
            ExprKind::Borrow {
                array: name.into(),
                field: None,
                mutable: true,
            },
            Ty::borrow(Mutability::Mut, Ty::slots(Ty::Bool)),
            start,
        )
    }

    fn bool_slots_put(name: &str, start: usize) -> Expr {
        let index = Expr {
            kind: ExprKind::Binary {
                op: BinOp::Add,
                op_span: Span::new(start + 2, start + 3),
                lhs: Box::new(expression_at(
                    ExprKind::IntLit(0),
                    Ty::Int(IntTy::U64),
                    start + 20,
                )),
                rhs: Box::new(expression_at(
                    ExprKind::IntLit(0),
                    Ty::Int(IntTy::U64),
                    start + 21,
                )),
            },
            span: Span::new(start + 2, start + 3),
            ty: Some(Ty::Int(IntTy::U64)),
        };
        Expr {
            kind: ExprKind::SlotOp {
                op: SlotOp::Put,
                op_span: Span::new(start, start + 1),
                args: vec![
                    bool_slots_borrow(name, start + 1),
                    index,
                    expression_at(ExprKind::BoolLit(true), Ty::Bool, start + 3),
                ],
            },
            span: Span::new(start, start + 4),
            ty: Some(Ty::Unit),
        }
    }

    fn bool_slots_take(name: &str, start: usize) -> Expr {
        Expr {
            kind: ExprKind::SlotOp {
                op: SlotOp::Take,
                op_span: Span::new(start, start + 1),
                args: vec![
                    bool_slots_borrow(name, start + 1),
                    expression_at(ExprKind::IntLit(0), Ty::Int(IntTy::U64), start + 2),
                ],
            },
            span: Span::new(start, start + 3),
            ty: Some(Ty::Bool),
        }
    }

    fn bool_slots_native_function() -> Fn {
        function(
            "bool_slots_native",
            Ty::Unit,
            vec![
                Stmt::Decl {
                    ty: Ty::slots(Ty::Bool),
                    name: "source".into(),
                    name_span: Span::new(1, 2),
                    init: Some(bool_slots_alloc(10, 2)),
                    mutable: true,
                },
                Stmt::Decl {
                    ty: Ty::slots(Ty::Bool),
                    name: "other".into(),
                    name_span: Span::new(5, 6),
                    init: Some(bool_slots_alloc(20, 1)),
                    mutable: true,
                },
                Stmt::ExprStmt(bool_slots_put("source", 30)),
                Stmt::Decl {
                    ty: Ty::slots(Ty::Bool),
                    name: "moved".into(),
                    name_span: Span::new(2, 3),
                    init: Some(expression_at(
                        ExprKind::Var("source".into()),
                        Ty::slots(Ty::Bool),
                        40,
                    )),
                    mutable: true,
                },
                Stmt::Decl {
                    ty: Ty::Bool,
                    name: "answer".into(),
                    name_span: Span::new(3, 4),
                    init: Some(bool_slots_take("moved", 50)),
                    mutable: false,
                },
                Stmt::Decl {
                    ty: Ty::slots(Ty::Bool),
                    name: "empty".into(),
                    name_span: Span::new(4, 5),
                    init: Some(bool_slots_alloc(60, 0)),
                    mutable: false,
                },
            ],
        )
    }

    #[test]
    fn boolean_owner_slots_lower_distinct_cells_exact_staging_moves_and_reverse_cleanup() {
        let source = program(vec![bool_slots_native_function()]);
        let control = ControlProgram::build(&source).expect("exact Boolean-slot control plan");
        let ir = emit_program_with_control(&source, &control, 100, &EmitOptions::default())
            .expect("direct local Boolean owner slots lower natively");

        assert!(ir.contains("%sable.slot.bool = type { i8, i8 }"), "{ir}");
        assert!(ir.contains("%sable.slots.bool = type { ptr, i64 }"), "{ir}");
        assert!(!ir.contains("%sable.array.bool = type"), "{ir}");
        assert!(!ir.contains("%sable.option.bool = type"), "{ir}");
        assert!(ir.contains("mul i64") && ir.contains(", 2"), "{ir}");
        assert!(ir.contains("alloca i1"), "{ir}");
        assert!(
            ir.contains(".slots.bool.zero") && ir.contains(".slots.bool.alloc"),
            "{ir}"
        );

        let container = ir
            .find("load %sable.slots.bool")
            .expect("slot_put first evaluates its owner descriptor");
        let index = ir
            .find("call { i64, i1 } @llvm.uadd.with.overflow.i64")
            .expect("slot_put then evaluates its checked index");
        let staged = ir[index..]
            .find("store i1 1, ptr")
            .map(|offset| index + offset)
            .expect("slot_put stages the incoming value");
        let bounds = ir[staged..]
            .find(&format!("i32 {TRAP_SLOTS_OOB}"))
            .map(|offset| staged + offset)
            .expect("slot_put retains its bounds trap after staging");
        assert!(
            container < index && index < staged && staged < bounds,
            "{ir}"
        );

        let fail_site = |kind: u32| format!("call void @__sable_rt_fail_v1(i32 {kind},");
        let oom_sites = ir
            .match_indices(&fail_site(TRAP_SLOTS_OOM))
            .map(|(offset, _)| offset)
            .collect::<Vec<_>>();
        assert!(oom_sites.len() >= 2, "{ir}");
        let allocation = ir
            .find("call ptr @__sable_rt_array_alloc_v1")
            .expect("non-empty slots use the audited allocation hook");
        assert!(
            oom_sites[0] < allocation && allocation < oom_sites[1],
            "{ir}"
        );

        let oob_sites = ir
            .match_indices(&fail_site(TRAP_SLOTS_OOB))
            .map(|(offset, _)| offset)
            .collect::<Vec<_>>();
        assert_eq!(oob_sites.len(), 2, "{ir}");
        let occupied = ir
            .find(&fail_site(TRAP_SLOTS_OCCUPIED))
            .expect("slot_put retains its occupied-cell trap");
        let empty = ir
            .find(&fail_site(TRAP_SLOTS_EMPTY))
            .expect("slot_take retains its empty-cell trap");
        assert!(
            staged < oob_sites[0]
                && oob_sites[0] < occupied
                && occupied < oob_sites[1]
                && oob_sites[1] < empty,
            "{ir}"
        );

        let move_load = ir
            .find("load %sable.slots.bool")
            .expect("whole-owner move loads the descriptor");
        let move_neutral = ir[move_load..]
            .find("store %sable.slots.bool zeroinitializer")
            .map(|offset| move_load + offset)
            .expect("whole-owner move neutralizes its source");
        assert!(move_load < move_neutral, "{ir}");

        assert!(ir.contains("slots.bool.drop.head"), "{ir}");
        assert!(ir.contains("slots.bool.drop.next"), "{ir}");
        assert!(ir.contains("sub i64"), "{ir}");
        assert!(ir.contains("call void @__sable_rt_array_free_v1"), "{ir}");
    }

    #[test]
    fn boolean_owner_slots_reject_retargeted_actions_nested_traps_and_abi_transport() {
        let source = program(vec![bool_slots_native_function()]);
        let control = ControlProgram::build(&source).expect("exact Boolean-slot control plan");

        let mut retargeted = source.clone();
        let Stmt::ExprStmt(put) = &mut retargeted.fns[0].body[2] else {
            unreachable!()
        };
        let ExprKind::SlotOp { args, .. } = &mut put.kind else {
            unreachable!()
        };
        let ExprKind::Borrow { array, .. } = &mut args[0].kind else {
            unreachable!()
        };
        *array = "other".into();
        let error = emit_program_with_control(&retargeted, &control, 100, &EmitOptions::default())
            .expect_err("a sealed slot action cannot be retargeted");
        assert_eq!(error[0].name, "internal.control_plan_invalid");

        let mut changed_trap = source.clone();
        let Stmt::ExprStmt(put) = &mut changed_trap.fns[0].body[2] else {
            unreachable!()
        };
        let ExprKind::SlotOp { args, .. } = &mut put.kind else {
            unreachable!()
        };
        let ExprKind::Binary { op, .. } = &mut args[1].kind else {
            unreachable!()
        };
        *op = BinOp::Sub;
        let error =
            emit_program_with_control(&changed_trap, &control, 100, &EmitOptions::default())
                .expect_err("a nested trap identity cannot change after slot planning");
        assert_eq!(error[0].name, "internal.control_plan_invalid");
        assert!(error[0].label.contains("SubOverflow"), "{:?}", error[0]);

        let mut changed_cleanup = source.clone();
        let Stmt::Decl { ty, init, .. } = &mut changed_cleanup.fns[0].body[0] else {
            unreachable!()
        };
        *ty = Ty::slots(Ty::Int(IntTy::U64));
        let Some(init) = init else { unreachable!() };
        let ExprKind::SlotOp {
            op: SlotOp::Alloc { elem },
            ..
        } = &mut init.kind
        else {
            unreachable!()
        };
        *elem = Ty::Int(IntTy::U64);
        init.ty = Some(Ty::slots(Ty::Int(IntTy::U64)));
        let error =
            emit_program_with_control(&changed_cleanup, &control, 100, &EmitOptions::default())
                .expect_err("a retained Boolean-slot cleanup cannot be reused for another payload");
        assert_eq!(error[0].name, "internal.control_plan_invalid");

        let slot_ty = Ty::slots(Ty::Bool);
        let error = require_parameter_value(
            &program(Vec::new()),
            1,
            slot_ty.clone(),
            Span::new(80, 81),
            "forged slot parameter",
        )
        .expect_err("Boolean slots have no native call ABI");
        assert_eq!(error[0].name, "backend.slots_unsupported");
        let error = require_runtime_type(
            &program(Vec::new()),
            1,
            slot_ty,
            Span::new(81, 82),
            "forged slot return",
        )
        .expect_err("Boolean slots have no native return ABI");
        assert_eq!(error[0].name, "backend.slots_unsupported");
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
        expression(kind, Ty::option(Ty::Bool))
    }

    fn bool_option_variable(name: &str) -> Expr {
        bool_option(ExprKind::Var(name.into()))
    }

    fn bool_array_ty() -> Ty {
        Ty::array(Ty::Bool)
    }

    fn bool_array_literal(values: &[bool]) -> Expr {
        expression(
            ExprKind::ArrayLit(
                values
                    .iter()
                    .map(|value| expression(ExprKind::BoolLit(*value), Ty::Bool))
                    .collect(),
            ),
            bool_array_ty(),
        )
    }

    fn bool_array_alloc(len: Expr, init: Expr) -> Expr {
        expression(
            ExprKind::AllocArray {
                elem: Ty::Bool,
                len: Box::new(len),
                init: Box::new(init),
            },
            bool_array_ty(),
        )
    }

    fn u32_array_ty(mutability: BindingMode) -> Ty {
        mutability.bind(Ty::array(Ty::Int(IntTy::U32)))
    }

    fn u32_array_literal(values: &[u32]) -> Expr {
        expression(
            ExprKind::ArrayLit(
                values
                    .iter()
                    .map(|value| expression(ExprKind::IntLit((*value).into()), Ty::Int(IntTy::U32)))
                    .collect(),
            ),
            u32_array_ty(BindingMode::Owned),
        )
    }

    fn u32_array_alloc(len: Expr, init: Expr) -> Expr {
        expression(
            ExprKind::AllocArray {
                elem: Ty::Int(IntTy::U32),
                len: Box::new(len),
                init: Box::new(init),
            },
            u32_array_ty(BindingMode::Owned),
        )
    }

    fn u32_array_borrow(name: &str, mutability: Mutability) -> Expr {
        expression(
            ExprKind::Borrow {
                array: name.into(),
                field: None,
                mutable: mutability == Mutability::Mut,
            },
            Ty::array_ref(Ty::Int(IntTy::U32), mutability),
        )
    }

    fn fixed_class_constructor() -> Expr {
        expression(
            ExprKind::CtorCall {
                class: "Nat".into(),
                class_span: Span::new(0, 1),
                type_args: Vec::new(),
                init: "new".into(),
                args: Vec::new(),
            },
            Ty::Class(0),
        )
    }

    fn fixed_class_borrow(name: &str) -> Expr {
        expression(
            ExprKind::Borrow {
                array: name.into(),
                field: None,
                mutable: false,
            },
            Ty::borrow(Mutability::Shared, Ty::Class(0)),
        )
    }

    fn scalar_owner_constructor(value: i128, start: usize) -> Expr {
        expression_at(
            ExprKind::CtorCall {
                class: "ScalarOwner".into(),
                class_span: Span::new(start, start + 1),
                type_args: Vec::new(),
                init: "new".into(),
                args: vec![expression_at(
                    ExprKind::IntLit(value),
                    Ty::Int(IntTy::U64),
                    start + 1,
                )],
            },
            Ty::Class(0),
            start,
        )
    }

    fn scalar_owner_method_call(
        receiver: &str,
        method: &str,
        args: Vec<Expr>,
        ret: Ty,
        start: usize,
    ) -> Expr {
        expression_at(
            ExprKind::MethodCall {
                recv: receiver.into(),
                recv_span: Span::new(start, start + 1),
                method: method.into(),
                method_span: Span::new(start + 1, start + 2),
                args,
            },
            ret,
            start,
        )
    }

    fn scalar_owner_program() -> Program {
        let mut initializer = function(
            "new",
            Ty::Unit,
            vec![Stmt::FieldAssign {
                field: "value".into(),
                field_span: Span::new(3, 4),
                value: expression_at(ExprKind::Var("initial".into()), Ty::Int(IntTy::U64), 4),
            }],
        );
        initializer.params = vec![parameter("initial", Ty::Int(IntTy::U64))];
        let getter = Method {
            self_kind: SelfKind::Shared,
            f: function(
                "get",
                Ty::Int(IntTy::U64),
                vec![Stmt::Return {
                    value: Some(expression_at(
                        ExprKind::SelfField {
                            field: "value".into(),
                        },
                        Ty::Int(IntTy::U64),
                        6,
                    )),
                    span: Span::new(7, 8),
                }],
            ),
        };
        let mut forward = function(
            "forward",
            Ty::Class(0),
            vec![Stmt::Return {
                value: Some(expression_at(
                    ExprKind::Var("incoming".into()),
                    Ty::Class(0),
                    10,
                )),
                span: Span::new(11, 12),
            }],
        );
        forward.params = vec![parameter("incoming", Ty::Class(0))];
        let class = ClassDecl {
            is_pub: false,
            name: "ScalarOwner".into(),
            name_span: Span::new(1, 2),
            type_params: Vec::new(),
            type_bounds: Vec::new(),
            proof_reuse: ProofReuse::None,
            fields: vec![Field {
                name: "value".into(),
                ty: Ty::Int(IntTy::U64),
                span: Span::new(2, 3),
                must_consume: false,
            }],
            invariants: Vec::new(),
            inits: vec![initializer],
            methods: vec![
                getter,
                Method {
                    self_kind: SelfKind::Mut,
                    f: forward,
                },
            ],
            deinit: None,
            span: Span::new(1, 20),
        };
        let entry = function(
            "scalar_owner_entry",
            Ty::Int(IntTy::I32),
            vec![
                Stmt::VarDecl {
                    ty: Some(Ty::Class(0)),
                    name: "receiver".into(),
                    name_span: Span::new(20, 21),
                    init: scalar_owner_constructor(10, 21),
                    mutable: true,
                },
                Stmt::VarDecl {
                    ty: Some(Ty::Class(0)),
                    name: "incoming".into(),
                    name_span: Span::new(30, 31),
                    init: scalar_owner_constructor(32, 31),
                    mutable: false,
                },
                Stmt::VarDecl {
                    ty: Some(Ty::Class(0)),
                    name: "returned".into(),
                    name_span: Span::new(40, 41),
                    init: scalar_owner_method_call(
                        "receiver",
                        "forward",
                        vec![expression_at(
                            ExprKind::Var("incoming".into()),
                            Ty::Class(0),
                            43,
                        )],
                        Ty::Class(0),
                        41,
                    ),
                    mutable: false,
                },
                Stmt::Return {
                    value: Some(expression_at(ExprKind::IntLit(42), Ty::Int(IntTy::I32), 50)),
                    span: Span::new(51, 52),
                },
            ],
        );
        let mut result = program(vec![entry]);
        result.classes.push(class);
        result
    }

    fn fixed_class_program() -> Program {
        let initializer = function(
            "new",
            Ty::Unit,
            vec![Stmt::FieldAssign {
                field: "limbs".into(),
                field_span: Span::new(0, 1),
                value: u32_array_literal(&[7]),
            }],
        );
        let mut inspect = function(
            "inspect",
            Ty::Unit,
            vec![
                Stmt::ExprStmt(expression(
                    ExprKind::ClassFieldIndex {
                        obj: "value".into(),
                        obj_span: Span::new(0, 1),
                        field: "limbs".into(),
                        index: Box::new(expression(
                            ExprKind::IntLit(0.into()),
                            Ty::Int(IntTy::U64),
                        )),
                    },
                    Ty::Int(IntTy::U32),
                )),
                Stmt::Return {
                    value: None,
                    span: Span::new(0, 1),
                },
            ],
        );
        inspect.params = vec![parameter(
            "value",
            Ty::borrow(Mutability::Shared, Ty::Class(0)),
        )];
        let entry = function(
            "entry",
            Ty::Int(IntTy::I32),
            vec![
                Stmt::VarDecl {
                    ty: Some(Ty::Class(0)),
                    name: "value".into(),
                    name_span: Span::new(0, 1),
                    init: fixed_class_constructor(),
                    mutable: false,
                },
                Stmt::ExprStmt(call_with(
                    "inspect",
                    Ty::Unit,
                    vec![fixed_class_borrow("value")],
                )),
                Stmt::Return {
                    value: Some(expression(ExprKind::IntLit(42.into()), Ty::Int(IntTy::I32))),
                    span: Span::new(0, 1),
                },
            ],
        );
        let mut result = program(vec![inspect, entry]);
        result.classes.push(ClassDecl {
            is_pub: false,
            name: "Nat".into(),
            name_span: Span::new(0, 1),
            type_params: Vec::new(),
            type_bounds: Vec::new(),
            proof_reuse: ProofReuse::None,
            fields: vec![Field {
                name: "limbs".into(),
                ty: u32_array_ty(BindingMode::Owned),
                span: Span::new(0, 1),
                must_consume: false,
            }],
            invariants: Vec::new(),
            inits: vec![initializer],
            methods: Vec::new(),
            deinit: Some(Vec::new()),
            span: Span::new(0, 1),
        });
        result
    }

    fn affine_bool_option(kind: ExprKind) -> Expr {
        expression(kind, affine_bool_option_ty())
    }

    fn affine_bool_option_variable(name: &str) -> Expr {
        affine_bool_option(ExprKind::Var(name.into()))
    }

    fn affine_is_some(name: &str) -> Expr {
        expression(
            ExprKind::IsSome {
                operand: Box::new(affine_bool_option_variable(name)),
            },
            Ty::Bool,
        )
    }

    fn affine_some_alloc(len: u64, init: bool) -> Expr {
        affine_bool_option(ExprKind::SomeE(Box::new(bool_array_alloc(
            expression(ExprKind::IntLit(len.into()), Ty::Int(IntTy::U64)),
            expression(ExprKind::BoolLit(init), Ty::Bool),
        ))))
    }

    fn affine_take(name: &str) -> Expr {
        expression(
            ExprKind::OptTake {
                option: name.into(),
                option_span: Span::new(0, 1),
            },
            bool_array_ty(),
        )
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
    fn exact_scalar_owner_gate_rejects_authority_metadata_and_non_scalar_layouts() {
        let baseline = scalar_owner_program();
        require_exact_scalar_owner_class(&baseline, 0, 100, Span::new(1, 2), "baseline")
            .expect("private concrete integer-only owner is admitted");

        let mut cases = Vec::new();
        let mut public = baseline.clone();
        public.classes[0].is_pub = true;
        cases.push(public);
        let mut imported = baseline.clone();
        imported.classes[0].name_span = Span::new(100, 101);
        cases.push(imported);
        let mut generic = baseline.clone();
        generic.classes[0].type_params.push("T".into());
        generic.classes[0].type_bounds.push(None);
        cases.push(generic);
        let mut generic_method = baseline.clone();
        generic_method.classes[0].methods[0]
            .f
            .type_params
            .push("T".into());
        generic_method.classes[0].methods[0]
            .f
            .type_bounds
            .push(None);
        cases.push(generic_method);
        let mut reused = baseline.clone();
        reused.classes[0].proof_reuse = ProofReuse::adr0009_int_model("Template".into());
        cases.push(reused);
        let mut reused_method = baseline.clone();
        reused_method.classes[0].methods[0].f.proof_reuse =
            ProofReuse::adr0009_int_model("TemplateMethod".into());
        cases.push(reused_method);
        let mut extern_method = baseline.clone();
        extern_method.classes[0].methods[0].f.extern_info = Some(ExternInfo {
            abi: "C".into(),
            audit_id: "forged-scalar-owner".into(),
            reason: "negative LLVM gate test".into(),
            span: Span::new(62, 63),
        });
        cases.push(extern_method);
        let mut executable_deinit = baseline.clone();
        executable_deinit.classes[0].deinit = Some(vec![Stmt::ExprStmt(expression(
            ExprKind::BoolLit(true),
            Ty::Bool,
        ))]);
        cases.push(executable_deinit);
        let mut mandatory = baseline.clone();
        mandatory.classes[0].fields[0].must_consume = true;
        cases.push(mandatory);
        for ty in [
            Ty::array(Ty::Int(IntTy::U32)),
            Ty::slots(Ty::Bool),
            Ty::Record(0),
            Ty::Class(0),
        ] {
            let mut non_scalar = baseline.clone();
            non_scalar.classes[0].fields[0].ty = ty;
            cases.push(non_scalar);
        }

        for case in cases {
            let error =
                require_exact_scalar_owner_class(&case, 0, 100, Span::new(1, 2), "negative shape")
                    .expect_err("every authority-bearing or non-scalar shape stays closed");
            assert_eq!(error[0].name, "backend.class_unsupported");
        }

        let error = require_parameter_value(
            &baseline,
            100,
            Ty::Class(0),
            Span::new(60, 61),
            "free-function owner parameter",
        )
        .expect_err("the new owner is not a free-function by-value ABI");
        assert_eq!(error[0].name, "backend.class_unsupported");

        let mut wrong_result = baseline.clone();
        wrong_result.classes[0].methods[1].f.ret = Ty::slots(Ty::Bool);
        let error = require_scalar_owner_method_result(
            &wrong_result,
            100,
            wrong_result.classes[0].methods[1].f.ret.clone(),
            Span::new(61, 62),
        )
        .expect_err("slots cannot become a scalar-owner method result");
        assert_eq!(error[0].name, "backend.class_unsupported");
    }

    #[test]
    fn scalar_owner_method_moves_are_live_checked_and_zeroed() {
        let valid = scalar_owner_program();
        let ir = emit_program(
            &valid,
            100,
            &EmitOptions {
                entry: Some("scalar_owner_entry".into()),
            },
        )
        .expect("exact scalar-owner constructors and methods lower");
        assert!(
            ir.contains(
                "define internal void @__sable_v0_c0_m_7_forward__p_c0o__r_c0o(ptr %self, ptr %result, %sable.class.0 %p0)"
            ),
            "{ir}"
        );
        let moved = ir
            .find("load %sable.class.0")
            .expect("owned method argument is loaded");
        let cleared = ir[moved..]
            .find("store %sable.class.0 zeroinitializer")
            .map(|offset| moved + offset)
            .expect("owned method argument source is neutralized");
        let called = ir[cleared..]
            .find("call void @__sable_v0_c0_m_7_forward")
            .map(|offset| cleared + offset)
            .expect("class-returning method is invoked after the move");
        assert!(moved < cleared && cleared < called, "{ir}");

        let mut reused = scalar_owner_program();
        reused.fns[0].body.insert(
            3,
            Stmt::ExprStmt(scalar_owner_method_call(
                "incoming",
                "get",
                Vec::new(),
                Ty::Int(IntTy::U64),
                48,
            )),
        );
        let error = emit_program(
            &reused,
            100,
            &EmitOptions {
                entry: Some("scalar_owner_entry".into()),
            },
        )
        .expect_err("a moved argument cannot be reused as a method receiver");
        assert_eq!(error[0].name, "backend.class_moved");

        let mut wrong_call_result = scalar_owner_program();
        let Stmt::VarDecl { init, .. } = &mut wrong_call_result.fns[0].body[2] else {
            unreachable!()
        };
        init.ty = Some(Ty::Unit);
        let error = emit_program(
            &wrong_call_result,
            100,
            &EmitOptions {
                entry: Some("scalar_owner_entry".into()),
            },
        )
        .expect_err("a method result annotation cannot disagree with its declaration");
        assert_eq!(error[0].name, "backend.unsupported");
    }

    #[test]
    fn scalar_owner_method_calls_exact_consume_the_checker_plan() {
        let mut source = scalar_owner_program();
        let checked = crate::check::check(&mut source).expect("synthetic scalar owner typechecks");
        emit_program_with_plans(
            &source,
            &checked.control,
            &checked.ownership,
            100,
            &EmitOptions {
                entry: Some("scalar_owner_entry".into()),
            },
            "test-only checked plan",
        )
        .expect("the exact checked method plan lowers");

        let mut respanned = source.clone();
        let Stmt::VarDecl { init, .. } = &mut respanned.fns[0].body[2] else {
            unreachable!()
        };
        let ExprKind::MethodCall { args, .. } = &mut init.kind else {
            unreachable!()
        };
        args[0].span = Span::new(70, 71);
        let error = emit_program_with_plans(
            &respanned,
            &checked.control,
            &checked.ownership,
            100,
            &EmitOptions {
                entry: Some("scalar_owner_entry".into()),
            },
            "test-only checked plan",
        )
        .expect_err("a respanned owned argument cannot reuse the checked method plan");
        assert_eq!(error[0].name, "internal.control_plan_invalid");

        let mut tampered = crate::check::check(&mut source).expect("fresh exact call plan");
        let key = tampered
            .ownership
            .calls
            .for_owner(&CallOwner::Function("scalar_owner_entry".into()))
            .find(|(key, _)| {
                matches!(key.target, CallTarget::Method { ref method, .. } if method == "forward")
            })
            .map(|(key, _)| key.clone())
            .expect("forward call transition");
        tampered
            .ownership
            .calls
            .get_mut(&key)
            .expect("mutable checked transition")
            .arguments[0]
            .parameter_ty = Ty::Bool;
        let error = emit_program_with_plans(
            &source,
            &tampered.control,
            &tampered.ownership,
            100,
            &EmitOptions {
                entry: Some("scalar_owner_entry".into()),
            },
            "test-only checked plan",
        )
        .expect_err("a mutated transfer cannot authorize LLVM argument lowering");
        assert_eq!(error[0].name, "internal.control_plan_invalid");

        let mut detached = crate::check::check(&mut source).expect("fresh exact call plan");
        let key = detached
            .ownership
            .calls
            .for_owner(&CallOwner::Function("scalar_owner_entry".into()))
            .find(|(key, _)| {
                matches!(key.target, CallTarget::Method { ref method, .. } if method == "forward")
            })
            .map(|(key, _)| key.clone())
            .expect("forward call transition");
        detached
            .ownership
            .calls
            .get_mut(&key)
            .expect("mutable checked transition")
            .key
            .span = Span::new(80, 81);
        let error = emit_program_with_plans(
            &source,
            &detached.control,
            &detached.ownership,
            100,
            &EmitOptions {
                entry: Some("scalar_owner_entry".into()),
            },
            "test-only checked plan",
        )
        .expect_err("a detached transition value key cannot authorize LLVM lowering");
        assert_eq!(error[0].name, "internal.control_plan_invalid");
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
            record.clone(),
            vec![Stmt::Return {
                value: Some(pair_literal(
                    typed_variable("answer", i32_ty.clone()),
                    typed_variable("marker", u64_ty.clone()),
                )),
                span: Span::new(0, 1),
            }],
        );
        make.params = vec![
            parameter("answer", i32_ty.clone()),
            parameter("marker", u64_ty.clone()),
        ];

        let mut project = function(
            "project",
            i32_ty.clone(),
            vec![
                Stmt::Decl {
                    ty: record.clone(),
                    name: "copy".into(),
                    name_span: Span::new(0, 1),
                    init: Some(typed_variable("pair", record.clone())),
                    mutable: false,
                },
                Stmt::Return {
                    value: Some(pair_answer("copy")),
                    span: Span::new(0, 1),
                },
            ],
        );
        project.params = vec![parameter("pair", record.clone())];

        let forward = function(
            "forward",
            record.clone(),
            vec![
                Stmt::Decl {
                    ty: record.clone(),
                    name: "result".into(),
                    name_span: Span::new(0, 1),
                    init: Some(pair_literal(
                        expression(ExprKind::IntLit(0), i32_ty.clone()),
                        expression(ExprKind::IntLit(0), u64_ty.clone()),
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
                            record.clone(),
                            vec![
                                expression(ExprKind::IntLit(42), i32_ty.clone()),
                                expression(ExprKind::IntLit(7), u64_ty.clone()),
                            ],
                        ),
                    }],
                    else_block: Some(vec![Stmt::Assign {
                        name: "result".into(),
                        name_span: Span::new(0, 1),
                        value: pair_literal(
                            expression(ExprKind::IntLit(1), i32_ty.clone()),
                            expression(ExprKind::IntLit(2), u64_ty),
                        ),
                    }]),
                },
                Stmt::Return {
                    value: Some(typed_variable("result", record.clone())),
                    span: Span::new(0, 1),
                },
            ],
        );

        let consume = function(
            "consume",
            i32_ty.clone(),
            vec![
                Stmt::Decl {
                    ty: record.clone(),
                    name: "value".into(),
                    name_span: Span::new(0, 1),
                    init: Some(call("forward", record.clone())),
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
    fn pod_record_value_rejects_pointer_fields_and_imported_identity() {
        let mut pointer_record = integer_pair_record();
        pointer_record.name = "Node".into();
        pointer_record.fields[0].name = "next".into();
        pointer_record.fields[0].ty = Ty::RawRecord(0);
        let mut pointer_program = program(Vec::new());
        pointer_program.records.push(pointer_record);
        let pointer_error = emit_program(&pointer_program, 1, &EmitOptions::default()).unwrap_err();
        assert_eq!(pointer_error[0].name, "backend.unsupported");
        assert!(
            pointer_error[0]
                .label
                .contains("only when every field is a concrete integer")
        );

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
    fn affine_options_lower_canonical_local_state_atomic_take_and_conditional_drop() {
        let affine_bool = Ty::affine_array_option(Ty::Bool);
        let subject = function(
            "affine_local",
            Ty::Bool,
            vec![
                Stmt::Decl {
                    ty: affine_bool.clone(),
                    name: "pending".into(),
                    name_span: Span::new(0, 1),
                    init: Some(affine_some_alloc(2, false)),
                    mutable: true,
                },
                Stmt::ExprStmt(affine_is_some("pending")),
                Stmt::Decl {
                    ty: bool_array_ty(),
                    name: "values".into(),
                    name_span: Span::new(0, 1),
                    init: Some(affine_take("pending")),
                    mutable: true,
                },
                Stmt::Decl {
                    ty: affine_bool,
                    name: "absent".into(),
                    name_span: Span::new(0, 1),
                    init: Some(affine_bool_option(ExprKind::NoneE)),
                    mutable: true,
                },
                Stmt::Return {
                    value: Some(expression(
                        ExprKind::Unary {
                            op: UnOp::Not,
                            operand: Box::new(affine_is_some("pending")),
                        },
                        Ty::Bool,
                    )),
                    span: Span::new(0, 1),
                },
            ],
        );
        let ir = emit_program(&program(vec![subject]), 1, &EmitOptions::default()).unwrap();

        assert_eq!(
            ir.matches("%sable.option.array.bool = type { i8, %sable.array.bool }")
                .count(),
            1
        );
        assert!(
            ir.find("%sable.array.bool = type { ptr, i64 }").unwrap()
                < ir.find("%sable.option.array.bool = type").unwrap()
        );
        assert!(
            ir.find("%sable.option.array.bool = type").unwrap()
                < ir.find("define internal").unwrap()
        );
        assert!(ir.contains("alloca %sable.option.array.bool"));
        assert!(
            ir.contains("insertvalue %sable.option.array.bool zeroinitializer, %sable.array.bool")
        );
        assert!(ir.contains("insertvalue %sable.option.array.bool"));
        assert!(ir.contains(", i8 1, 0"));
        assert!(ir.contains("store %sable.option.array.bool zeroinitializer, ptr %v2"));
        assert!(ir.contains("icmp eq i8"));
        assert!(ir.contains(", 1"));

        let take_load = ir.find("load %sable.option.array.bool, ptr %v0").unwrap();
        let take_guard = ir[take_load..].find("icmp ne i8").unwrap() + take_load;
        let trap = ir[take_guard..]
            .find("call void @__sable_rt_fail_v1(i32 8, i32 0")
            .unwrap()
            + take_guard;
        let clear = ir[trap..]
            .find("store %sable.option.array.bool zeroinitializer, ptr %v0")
            .unwrap()
            + trap;
        let destination = ir[clear..].find("store %sable.array.bool").unwrap() + clear;
        assert!(take_load < take_guard && take_guard < trap && trap < clear && clear < destination);

        // Both ownership carriers retain cleanup code. At runtime the cleared
        // source follows the tag-zero edge, while `values` owns the sole free.
        let cleanup = &ir[destination..];
        assert!(cleanup.contains("icmp eq i8"));
        assert!(cleanup.contains("icmp eq ptr"));
        assert!(cleanup.contains("call void @__sable_rt_array_free_v1"));
    }

    #[test]
    fn affine_option_abi_construction_transport_and_take_fences_stay_closed() {
        let affine_bool = affine_bool_option_ty();
        let affine_integer = Ty::affine_array_option(Ty::Int(IntTy::I32));
        let assert_affine_error = |errors: Vec<BackendError>| {
            assert_eq!(errors[0].name, "backend.affine_option_unsupported");
        };

        for ty in [affine_bool.clone(), affine_integer.clone()] {
            assert_affine_error(
                emit_program(
                    &program(vec![function("affine_return", ty, Vec::new())]),
                    1,
                    &EmitOptions::default(),
                )
                .expect_err("affine options must not acquire a return ABI"),
            );
        }
        let mut parameterized = function("affine_parameter", Ty::Unit, Vec::new());
        parameterized
            .params
            .push(parameter("pending", affine_bool.clone()));
        assert_affine_error(
            emit_program(&program(vec![parameterized]), 1, &EmitOptions::default())
                .expect_err("affine options must not acquire a parameter ABI"),
        );

        for invalid in [
            Stmt::Decl {
                ty: affine_bool.clone(),
                name: "immutable".into(),
                name_span: Span::new(0, 1),
                init: Some(affine_bool_option(ExprKind::NoneE)),
                mutable: false,
            },
            Stmt::Decl {
                ty: affine_bool.clone(),
                name: "missing".into(),
                name_span: Span::new(0, 1),
                init: None,
                mutable: true,
            },
            Stmt::Decl {
                ty: affine_integer.clone(),
                name: "nonbool".into(),
                name_span: Span::new(0, 1),
                init: Some(expression(ExprKind::NoneE, affine_integer)),
                mutable: true,
            },
            Stmt::Decl {
                ty: affine_bool.clone(),
                name: "literal".into(),
                name_span: Span::new(0, 1),
                init: Some(affine_bool_option(ExprKind::SomeE(Box::new(
                    bool_array_literal(&[true]),
                )))),
                mutable: true,
            },
            Stmt::VarDecl {
                name: "inferred".into(),
                name_span: Span::new(0, 1),
                init: affine_bool_option(ExprKind::NoneE),
                mutable: true,
                ty: Some(affine_bool.clone()),
            },
        ] {
            assert_affine_error(
                emit_program(
                    &program(vec![function("invalid_local", Ty::Unit, vec![invalid])]),
                    1,
                    &EmitOptions::default(),
                )
                .expect_err("forged construction must remain outside what the backend lowers"),
            );
        }

        let empty = program(Vec::new());
        let mut locals = ValidationLocals::new();
        locals
            .insert(
                "pending".into(),
                ValidationLocal {
                    ty: affine_bool.clone(),
                    mutable: true,
                },
                Span::new(0, 1),
            )
            .unwrap();
        locals
            .insert(
                "immutable".into(),
                ValidationLocal {
                    ty: affine_bool.clone(),
                    mutable: false,
                },
                Span::new(0, 1),
            )
            .unwrap();
        locals
            .insert(
                "scalar".into(),
                ValidationLocal {
                    ty: Ty::Bool,
                    mutable: true,
                },
                Span::new(0, 1),
            )
            .unwrap();

        for (destination, take) in [
            ("pending", affine_take("pending")),
            ("values", affine_take("immutable")),
            ("values", affine_take("scalar")),
            ("values", affine_take("missing")),
        ] {
            assert_affine_error(
                validate_fresh_bool_array_initializer(
                    &empty,
                    &take,
                    1,
                    &mut locals,
                    destination,
                    true,
                )
                .expect_err("forged take source/destination must be rejected"),
            );
        }

        assert_affine_error(
            validate_expr(&empty, &affine_take("pending"), 1, &mut locals)
                .expect_err("take is not a general expression"),
        );
        assert_affine_error(
            validate_expr(
                &empty,
                &expression(
                    ExprKind::OptValue {
                        operand: Box::new(affine_bool_option_variable("pending")),
                    },
                    bool_array_ty(),
                ),
                1,
                &mut locals,
            )
            .expect_err("`.value` must not copy an affine payload"),
        );

        let inferred_take = function(
            "inferred_take",
            Ty::Unit,
            vec![
                Stmt::Decl {
                    ty: affine_bool.clone(),
                    name: "pending".into(),
                    name_span: Span::new(0, 1),
                    init: Some(affine_bool_option(ExprKind::NoneE)),
                    mutable: true,
                },
                Stmt::VarDecl {
                    name: "values".into(),
                    name_span: Span::new(0, 1),
                    init: affine_take("pending"),
                    mutable: false,
                    ty: Some(bool_array_ty()),
                },
            ],
        );
        assert_affine_error(
            emit_program(&program(vec![inferred_take]), 1, &EmitOptions::default())
                .expect_err("take destination must be an explicit owned-array declaration"),
        );

        let mut record_program = program(Vec::new());
        let mut record = integer_pair_record();
        record.fields[0].ty = affine_bool;
        record_program.records.push(record);
        assert_affine_error(
            emit_program(&record_program, 1, &EmitOptions::default())
                .expect_err("affine options must not acquire POD record layout"),
        );
    }

    #[test]
    fn affine_option_cleanups_follow_branch_loop_unsafe_and_return_lifetimes() {
        let affine = affine_bool_option_ty();
        let option_decl = |name: &str, len: u64| {
            let mut init = affine_some_alloc(len, true);
            let ExprKind::SomeE(payload) = &mut init.kind else {
                unreachable!("fixture constructs a present affine option")
            };
            payload.span = Span::new(100 + len as usize, 101 + len as usize);
            Stmt::Decl {
                ty: affine.clone(),
                name: name.into(),
                name_span: Span::new(0, 1),
                init: Some(init),
                mutable: true,
            }
        };
        let subject = function(
            "affine_cfg",
            Ty::Bool,
            vec![
                option_decl("outer", 1),
                Stmt::If {
                    cond: expression(ExprKind::BoolLit(true), Ty::Bool),
                    then_block: vec![option_decl("branch", 2)],
                    else_block: None,
                },
                Stmt::While {
                    cond: expression(ExprKind::BoolLit(false), Ty::Bool),
                    invariants: Vec::new(),
                    variant: None,
                    kw_span: Span::new(0, 1),
                    body: vec![
                        option_decl("loop_option", 3),
                        Stmt::Decl {
                            ty: bool_array_ty(),
                            name: "loop_values".into(),
                            name_span: Span::new(0, 1),
                            init: Some(affine_take("loop_option")),
                            mutable: false,
                        },
                    ],
                },
                Stmt::Unsafe {
                    kw_span: Span::new(0, 1),
                    body: vec![option_decl("unsafe_option", 4)],
                },
                Stmt::Return {
                    value: Some(expression(ExprKind::BoolLit(true), Ty::Bool)),
                    span: Span::new(0, 1),
                },
            ],
        );
        let ir = emit_program(&program(vec![subject]), 1, &EmitOptions::default()).unwrap();

        assert!(ir.contains("if.then"));
        assert!(ir.contains("while.body"));
        assert!(ir.contains("option.drop.present"));
        assert_eq!(ir.matches("call void @__sable_rt_array_free_v1").count(), 5);

        let loop_body = ir.find("while.body").unwrap();
        let loop_array_drop = ir[loop_body..]
            .find("load %sable.array.bool, ptr %v3")
            .unwrap()
            + loop_body;
        let loop_option_drop = ir[loop_array_drop..]
            .find("load %sable.option.array.bool, ptr %v2")
            .unwrap()
            + loop_array_drop;
        assert!(loop_array_drop < loop_option_drop);

        let return_cleanup = ir.rfind("load %sable.option.array.bool, ptr %v4").unwrap();
        let outer_cleanup = ir[return_cleanup..]
            .find("load %sable.option.array.bool, ptr %v0")
            .unwrap()
            + return_cleanup;
        let ret = ir.rfind("ret i1 1").unwrap();
        assert!(return_cleanup < outer_cleanup && outer_cleanup < ret);

        let take_trap = ir
            .find("call void @__sable_rt_fail_v1(i32 8, i32 0")
            .unwrap();
        let trap_end = ir[take_trap..].find("unreachable").unwrap() + take_trap;
        assert!(!ir[take_trap..trap_end].contains("@__sable_rt_array_free_v1"));
    }

    #[test]
    fn boolean_option_is_canonical_and_transports_across_cfg_calls_and_locals() {
        let option = Ty::option(Ty::Bool);
        let make_false = function(
            "make_false",
            option.clone(),
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
            option.clone(),
            vec![
                Stmt::Decl {
                    ty: option.clone(),
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
                        value: call("make_false", option.clone()),
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
                    init: call("forward", option.clone()),
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
    fn boolean_option_parameters_lower_and_other_option_positions_stay_closed() {
        let option = Ty::option(Ty::Bool);
        let bool_array = Ty::array(Ty::Bool);
        let mut parameterized = function(
            "parameterized",
            Ty::Bool,
            vec![
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
        parameterized.params = vec![parameter("value", option.clone())];
        let caller = function(
            "call_it",
            Ty::Bool,
            vec![Stmt::Return {
                value: Some(call_with(
                    "parameterized",
                    Ty::Bool,
                    vec![bool_option(ExprKind::NoneE)],
                )),
                span: Span::new(0, 1),
            }],
        );
        let ir = emit_program(
            &program(vec![parameterized, caller]),
            1,
            &EmitOptions::default(),
        )
        .unwrap();
        assert!(ir.contains(
            "define internal i1 @__sable_v0_f_13_parameterized__p_ob__r_b(%sable.option.bool %p0)"
        ));
        assert!(ir.contains("store %sable.option.bool %p0, ptr"));
        assert!(ir.contains(
            "call i1 @__sable_v0_f_13_parameterized__p_ob__r_b(%sable.option.bool zeroinitializer)"
        ));

        let mut integer_parameterized = function(
            "integer_parameterized",
            Ty::Bool,
            vec![Stmt::Return {
                value: Some(expression(ExprKind::BoolLit(false), Ty::Bool)),
                span: Span::new(0, 1),
            }],
        );
        integer_parameterized.params = vec![parameter("value", Ty::option(Ty::Int(IntTy::U64)))];
        let parameter_error = emit_program(
            &program(vec![integer_parameterized]),
            1,
            &EmitOptions::default(),
        )
        .unwrap_err();
        assert_eq!(parameter_error[0].name, "backend.unsupported");
        assert!(parameter_error[0].label.contains("function parameter"));
        assert!(
            parameter_error[0]
                .label
                .contains("no LLVM value representation")
        );

        let local_array = function(
            "bool_array_local",
            Ty::Unit,
            vec![
                Stmt::Decl {
                    ty: bool_array,
                    name: "values".into(),
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
        let array_error =
            emit_program(&program(vec![local_array]), 1, &EmitOptions::default()).unwrap_err();
        assert_eq!(array_error[0].name, "backend.unsupported");
        assert!(array_error[0].label.contains("has no initializer"));

        for unsupported_return in [
            Ty::option(Ty::Int(IntTy::I32)),
            Ty::option(Ty::Record(0)),
            Ty::option(Ty::Param(crate::ast::TypeParamId::from_legacy(0))),
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
            option.clone(),
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
    fn u32_arrays_lower_typed_unaligned_storage_borrows_and_logical_oom_payloads() {
        let owned = u32_array_ty(BindingMode::Owned);
        let shared = u32_array_ty(BindingMode::Shared);
        let mutable = u32_array_ty(BindingMode::Mut);
        let u32_ty = Ty::Int(IntTy::U32);
        let u64_ty = Ty::Int(IntTy::U64);

        let mut shared_head = function(
            "shared_head",
            u32_ty.clone(),
            vec![Stmt::Return {
                value: Some(expression(
                    ExprKind::Index {
                        array: "values".into(),
                        array_span: Span::new(0, 1),
                        index: Box::new(expression(ExprKind::IntLit(0), u64_ty.clone())),
                    },
                    u32_ty.clone(),
                )),
                span: Span::new(0, 1),
            }],
        );
        shared_head.params = vec![parameter("values", shared)];

        let mut mutate = function(
            "mutate",
            u32_ty.clone(),
            vec![
                Stmt::Store {
                    array: "values".into(),
                    array_span: Span::new(0, 1),
                    index: expression(ExprKind::IntLit(1), u64_ty.clone()),
                    value: typed_variable("replacement", u32_ty.clone()),
                },
                Stmt::Return {
                    value: Some(expression(
                        ExprKind::Index {
                            array: "values".into(),
                            array_span: Span::new(0, 1),
                            index: Box::new(expression(ExprKind::IntLit(1), u64_ty.clone())),
                        },
                        u32_ty.clone(),
                    )),
                    span: Span::new(0, 1),
                },
            ],
        );
        mutate.params = vec![
            parameter("values", mutable),
            parameter("replacement", u32_ty.clone()),
        ];

        let mut allocate = function(
            "allocate",
            u64_ty.clone(),
            vec![
                Stmt::Decl {
                    ty: owned.clone(),
                    name: "values".into(),
                    name_span: Span::new(0, 1),
                    init: Some(u32_array_alloc(
                        typed_variable("length", u64_ty.clone()),
                        expression(ExprKind::IntLit(17), u32_ty.clone()),
                    )),
                    mutable: false,
                },
                Stmt::Return {
                    value: Some(expression(
                        ExprKind::Len {
                            array: "values".into(),
                        },
                        u64_ty.clone(),
                    )),
                    span: Span::new(0, 1),
                },
            ],
        );
        allocate.params = vec![parameter("length", u64_ty)];

        let caller = function(
            "caller",
            u32_ty.clone(),
            vec![
                Stmt::Decl {
                    ty: owned,
                    name: "values".into(),
                    name_span: Span::new(0, 1),
                    init: Some(u32_array_literal(&[1, 2, 3])),
                    mutable: true,
                },
                Stmt::Decl {
                    ty: u32_ty.clone(),
                    name: "changed".into(),
                    name_span: Span::new(0, 1),
                    init: Some(call_with(
                        "mutate",
                        u32_ty.clone(),
                        vec![
                            u32_array_borrow("values", Mutability::Mut),
                            expression(ExprKind::IntLit(9), u32_ty.clone()),
                        ],
                    )),
                    mutable: false,
                },
                Stmt::Return {
                    value: Some(call_with(
                        "shared_head",
                        u32_ty,
                        vec![u32_array_borrow("values", Mutability::Shared)],
                    )),
                    span: Span::new(0, 1),
                },
            ],
        );

        let ir = emit_program(
            &program(vec![shared_head, mutate, allocate, caller]),
            1,
            &EmitOptions::default(),
        )
        .unwrap();
        assert!(ir.contains("%sable.array.u32 = type { ptr, i64 }"));
        assert!(ir.contains("getelementptr i32"));
        assert!(ir.contains("store i32 1, ptr"));
        assert!(ir.contains("store i32 2, ptr"));
        assert!(ir.contains("store i32 3, ptr"));
        assert!(ir.contains("store i32 17, ptr"));
        assert!(ir.contains("load i32, ptr"));
        let payload_addresses = ir
            .lines()
            .filter(|line| line.contains(" = getelementptr i32, ptr "))
            .filter_map(|line| line.trim().split_once(" = ").map(|(name, _)| name))
            .collect::<Vec<_>>();
        assert!(!payload_addresses.is_empty());
        for address in payload_addresses {
            let accesses = ir
                .lines()
                .filter(|line| {
                    (line.contains("load i32, ptr") || line.contains("store i32"))
                        && line.contains(&format!("ptr {address}"))
                })
                .collect::<Vec<_>>();
            assert!(!accesses.is_empty(), "payload address {address} is unused");
            for payload_access in accesses {
                assert!(payload_access.ends_with(", align 1"), "{payload_access}");
            }
        }
        assert!(ir.contains(" = mul i64 "));
        assert!(ir.contains(", 4"));
        assert!(!ir.contains("getelementptr inbounds"));
        assert!(ir.contains("__p_au32s__r_u32"));
        assert!(ir.contains("__p_au32m_u32__r_u32"));

        let byte_temp = ir
            .lines()
            .find(|line| line.contains(" = mul i64 ") && line.ends_with(", 4"))
            .and_then(|line| line.trim().split_once(" = ").map(|(name, _)| name))
            .expect("dynamic `u32` allocation computes byte size");
        assert!(
            !ir.lines().any(|line| {
                line.contains("@__sable_rt_fail_v1(i32 9")
                    && line.contains(&format!("i64 {byte_temp}, i64 0"))
            }),
            "OOM payload must report logical element length, not byte size"
        );

        let shared_start = ir
            .find("_shared_head__p_au32s__r_u32")
            .expect("shared helper is emitted");
        let shared_body = &ir[shared_start..];
        let shared_end = shared_body.find("\n}\n").expect("helper definition ends");
        assert!(!shared_body[..shared_end].contains("__sable_rt_array_free_v1"));
        assert_eq!(ir.matches("call void @__sable_rt_array_free_v1").count(), 2);
    }

    #[test]
    fn the_type_lowerings_answer_every_shape_and_name_the_ones_they_cannot_spell() {
        // A resource is representable, gated out of the backend by name, and
        // has no native spelling — so it is what the lowerings must answer
        // `None` for rather than abort on.
        let outside = Ty::Res(crate::ast::ResKind::OpenFile);
        assert_eq!(llvm_ty(outside.clone()), None);
        assert_eq!(type_code(outside.clone()), None);

        let span = Span::new(11, 17);
        let error = require_llvm_ty(outside, span, "parameter `handle`").unwrap_err();
        assert_eq!(error.len(), 1);
        assert_eq!(error[0].name, "internal.backend.type_lowering");
        assert_eq!(error[0].span, span);
        assert!(error[0].label.contains("parameter `handle`"));

        // Every shape the gates do admit still lowers, which is what keeps
        // that diagnostic unreachable from a source program.
        assert_eq!(llvm_ty(Ty::Bool).as_deref(), Some("i1"));
        assert_eq!(
            llvm_ty(Ty::array_ref(Ty::Bool, Mutability::Mut)).as_deref(),
            Some(LLVM_ARRAY_BOOL)
        );
        assert_eq!(
            type_code(Ty::array_ref(Ty::Bool, Mutability::Mut)).as_deref(),
            Some("abm")
        );
    }

    #[test]
    fn u32_array_backend_revalidates_borrow_positions_capabilities_and_aliases() {
        let owned = u32_array_ty(BindingMode::Owned);
        let shared = u32_array_ty(BindingMode::Shared);
        let mutable = u32_array_ty(BindingMode::Mut);
        let u32_ty = Ty::Int(IntTy::U32);

        let mut sink = function(
            "sink",
            Ty::Unit,
            vec![Stmt::Return {
                value: None,
                span: Span::new(0, 1),
            }],
        );
        sink.params = vec![
            parameter("left", mutable.clone()),
            parameter("right", shared.clone()),
        ];

        let caller_with = |first: Expr, second: Expr, source_mutable: bool| {
            function(
                "caller",
                Ty::Unit,
                vec![
                    Stmt::Decl {
                        ty: owned.clone(),
                        name: "values".into(),
                        name_span: Span::new(0, 1),
                        init: Some(u32_array_literal(&[1])),
                        mutable: source_mutable,
                    },
                    Stmt::ExprStmt(call_with("sink", Ty::Unit, vec![first, second])),
                    Stmt::Return {
                        value: None,
                        span: Span::new(0, 1),
                    },
                ],
            )
        };

        let alias = caller_with(
            u32_array_borrow("values", Mutability::Mut),
            u32_array_borrow("values", Mutability::Shared),
            true,
        );
        let error = emit_program(
            &program(vec![sink.clone(), alias]),
            1,
            &EmitOptions::default(),
        )
        .unwrap_err();
        assert!(error[0].label.contains("overlapping borrows"));

        let immutable = caller_with(
            u32_array_borrow("values", Mutability::Mut),
            u32_array_borrow("values", Mutability::Shared),
            false,
        );
        let error = emit_program(
            &program(vec![sink.clone(), immutable]),
            1,
            &EmitOptions::default(),
        )
        .unwrap_err();
        assert!(error[0].label.contains("non-mutable array place"));

        let forged_value = caller_with(
            typed_variable("values", mutable),
            u32_array_borrow("values", Mutability::Shared),
            true,
        );
        let error = emit_program(
            &program(vec![sink, forged_value]),
            1,
            &EmitOptions::default(),
        )
        .unwrap_err();
        assert!(error[0].label.contains("explicit named borrow"));

        let standalone = function(
            "standalone",
            Ty::Unit,
            vec![
                Stmt::Decl {
                    ty: owned,
                    name: "values".into(),
                    name_span: Span::new(0, 1),
                    init: Some(u32_array_literal(&[1])),
                    mutable: false,
                },
                Stmt::ExprStmt(u32_array_borrow("values", Mutability::Shared)),
                Stmt::Return {
                    value: None,
                    span: Span::new(0, 1),
                },
            ],
        );
        let error =
            emit_program(&program(vec![standalone]), 1, &EmitOptions::default()).unwrap_err();
        assert!(error[0].label.contains("outside the scalar"));

        let mut shared_store = function(
            "shared_store",
            Ty::Unit,
            vec![Stmt::Store {
                array: "values".into(),
                array_span: Span::new(0, 1),
                index: expression(ExprKind::IntLit(0), Ty::Int(IntTy::U64)),
                value: expression(ExprKind::IntLit(1), u32_ty),
            }],
        );
        shared_store.params = vec![parameter("values", shared)];
        let error =
            emit_program(&program(vec![shared_store]), 1, &EmitOptions::default()).unwrap_err();
        assert!(error[0].label.contains("shared borrow"));
    }

    #[test]
    fn owned_boolean_arrays_lower_bytes_guards_and_reverse_cleanups() {
        let array = bool_array_ty();
        let len = expression(ExprKind::IntLit(3), Ty::Int(IntTy::U64));
        let mut first_initializer = bool_array_literal(&[true, false]);
        first_initializer.span = Span::new(10, 11);
        let mut second_initializer =
            bool_array_alloc(len, expression(ExprKind::BoolLit(true), Ty::Bool));
        second_initializer.span = Span::new(20, 21);
        let mut f = function(
            "arrays",
            Ty::Bool,
            vec![
                Stmt::Decl {
                    ty: array.clone(),
                    name: "first".into(),
                    name_span: Span::new(0, 1),
                    init: Some(first_initializer),
                    mutable: true,
                },
                Stmt::Unsafe {
                    kw_span: Span::new(0, 1),
                    body: vec![Stmt::Decl {
                        ty: array,
                        name: "second".into(),
                        name_span: Span::new(0, 1),
                        init: Some(second_initializer),
                        mutable: true,
                    }],
                },
                Stmt::Store {
                    array: "second".into(),
                    array_span: Span::new(0, 1),
                    index: expression(ExprKind::IntLit(1), Ty::Int(IntTy::U64)),
                    value: expression(ExprKind::BoolLit(false), Ty::Bool),
                },
                Stmt::Return {
                    value: Some(expression(
                        ExprKind::Index {
                            array: "first".into(),
                            array_span: Span::new(0, 1),
                            index: Box::new(expression(ExprKind::IntLit(0), Ty::Int(IntTy::U64))),
                        },
                        Ty::Bool,
                    )),
                    span: Span::new(0, 1),
                },
            ],
        );
        f.params = Vec::new();

        let ir = emit_program(&program(vec![f]), 1, &EmitOptions::default()).unwrap();
        assert!(ir.contains("%sable.array.bool = type { ptr, i64 }"));
        assert!(ir.contains("declare ptr @__sable_rt_array_alloc_v1(i64)"));
        assert!(ir.contains("declare void @__sable_rt_array_free_v1(ptr)"));
        assert!(ir.contains("icmp ugt i64"));
        assert!(ir.contains(", 50000000"));
        assert!(ir.contains("@__sable_rt_fail_v1(i32 9, i32 0"));
        assert!(ir.contains("@__sable_rt_fail_v1(i32 10, i32 0"));
        assert!(ir.contains("getelementptr i8"));
        assert!(!ir.contains("getelementptr inbounds"));
        assert_eq!(ir.matches("call void @__sable_rt_array_free_v1").count(), 2);
        let return_value = ir.rfind(" = trunc i8").unwrap();
        let cleanup = &ir[return_value..];
        let second_slot_load = cleanup
            .find("load %sable.array.bool, ptr %v1")
            .expect("the later `second` declaration is dropped first");
        let first_drop = cleanup.find("call void @__sable_rt_array_free_v1").unwrap();
        let first_slot_load = cleanup[first_drop + 1..]
            .find("load %sable.array.bool, ptr %v0")
            .expect("the earlier `first` declaration is dropped second")
            + first_drop
            + 1;
        let second_drop = cleanup[first_drop + 1..]
            .find("call void @__sable_rt_array_free_v1")
            .unwrap()
            + first_drop
            + 1;
        let ret = cleanup.rfind("ret i1").unwrap();
        assert!(
            second_slot_load < first_drop
                && first_drop < first_slot_load
                && first_slot_load < second_drop
                && second_drop < ret
        );
    }

    #[test]
    fn boolean_array_effect_order_and_guard_dominance_are_structural() {
        let lit_first = function(
            "lit_first",
            Ty::Bool,
            vec![Stmt::Return {
                value: Some(expression(ExprKind::BoolLit(true), Ty::Bool)),
                span: Span::new(0, 1),
            }],
        );
        let lit_second = function(
            "lit_second",
            Ty::Bool,
            vec![Stmt::Return {
                value: Some(expression(ExprKind::BoolLit(false), Ty::Bool)),
                span: Span::new(0, 1),
            }],
        );
        let allocation_length = returning_function(
            "allocation_length",
            IntTy::U64,
            expression(ExprKind::IntLit(3), Ty::Int(IntTy::U64)),
        );
        let allocation_init = function(
            "allocation_init",
            Ty::Bool,
            vec![Stmt::Return {
                value: Some(expression(ExprKind::BoolLit(true), Ty::Bool)),
                span: Span::new(0, 1),
            }],
        );
        let store_index = returning_function(
            "store_index",
            IntTy::U64,
            expression(ExprKind::IntLit(1), Ty::Int(IntTy::U64)),
        );
        let store_value = function(
            "store_value",
            Ty::Bool,
            vec![Stmt::Return {
                value: Some(expression(ExprKind::BoolLit(false), Ty::Bool)),
                span: Span::new(0, 1),
            }],
        );
        let read_index = returning_function(
            "read_index",
            IntTy::U64,
            expression(ExprKind::IntLit(2), Ty::Int(IntTy::U64)),
        );

        let mut literal = expression(
            ExprKind::ArrayLit(vec![
                call("lit_first", Ty::Bool),
                call("lit_second", Ty::Bool),
            ]),
            bool_array_ty(),
        );
        literal.span = Span::new(10, 11);
        let mut allocated = bool_array_alloc(
            call("allocation_length", Ty::Int(IntTy::U64)),
            call("allocation_init", Ty::Bool),
        );
        allocated.span = Span::new(20, 21);
        let subject = function(
            "array_effects",
            Ty::Bool,
            vec![
                Stmt::Decl {
                    ty: bool_array_ty(),
                    name: "literal".into(),
                    name_span: Span::new(0, 1),
                    init: Some(literal),
                    mutable: false,
                },
                Stmt::Decl {
                    ty: bool_array_ty(),
                    name: "allocated".into(),
                    name_span: Span::new(0, 1),
                    init: Some(allocated),
                    mutable: true,
                },
                Stmt::Store {
                    array: "allocated".into(),
                    array_span: Span::new(0, 1),
                    index: call("store_index", Ty::Int(IntTy::U64)),
                    value: call("store_value", Ty::Bool),
                },
                Stmt::Return {
                    value: Some(expression(
                        ExprKind::Index {
                            array: "allocated".into(),
                            array_span: Span::new(0, 1),
                            index: Box::new(call("read_index", Ty::Int(IntTy::U64))),
                        },
                        Ty::Bool,
                    )),
                    span: Span::new(0, 1),
                },
            ],
        );

        let subject_symbol = mangle(&subject).expect("test subject has a mangled symbol");
        let call_marker = |function: &Fn| {
            format!(
                "call {} @{}()",
                llvm_ty(function.ret.clone()).expect("test helper has an LLVM return type"),
                mangle(function).expect("test helper has a mangled symbol")
            )
        };
        let lit_first_call = call_marker(&lit_first);
        let lit_second_call = call_marker(&lit_second);
        let length_call = call_marker(&allocation_length);
        let init_call = call_marker(&allocation_init);
        let store_index_call = call_marker(&store_index);
        let store_value_call = call_marker(&store_value);
        let read_index_call = call_marker(&read_index);

        let ir = emit_program(
            &program(vec![
                lit_first,
                lit_second,
                allocation_length,
                allocation_init,
                store_index,
                store_value,
                read_index,
                subject,
            ]),
            1,
            &EmitOptions::default(),
        )
        .unwrap();
        let definition = format!("define internal i1 @{subject_symbol}()");
        let subject = &ir[ir.find(&definition).unwrap()..];
        let subject = &subject[..subject.find("\n}\n").unwrap() + 3];

        let literal_first = subject.find(&lit_first_call).unwrap();
        let literal_second = subject.find(&lit_second_call).unwrap();
        let literal_alloc = subject.find("call ptr @__sable_rt_array_alloc_v1").unwrap();
        assert!(literal_first < literal_second && literal_second < literal_alloc);

        let length = subject.find(&length_call).unwrap();
        let literal_first_gep =
            subject[literal_alloc..].find("getelementptr i8").unwrap() + literal_alloc;
        let literal_first_write =
            subject[literal_first_gep..].find("store i8").unwrap() + literal_first_gep;
        let literal_second_gep = subject[literal_first_write + 1..]
            .find("getelementptr i8")
            .unwrap()
            + literal_first_write
            + 1;
        let literal_second_write =
            subject[literal_second_gep..].find("store i8").unwrap() + literal_second_gep;
        assert!(
            literal_alloc < literal_first_gep
                && literal_first_gep < literal_first_write
                && literal_first_write < literal_second_gep
                && literal_second_gep < literal_second_write
                && literal_second_write < length
        );
        let init = subject.find(&init_call).unwrap();
        let cap = subject[init..].find("icmp ugt i64").unwrap() + init;
        let cap_guard = subject[cap..].find("br i1").unwrap() + cap;
        let allocation = subject[literal_alloc + 1..]
            .find("call ptr @__sable_rt_array_alloc_v1")
            .unwrap()
            + literal_alloc
            + 1;
        assert!(literal_alloc < length && length < init && init < cap && cap < cap_guard);
        assert!(cap_guard < allocation);

        let null_check = subject[allocation..].find("icmp eq ptr").unwrap() + allocation;
        let null_guard = subject[null_check..].find("br i1").unwrap() + null_check;
        let fill_gep = subject[null_guard..].find("getelementptr i8").unwrap() + null_guard;
        assert!(allocation < null_check && null_check < null_guard && null_guard < fill_gep);

        let store_index = subject.find(&store_index_call).unwrap();
        let store_value = subject.find(&store_value_call).unwrap();
        let store_oob = subject[store_value..].find("icmp uge i64").unwrap() + store_value;
        let store_guard = subject[store_oob..].find("br i1").unwrap() + store_oob;
        let store_gep = subject[store_guard..].find("getelementptr i8").unwrap() + store_guard;
        let store_write = subject[store_gep..].find("store i8").unwrap() + store_gep;
        assert!(
            fill_gep < store_index
                && store_index < store_value
                && store_value < store_oob
                && store_oob < store_guard
                && store_guard < store_gep
                && store_gep < store_write
        );

        let read_index = subject.find(&read_index_call).unwrap();
        let read_descriptor = subject[read_index..]
            .find("load %sable.array.bool")
            .unwrap()
            + read_index;
        let read_oob = subject[read_descriptor..].find("icmp uge i64").unwrap() + read_descriptor;
        let read_guard = subject[read_oob..].find("br i1").unwrap() + read_oob;
        let read_gep = subject[read_guard..].find("getelementptr i8").unwrap() + read_guard;
        let read_byte = subject[read_gep..].find("load i8").unwrap() + read_gep;
        assert!(
            store_write < read_index
                && read_index < read_descriptor
                && read_descriptor < read_oob
                && read_oob < read_guard
                && read_guard < read_gep
                && read_gep < read_byte
        );
    }

    #[test]
    fn planned_nested_return_route_drops_inner_then_outer_owner() {
        let array = bool_array_ty();
        let mut condition = expression(ExprKind::BoolLit(true), Ty::Bool);
        condition.span = Span::new(10, 11);
        let subject = function(
            "planned_return_cleanup",
            Ty::Bool,
            vec![
                Stmt::Decl {
                    ty: array.clone(),
                    name: "outer".into(),
                    name_span: Span::new(1, 2),
                    init: Some(bool_array_literal(&[true])),
                    mutable: false,
                },
                Stmt::If {
                    cond: condition,
                    then_block: vec![
                        Stmt::Decl {
                            ty: array,
                            name: "inner".into(),
                            name_span: Span::new(3, 4),
                            init: Some(bool_array_literal(&[false])),
                            mutable: false,
                        },
                        Stmt::Return {
                            value: Some(expression(ExprKind::BoolLit(true), Ty::Bool)),
                            span: Span::new(20, 21),
                        },
                    ],
                    else_block: None,
                },
                Stmt::Return {
                    value: Some(expression(ExprKind::BoolLit(false), Ty::Bool)),
                    span: Span::new(30, 31),
                },
            ],
        );

        let ir = emit_program(&program(vec![subject]), 1, &EmitOptions::default()).unwrap();
        let branch = ir.find("if.then").expect("then branch");
        let branch_ir = &ir[branch..];
        let inner = branch_ir
            .find("load %sable.array.bool, ptr %v1")
            .expect("inner owner cleanup");
        let inner_free = branch_ir[inner..]
            .find("call void @__sable_rt_array_free_v1")
            .expect("inner owner free")
            + inner;
        let outer = branch_ir[inner_free..]
            .find("load %sable.array.bool, ptr %v0")
            .expect("outer owner cleanup")
            + inner_free;
        let outer_free = branch_ir[outer..]
            .find("call void @__sable_rt_array_free_v1")
            .expect("outer owner free")
            + outer;
        let returned = branch_ir[outer_free..]
            .find("ret i1 1")
            .expect("then return")
            + outer_free;
        assert!(inner < inner_free && inner_free < outer && outer < outer_free);
        assert!(outer_free < returned);
    }

    #[test]
    fn exact_route_skips_a_cleanup_candidate_whose_declaration_was_not_reached() {
        let subject = function(
            "unreached_cleanup",
            Ty::Unit,
            vec![
                Stmt::Return {
                    value: None,
                    span: Span::new(10, 11),
                },
                Stmt::Decl {
                    ty: bool_array_ty(),
                    name: "after_return".into(),
                    name_span: Span::new(20, 21),
                    init: Some(bool_array_literal(&[true])),
                    mutable: false,
                },
            ],
        );
        let program = program(vec![subject]);
        let control = ControlProgram::build(&program).expect("typed control plan");
        let ir = emit_program_with_control(&program, &control, 1, &EmitOptions::default())
            .expect("exact checked control lowering");

        assert!(!ir.contains("call ptr @__sable_rt_array_alloc_v1"));
        assert!(!ir.contains("call void @__sable_rt_array_free_v1"));
        assert!(ir.contains("ret void"));
    }

    #[test]
    fn unsupported_exposure_consumes_its_retained_plan_before_native_refusal() {
        let exposure_span = Span::new(20, 21);
        let mut subject = function(
            "exposure_boundary",
            Ty::Unit,
            vec![Stmt::Expose {
                kw_span: exposure_span,
                array: "bytes".into(),
                array_span: Span::new(21, 22),
                mutable: false,
                ptr: "pointer".into(),
                ptr_span: Span::new(22, 23),
                res: "memory".into(),
                res_span: Span::new(23, 24),
                body: Vec::new(),
            }],
        );
        subject.params = vec![parameter(
            "bytes",
            Ty::array_ref(Ty::Int(IntTy::U8), Mutability::Shared),
        )];
        let source = program(vec![subject]);
        let control = ControlProgram::build(&source).expect("exact exposure control plan");

        let refusal = emit_program_with_control(&source, &control, 100, &EmitOptions::default())
            .expect_err("byte-array exposure remains outside LLVM admission");
        assert_eq!(refusal[0].name, "backend.unsupported");

        let mut changed = source.clone();
        let Stmt::Expose { ptr, .. } = &mut changed.fns[0].body[0] else {
            unreachable!()
        };
        *ptr = "changed_pointer".into();
        let mismatch = emit_program_with_control(&changed, &control, 100, &EmitOptions::default())
            .expect_err("a changed exposure may not reuse the retained native boundary");
        assert_eq!(mismatch[0].name, "internal.control_plan_invalid");
    }

    #[test]
    fn llvm_operations_and_entry_ledger_reject_changed_retained_trap_sites() {
        let trap_span = Span::new(20, 21);
        let arithmetic = |op| Expr {
            kind: ExprKind::Binary {
                op,
                op_span: trap_span,
                lhs: Box::new(Expr {
                    kind: ExprKind::IntLit(4),
                    span: Span::new(22, 23),
                    ty: Some(Ty::Int(IntTy::I32)),
                }),
                rhs: Box::new(Expr {
                    kind: ExprKind::IntLit(2),
                    span: Span::new(24, 25),
                    ty: Some(Ty::Int(IntTy::I32)),
                }),
            },
            span: trap_span,
            ty: Some(Ty::Int(IntTy::I32)),
        };
        let original = arithmetic(BinOp::Add);
        let source = program(vec![function(
            "retained_trap",
            Ty::Unit,
            vec![Stmt::ExprStmt(original.clone())],
        )]);
        let control = ControlProgram::build(&source).unwrap();

        let mut support = ModuleSupport::default();
        let emitter =
            FunctionEmitter::new(&source, Some(&control), &source.fns[0], &mut support).unwrap();
        let mismatch = emitter
            .consume_expression_trap_sites(&arithmetic(BinOp::Sub))
            .expect_err("the lowering operation must exact-lookup its sealed kind");
        assert_eq!(mismatch[0].name, "internal.control_plan_invalid");
        assert!(mismatch[0].label.contains("SubOverflow"));

        let mut deleted = source.clone();
        deleted.fns[0].body.clear();
        let missing = emit_program_with_control(&deleted, &control, 1, &EmitOptions::default())
            .expect_err("entry reconciliation must find even unreachable retained sites");
        assert_eq!(missing[0].name, "internal.control_plan_invalid");
        assert!(missing[0].label.contains("planned trap site"));

        let branch_anchor = Span::new(30, 31);
        let scoped_source = program(vec![function(
            "scoped_trap",
            Ty::Unit,
            vec![Stmt::If {
                cond: Expr {
                    kind: ExprKind::BoolLit(true),
                    span: branch_anchor,
                    ty: Some(Ty::Bool),
                },
                then_block: vec![Stmt::ExprStmt(original.clone())],
                else_block: Some(Vec::new()),
            }],
        )]);
        let scoped_control = ControlProgram::build(&scoped_source).unwrap();
        let mut scoped_support = ModuleSupport::default();
        let mut scoped_emitter = FunctionEmitter::new(
            &scoped_source,
            Some(&scoped_control),
            &scoped_source.fns[0],
            &mut scoped_support,
        )
        .unwrap();
        let branch = scoped_emitter
            .control
            .branch(scoped_emitter.control.body_scope(), branch_anchor, true)
            .unwrap();
        let then_scope = branch.then_arm().scope();
        let else_scope = branch.else_arm().unwrap().scope();
        scoped_emitter.cleanup_scopes.last_mut().unwrap().id = then_scope;
        scoped_emitter
            .consume_expression_trap_sites(&original)
            .expect("the operation consumes the exact retained branch site");
        scoped_emitter.cleanup_scopes.last_mut().unwrap().id = else_scope;
        let moved = scoped_emitter
            .consume_expression_trap_sites(&original)
            .expect_err("a sibling branch may not consume the retained site");
        assert_eq!(moved[0].name, "internal.control_plan_invalid");
        assert!(moved[0].label.contains("active lexical scope"));
    }

    #[test]
    fn empty_boolean_array_bypasses_both_runtime_hooks() {
        let f = function(
            "empty",
            Ty::Unit,
            vec![Stmt::Decl {
                ty: bool_array_ty(),
                name: "values".into(),
                name_span: Span::new(0, 1),
                init: Some(bool_array_literal(&[])),
                mutable: false,
            }],
        );
        let ir = emit_program(&program(vec![f]), 1, &EmitOptions::default()).unwrap();
        assert!(!ir.contains("call ptr @__sable_rt_array_alloc_v1"));
        // A conditional drop is emitted, but its null edge bypasses the call.
        let null_check = ir.find("icmp eq ptr").unwrap();
        let free_call = ir.find("call void @__sable_rt_array_free_v1").unwrap();
        assert!(null_check < free_call);
    }

    #[test]
    fn boolean_array_transport_boundaries_remain_closed_on_forged_ast() {
        let array = bool_array_ty();
        let mut parameter_fn = function(
            "parameter",
            Ty::Unit,
            vec![Stmt::Return {
                value: None,
                span: Span::new(0, 1),
            }],
        );
        parameter_fn.params = vec![parameter("values", array.clone())];
        assert!(emit_program(&program(vec![parameter_fn]), 1, &EmitOptions::default()).is_err());

        let returned = function(
            "returned",
            array.clone(),
            vec![Stmt::Return {
                value: Some(bool_array_literal(&[true])),
                span: Span::new(0, 1),
            }],
        );
        assert!(emit_program(&program(vec![returned]), 1, &EmitOptions::default()).is_err());

        let moved = function(
            "moved",
            Ty::Unit,
            vec![
                Stmt::Decl {
                    ty: array.clone(),
                    name: "source".into(),
                    name_span: Span::new(0, 1),
                    init: Some(bool_array_literal(&[true])),
                    mutable: false,
                },
                Stmt::Decl {
                    ty: array.clone(),
                    name: "dest".into(),
                    name_span: Span::new(0, 1),
                    init: Some(typed_variable("source", array)),
                    mutable: false,
                },
            ],
        );
        let error = emit_program(&program(vec![moved]), 1, &EmitOptions::default()).unwrap_err();
        assert!(error[0].label.contains("fresh literal"));
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
                lhs: Box::new(expression(ExprKind::IntLit(1), int.clone())),
                rhs: Box::new(expression(ExprKind::IntLit(2), int.clone())),
            },
            int.clone(),
        );
        let f = function(
            "add",
            int.clone(),
            vec![Stmt::Return {
                value: Some(first_binary),
                span: Span::new(0, 1),
            }],
        );
        let second_binary = expression(
            ExprKind::Binary {
                op: BinOp::Add,
                op_span: Span::new(0, 1),
                lhs: Box::new(expression(ExprKind::IntLit(3), int.clone())),
                rhs: Box::new(expression(ExprKind::IntLit(4), int.clone())),
            },
            int.clone(),
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
            Ty::array_ref(Ty::Int(IntTy::I32), crate::ast::Mutability::Shared),
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
                    ty: Ty::array(Ty::Int(IntTy::I32)),
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
            int.clone(),
            vec![
                Stmt::If {
                    cond: expression(ExprKind::Var("flag".into()), Ty::Bool),
                    then_block: vec![Stmt::Return {
                        value: Some(expression(ExprKind::IntLit(1), int.clone())),
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
            int.clone(),
            vec![
                Stmt::While {
                    cond: expression(ExprKind::Var("keep_going".into()), Ty::Bool),
                    invariants: Vec::new(),
                    variant: None,
                    kw_span: Span::new(0, 1),
                    body: vec![Stmt::Return {
                        value: Some(expression(ExprKind::IntLit(7), int.clone())),
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

    #[test]
    fn fixed_owner_class_lowers_constructor_shared_borrow_and_nested_cleanup() {
        let ir = emit_program(
            &fixed_class_program(),
            1,
            &EmitOptions {
                entry: Some("entry".into()),
            },
        )
        .unwrap();

        assert!(ir.contains("%sable.class.0 = type { %sable.array.u32 }"));
        assert!(ir.contains("define internal void @__sable_v0_c0_i_3_new__p_(ptr %self)"));
        assert!(ir.contains("call void @__sable_v0_c0_i_3_new__p_(ptr %v0)"));
        assert!(ir.contains("call void @__sable_v0_f_7_inspect__p_c0s__r_v(ptr %v0)"));
        assert!(ir.contains("getelementptr %sable.class.0, ptr %v0, i32 0, i32 0"));
        assert!(ir.contains("call void @__sable_rt_array_free_v1(ptr"));
    }

    #[test]
    fn initializer_field_action_stages_then_conditionally_drops_neutral_storage_and_installs() {
        let result = fixed_class_program();
        let control = ControlProgram::build(&result).expect("exact field-assignment action");
        let ir = emit_program_with_control(
            &result,
            &control,
            1,
            &EmitOptions {
                entry: Some("entry".into()),
            },
        )
        .expect("u32 field initializer is in the native subset");
        let symbol = mangle_initializer(0, &result.classes[0].inits[0]).unwrap();
        let start = ir
            .find(&format!("define internal void @{symbol}"))
            .expect("initializer definition");
        let end = ir[start..].find("\n}\n").unwrap() + start;
        let initializer = &ir[start..end];

        let staging = initializer
            .find("alloca %sable.array.u32")
            .expect("retained field temporary has one entry slot");
        let neutral = initializer
            .find("store %sable.class.0 zeroinitializer, ptr %self")
            .expect("constructor starts with every field dynamically absent");
        let rhs = initializer
            .find("call ptr @__sable_rt_array_alloc_v1")
            .expect("RHS is fully evaluated into the planned staging value");
        let drop_guard = initializer[rhs..]
            .find("icmp eq ptr")
            .map(|offset| rhs + offset)
            .expect("old neutral field is dropped through a null-safe presence guard");
        let drop_done = initializer[drop_guard..]
            .find("class.free.done:")
            .map(|offset| drop_guard + offset)
            .expect("conditional drop rejoins before install");
        let install = initializer[drop_done..]
            .find("load %sable.array.u32, ptr")
            .map(|offset| drop_done + offset)
            .expect("staged descriptor is loaded only after the old drop");
        let clear = initializer[install..]
            .find("store %sable.array.u32 zeroinitializer")
            .map(|offset| install + offset)
            .expect("install consumes and neutralizes the planned temporary");
        assert!(staging < neutral && neutral < rhs && rhs < drop_guard);
        assert!(drop_guard < drop_done && drop_done < install && install < clear);
    }

    #[test]
    fn fixed_owner_cleanup_consumes_the_checked_class_drop_plan() {
        let mut result = fixed_class_program();
        result.classes[0].invariants.push(Clause {
            kind: ClauseKind::Invariant,
            label: Some("native_nat".into()),
            fact: false,
            unfold: false,
            text: "true".into(),
            span: Span::new(20, 21),
            line_span: Span::new(20, 21),
        });
        let control = ControlProgram::build(&result).expect("exact concrete class-drop plan");
        let ir = emit_program_with_control(
            &result,
            &control,
            1,
            &EmitOptions {
                entry: Some("entry".into()),
            },
        )
        .expect("verified native invariants are explicitly erased");
        assert!(ir.contains("; class-drop invariant for `Nat` erased after verification"));
        assert!(ir.contains("; empty class-drop deinitializer destructor `Nat::deinit`"));

        let mut mutated = result.clone();
        mutated.classes[0].fields[0].span = Span::new(90, 91);
        let error = emit_program_with_control(
            &mutated,
            &control,
            1,
            &EmitOptions {
                entry: Some("entry".into()),
            },
        )
        .expect_err("a mutated class field must not reuse a checked drop plan");
        assert_eq!(error[0].name, "internal.control_plan_invalid");
        assert!(error[0].title.contains("control plan"));
        assert!(error[0].label.contains("no longer matches its declaration"));
    }

    #[test]
    fn llvm_class_drop_phases_keep_reverse_order_and_reject_executable_deinit() {
        let mut ordered = fixed_class_program();
        ordered.classes[0].fields.push(Field {
            name: "tail".into(),
            ty: Ty::Int(IntTy::U64),
            span: Span::new(30, 31),
            must_consume: false,
        });
        let control = ControlProgram::build(&ordered).expect("synthetic ordered class-drop plan");
        let mut support = ModuleSupport::default();
        let emitter = FunctionEmitter::new(&ordered, Some(&control), &ordered.fns[1], &mut support)
            .expect("entry body has exact control");
        let mut ir = String::new();
        emitter
            .emit(&mut ir)
            .expect("the direct emitter supports integer and u32-array field cleanup");
        let tail = ir
            .find("getelementptr %sable.class.0, ptr %v0, i32 0, i32 1")
            .expect("last-declared scalar field phase");
        let limbs = ir[tail..]
            .find("getelementptr %sable.class.0, ptr %v0, i32 0, i32 0")
            .map(|offset| tail + offset)
            .expect("first-declared array field phase");
        assert!(tail < limbs);

        let mut executable = fixed_class_program();
        executable.classes[0].deinit = Some(vec![Stmt::ExprStmt(expression(
            ExprKind::BoolLit(true),
            Ty::Bool,
        ))]);
        let control =
            ControlProgram::build(&executable).expect("non-empty deinit remains a planned phase");
        let mut support = ModuleSupport::default();
        let emitter = FunctionEmitter::new(
            &executable,
            Some(&control),
            &executable.fns[1],
            &mut support,
        )
        .expect("entry body has exact control");
        let mut ignored = String::new();
        let error = emitter
            .emit(&mut ignored)
            .expect_err("LLVM must reject, not erase, an executable deinitializer");
        assert_eq!(error[0].name, "backend.control_plan_unsupported");
        assert!(error[0].title.contains("class deinitializer"));
        assert!(error[0].label.contains("non-empty body"));
    }

    #[test]
    fn fixed_owner_class_returns_and_named_moves_use_destination_passing() {
        let mut result = fixed_class_program();
        result.fns.push(function(
            "make",
            Ty::Class(0),
            vec![Stmt::Return {
                value: Some(fixed_class_constructor()),
                span: Span::new(0, 1),
            }],
        ));
        result.fns.push(function(
            "forward",
            Ty::Class(0),
            vec![Stmt::Return {
                value: Some(call("make", Ty::Class(0))),
                span: Span::new(0, 1),
            }],
        ));
        result.fns.push(function(
            "move_local",
            Ty::Class(0),
            vec![
                Stmt::VarDecl {
                    ty: Some(Ty::Class(0)),
                    name: "first".into(),
                    name_span: Span::new(0, 1),
                    init: call("forward", Ty::Class(0)),
                    mutable: false,
                },
                Stmt::VarDecl {
                    ty: Some(Ty::Class(0)),
                    name: "second".into(),
                    name_span: Span::new(0, 1),
                    init: typed_variable("first", Ty::Class(0)),
                    mutable: false,
                },
                Stmt::Return {
                    value: Some(typed_variable("second", Ty::Class(0))),
                    span: Span::new(0, 1),
                },
            ],
        ));
        let mut branch_move = function(
            "branch_move",
            Ty::Class(0),
            vec![
                Stmt::VarDecl {
                    ty: Some(Ty::Class(0)),
                    name: "owner".into(),
                    name_span: Span::new(0, 1),
                    init: call("move_local", Ty::Class(0)),
                    mutable: false,
                },
                Stmt::If {
                    cond: typed_variable("early", Ty::Bool),
                    then_block: vec![Stmt::Return {
                        value: Some(typed_variable("owner", Ty::Class(0))),
                        span: Span::new(0, 1),
                    }],
                    else_block: None,
                },
                Stmt::Return {
                    value: Some(typed_variable("owner", Ty::Class(0))),
                    span: Span::new(0, 1),
                },
            ],
        );
        branch_move.params = vec![parameter("early", Ty::Bool)];
        result.fns.push(branch_move);
        let entry = &mut result.fns[1];
        entry.body[0] = Stmt::VarDecl {
            ty: Some(Ty::Class(0)),
            name: "value".into(),
            name_span: Span::new(0, 1),
            init: call_with(
                "branch_move",
                Ty::Class(0),
                vec![expression(ExprKind::BoolLit(true), Ty::Bool)],
            ),
            mutable: false,
        };

        let ir = emit_program(
            &result,
            1,
            &EmitOptions {
                entry: Some("entry".into()),
            },
        )
        .unwrap();
        assert!(ir.contains("define internal void @__sable_v0_f_4_make__p___r_c0o(ptr %result)"));
        assert!(
            ir.contains("define internal void @__sable_v0_f_7_forward__p___r_c0o(ptr %result)")
        );
        assert!(ir.contains("call void @__sable_v0_f_4_make__p___r_c0o(ptr %result)"));
        assert!(ir.contains("call void @__sable_v0_f_10_move_local__p___r_c0o(ptr "));
        assert!(ir.contains("call void @__sable_v0_f_11_branch_move__p_b__r_c0o(ptr %v0, i1 1)"));
        assert!(ir.contains("store %sable.class.0 zeroinitializer, ptr"));
    }

    #[test]
    fn fixed_owner_class_move_validation_rejects_stale_borrows_and_cfg_shape_mismatches() {
        let options = |entry: &str| EmitOptions {
            entry: Some(entry.into()),
        };

        let mut stale_borrow = fixed_class_program();
        stale_borrow.fns.push(function(
            "stale_borrow",
            Ty::Int(IntTy::I32),
            vec![
                Stmt::VarDecl {
                    ty: Some(Ty::Class(0)),
                    name: "first".into(),
                    name_span: Span::new(0, 1),
                    init: fixed_class_constructor(),
                    mutable: false,
                },
                Stmt::VarDecl {
                    ty: Some(Ty::Class(0)),
                    name: "second".into(),
                    name_span: Span::new(0, 1),
                    init: typed_variable("first", Ty::Class(0)),
                    mutable: false,
                },
                Stmt::ExprStmt(call_with(
                    "inspect",
                    Ty::Unit,
                    vec![fixed_class_borrow("first")],
                )),
                Stmt::Return {
                    value: Some(expression(ExprKind::IntLit(0.into()), Ty::Int(IntTy::I32))),
                    span: Span::new(0, 1),
                },
            ],
        ));
        let error = emit_program(&stale_borrow, 1, &options("stale_borrow")).unwrap_err();
        assert_eq!(error[0].name, "backend.class_moved");

        let mut mismatched_branches = fixed_class_program();
        mismatched_branches.fns.push(function(
            "mismatched_branches",
            Ty::Int(IntTy::I32),
            vec![
                Stmt::VarDecl {
                    ty: Some(Ty::Class(0)),
                    name: "first".into(),
                    name_span: Span::new(0, 1),
                    init: fixed_class_constructor(),
                    mutable: false,
                },
                Stmt::If {
                    cond: expression(ExprKind::BoolLit(true), Ty::Bool),
                    then_block: vec![Stmt::VarDecl {
                        ty: Some(Ty::Class(0)),
                        name: "second".into(),
                        name_span: Span::new(0, 1),
                        init: typed_variable("first", Ty::Class(0)),
                        mutable: false,
                    }],
                    else_block: None,
                },
                Stmt::Return {
                    value: Some(expression(ExprKind::IntLit(0.into()), Ty::Int(IntTy::I32))),
                    span: Span::new(0, 1),
                },
            ],
        ));
        let error =
            emit_program(&mismatched_branches, 1, &options("mismatched_branches")).unwrap_err();
        assert_eq!(error[0].name, "backend.class_branch_shape");
    }

    #[test]
    fn mutable_fixed_owner_reassignment_uses_scratch_before_dropping_the_old_value() {
        let mut result = fixed_class_program();
        let mut refresh = function(
            "refresh",
            Ty::Class(0),
            vec![Stmt::Return {
                value: Some(fixed_class_constructor()),
                span: Span::new(0, 1),
            }],
        );
        refresh.params = vec![parameter(
            "old",
            Ty::borrow(Mutability::Shared, Ty::Class(0)),
        )];
        result.fns.push(refresh);

        let entry = &mut result.fns[1];
        let Stmt::VarDecl { mutable, .. } = &mut entry.body[0] else {
            unreachable!()
        };
        *mutable = true;
        entry.body.insert(
            1,
            Stmt::Assign {
                name: "value".into(),
                name_span: Span::new(0, 1),
                value: call_with("refresh", Ty::Class(0), vec![fixed_class_borrow("value")]),
            },
        );

        let ir = emit_program(
            &result,
            1,
            &EmitOptions {
                entry: Some("entry".into()),
            },
        )
        .unwrap();
        let call = ir
            .find("call void @__sable_v0_f_7_refresh__p_c0s__r_c0o(ptr %v1, ptr %v0)")
            .expect("replacement is evaluated into the entry scratch");
        let drop = ir[call..]
            .find("call void @__sable_rt_array_free_v1")
            .map(|offset| call + offset)
            .expect("the old owner is dropped after replacement evaluation");
        let transfer = ir[drop..]
            .find("store %sable.class.0 zeroinitializer, ptr %v1")
            .map(|offset| drop + offset)
            .expect("scratch is transferred and neutralized after the drop");
        assert!(call < drop && drop < transfer);
        assert_eq!(ir.matches("%v1 = alloca %sable.class.0").count(), 1);
    }

    #[test]
    fn planned_replacement_of_a_moved_out_class_drops_the_neutral_destination_then_installs() {
        let mut result = fixed_class_program();
        let entry = &mut result.fns[1];
        let Stmt::VarDecl { mutable, .. } = &mut entry.body[0] else {
            unreachable!()
        };
        *mutable = true;
        entry.body.insert(
            1,
            Stmt::VarDecl {
                ty: Some(Ty::Class(0)),
                name: "moved".into(),
                name_span: Span::new(10, 11),
                init: typed_variable("value", Ty::Class(0)),
                mutable: false,
            },
        );
        entry.body.insert(
            2,
            Stmt::Assign {
                name: "value".into(),
                name_span: Span::new(20, 21),
                value: {
                    let mut replacement = fixed_class_constructor();
                    replacement.span = Span::new(22, 23);
                    replacement
                },
            },
        );
        let entry_symbol = mangle(entry).unwrap();
        let initializer_symbol = mangle_initializer(0, &result.classes[0].inits[0]).unwrap();
        let control = ControlProgram::build(&result).expect("exact assignment actions");
        let ir = emit_program_with_control(
            &result,
            &control,
            1,
            &EmitOptions {
                entry: Some("entry".into()),
            },
        )
        .unwrap();
        let start = ir
            .find(&format!("define internal i32 @{entry_symbol}"))
            .unwrap();
        let end = ir[start..].find("\n}\n").unwrap() + start;
        let entry_ir = &ir[start..end];

        let moved_out = entry_ir
            .find("store %sable.class.0 zeroinitializer, ptr %v0")
            .expect("the first move neutralizes its source");
        let replacement = entry_ir[moved_out..]
            .find(&format!("call void @{initializer_symbol}(ptr %v2)"))
            .map(|offset| moved_out + offset)
            .expect("the replacement is evaluated into its planned temporary");
        let planned_drop = entry_ir[replacement..]
            .find("getelementptr %sable.class.0, ptr %v0")
            .map(|offset| replacement + offset)
            .expect("the planned old-destination drop still runs null-safely");
        let staged_load = entry_ir[planned_drop..]
            .find("load %sable.class.0, ptr %v2")
            .map(|offset| planned_drop + offset)
            .expect("the staged replacement is installed after the drop");
        let staged_clear = entry_ir[staged_load..]
            .find("store %sable.class.0 zeroinitializer, ptr %v2")
            .map(|offset| staged_load + offset)
            .expect("install consumes the planned temporary");
        assert!(moved_out < replacement && replacement < planned_drop);
        assert!(planned_drop < staged_load && staged_load < staged_clear);
    }

    #[test]
    fn trapping_class_rhs_precedes_the_planned_old_destination_drop() {
        let mut result = fixed_class_program();
        let mut may_trap = function(
            "may_trap",
            Ty::Class(0),
            vec![
                Stmt::ExprStmt(expression(
                    ExprKind::Binary {
                        op: BinOp::Div,
                        op_span: Span::new(30, 31),
                        lhs: Box::new(expression(ExprKind::IntLit(1.into()), Ty::Int(IntTy::I32))),
                        rhs: Box::new(expression(
                            ExprKind::Var("divisor".into()),
                            Ty::Int(IntTy::I32),
                        )),
                    },
                    Ty::Int(IntTy::I32),
                )),
                Stmt::Return {
                    value: Some(fixed_class_constructor()),
                    span: Span::new(40, 41),
                },
            ],
        );
        may_trap.params = vec![parameter("divisor", Ty::Int(IntTy::I32))];
        let may_trap_symbol = mangle(&may_trap).unwrap();
        result.fns.push(may_trap);

        let entry = &mut result.fns[1];
        let Stmt::VarDecl { mutable, .. } = &mut entry.body[0] else {
            unreachable!()
        };
        *mutable = true;
        entry.body.insert(
            1,
            Stmt::Assign {
                name: "value".into(),
                name_span: Span::new(50, 51),
                value: call_with(
                    "may_trap",
                    Ty::Class(0),
                    vec![expression(ExprKind::IntLit(0.into()), Ty::Int(IntTy::I32))],
                ),
            },
        );
        let entry_symbol = mangle(entry).unwrap();
        let control = ControlProgram::build(&result).expect("exact assignment actions");
        let ir = emit_program_with_control(
            &result,
            &control,
            1,
            &EmitOptions {
                entry: Some("entry".into()),
            },
        )
        .unwrap();
        let start = ir
            .find(&format!("define internal i32 @{entry_symbol}"))
            .unwrap();
        let end = ir[start..].find("\n}\n").unwrap() + start;
        let entry_ir = &ir[start..end];
        let rhs = entry_ir
            .find(&format!("call void @{may_trap_symbol}(ptr %v1, i32 0)"))
            .expect("potentially trapping RHS fills the planned temporary");
        let old_drop = entry_ir[rhs..]
            .find("getelementptr %sable.class.0, ptr %v0")
            .map(|offset| rhs + offset)
            .expect("old destination drop follows a successful RHS return");
        assert!(rhs < old_drop);

        let callee_start = ir
            .find(&format!("define internal void @{may_trap_symbol}"))
            .unwrap();
        let callee_end = ir[callee_start..].find("\n}\n").unwrap() + callee_start;
        assert!(ir[callee_start..callee_end].contains("@__sable_rt_fail_v1"));
    }

    #[test]
    fn uninitialized_fixed_owner_uses_a_neutral_slot_on_optional_paths() {
        fn function_ir<'a>(ir: &'a str, symbol: &str) -> &'a str {
            let start = ir
                .find(&format!("define internal i32 @{symbol}"))
                .expect("subject definition");
            let end = ir[start..]
                .find("\n}\n")
                .map(|offset| start + offset)
                .expect("subject definition end");
            &ir[start..end]
        }

        fn uninitialized_nat(name: &str, control: Stmt) -> Fn {
            let mut function = function(
                name,
                Ty::Int(IntTy::I32),
                vec![
                    Stmt::Decl {
                        ty: Ty::Class(0),
                        name: "value".into(),
                        name_span: Span::new(2, 3),
                        init: None,
                        mutable: true,
                    },
                    control,
                    Stmt::Return {
                        value: Some(expression(ExprKind::IntLit(0.into()), Ty::Int(IntTy::I32))),
                        span: Span::new(30, 31),
                    },
                ],
            );
            function.span = Span::new(1, 40);
            function
        }

        let assign = || Stmt::Assign {
            name: "value".into(),
            name_span: Span::new(12, 13),
            value: fixed_class_constructor(),
        };
        let mut branch_condition = expression(ExprKind::BoolLit(false), Ty::Bool);
        branch_condition.span = Span::new(10, 11);
        let branch = uninitialized_nat(
            "optional_branch_init",
            Stmt::If {
                cond: branch_condition,
                then_block: vec![assign()],
                else_block: None,
            },
        );
        let mut loop_condition = expression(ExprKind::BoolLit(false), Ty::Bool);
        loop_condition.span = Span::new(20, 21);
        let looped = uninitialized_nat(
            "optional_loop_init",
            Stmt::While {
                cond: loop_condition,
                invariants: Vec::new(),
                variant: None,
                kw_span: Span::new(19, 20),
                body: vec![assign()],
            },
        );

        let branch_symbol = mangle(&branch).expect("branch subject has a symbol");
        let loop_symbol = mangle(&looped).expect("loop subject has a symbol");
        let mut result = fixed_class_program();
        result.fns.extend([branch, looped]);
        let branch_module = emit_program(
            &result,
            1,
            &EmitOptions {
                entry: Some("optional_branch_init".into()),
            },
        )
        .unwrap();
        let loop_module = emit_program(
            &result,
            1,
            &EmitOptions {
                entry: Some("optional_loop_init".into()),
            },
        )
        .unwrap();

        for subject in [
            function_ir(&branch_module, &branch_symbol),
            function_ir(&loop_module, &loop_symbol),
        ] {
            let neutral = subject
                .find("store %sable.class.0 zeroinitializer, ptr %v0")
                .expect("uninitialized class receives the neutral aggregate");
            let first_destination_read = subject
                .find("getelementptr %sable.class.0, ptr %v0")
                .expect("assignment or exit drops through the class slot");
            assert!(
                neutral < first_destination_read,
                "no path may inspect the class slot before its neutral store"
            );
            assert!(
                subject[first_destination_read..].contains("call void @__sable_rt_array_free_v1"),
                "the BodyPlan route retains the eventual owner cleanup"
            );
        }

        let branch_ir = function_ir(&branch_module, &branch_symbol);
        let merge = branch_ir
            .find("if.end")
            .expect("the false edge reaches the merge");
        assert!(branch_ir[merge..].contains("getelementptr %sable.class.0, ptr %v0"));

        let loop_ir = function_ir(&loop_module, &loop_symbol);
        let exit = loop_ir
            .find("while.end")
            .expect("the condition has a zero-iteration exit");
        assert!(loop_ir[exit..].contains("getelementptr %sable.class.0, ptr %v0"));
    }

    #[test]
    fn fixed_owner_class_reassignment_parameters_methods_and_discarded_results_stay_closed() {
        let options = EmitOptions {
            entry: Some("entry".into()),
        };

        let mut method_class = fixed_class_program();
        method_class.classes[0].methods.push(Method {
            self_kind: SelfKind::Shared,
            f: function("method", Ty::Unit, Vec::new()),
        });
        let error = emit_program(&method_class, 1, &options).unwrap_err();
        assert_eq!(error[0].name, "backend.class_unsupported");

        let mut missing_field = fixed_class_program();
        missing_field.classes[0].inits[0].body.clear();
        let error = emit_program(&missing_field, 1, &options).unwrap_err();
        assert!(
            error[0]
                .label
                .contains("does not initialize every native field exactly once")
        );

        let mut duplicate_field = fixed_class_program();
        let duplicate = duplicate_field.classes[0].inits[0].body[0].clone();
        duplicate_field.classes[0].inits[0].body.push(duplicate);
        let error = emit_program(&duplicate_field, 1, &options).unwrap_err();
        assert_eq!(error[0].name, "backend.class_unsupported");
        assert!(error[0].label.contains("was already initialized"));

        let mut ordinary_owned_argument = fixed_class_program();
        let mut sink = function("sink", Ty::Unit, Vec::new());
        sink.params = vec![parameter("owned", Ty::Class(0))];
        ordinary_owned_argument.fns.push(sink);
        ordinary_owned_argument.fns[1].body.insert(
            1,
            Stmt::ExprStmt(call_with(
                "sink",
                Ty::Unit,
                vec![typed_variable("value", Ty::Class(0))],
            )),
        );
        let error = emit_program(&ordinary_owned_argument, 1, &options).unwrap_err();
        assert_eq!(error[0].name, "backend.class_unsupported");
        assert!(error[0].title.contains("destination-passing position"));

        let mut overlapping_move = fixed_class_program();
        let mut overlap = function(
            "overlap",
            Ty::Class(0),
            vec![Stmt::Return {
                value: Some(typed_variable("owned", Ty::Class(0))),
                span: Span::new(0, 1),
            }],
        );
        overlap.params = vec![
            parameter("borrowed", Ty::borrow(Mutability::Shared, Ty::Class(0))),
            parameter("owned", Ty::Class(0)),
        ];
        overlapping_move.fns.push(overlap);
        overlapping_move.fns[1].body.insert(
            1,
            Stmt::VarDecl {
                ty: Some(Ty::Class(0)),
                name: "replacement".into(),
                name_span: Span::new(0, 1),
                init: call_with(
                    "overlap",
                    Ty::Class(0),
                    vec![
                        fixed_class_borrow("value"),
                        typed_variable("value", Ty::Class(0)),
                    ],
                ),
                mutable: false,
            },
        );
        let error = emit_program(&overlapping_move, 1, &options).unwrap_err();
        assert_eq!(error[0].name, "backend.class_unsupported");
        assert!(error[0].label.contains("both borrowed and moved by value"));

        let mut forwarded_alias = fixed_class_program();
        let mut integer_initializer = function(
            "make",
            Ty::Unit,
            vec![
                Stmt::FieldAssign {
                    field: "mag".into(),
                    field_span: Span::new(0, 1),
                    value: typed_variable("magnitude", Ty::Class(0)),
                },
                Stmt::FieldAssign {
                    field: "neg".into(),
                    field_span: Span::new(0, 1),
                    value: typed_variable("sign", Ty::Int(IntTy::U64)),
                },
            ],
        );
        integer_initializer.params = vec![
            parameter("magnitude", Ty::Class(0)),
            parameter("sign", Ty::Int(IntTy::U64)),
        ];
        forwarded_alias.classes.push(ClassDecl {
            is_pub: false,
            name: "Integer".into(),
            name_span: Span::new(0, 1),
            type_params: Vec::new(),
            type_bounds: Vec::new(),
            proof_reuse: ProofReuse::None,
            fields: vec![
                Field {
                    name: "mag".into(),
                    ty: Ty::Class(0),
                    span: Span::new(0, 1),
                    must_consume: false,
                },
                Field {
                    name: "neg".into(),
                    ty: Ty::Int(IntTy::U64),
                    span: Span::new(0, 1),
                    must_consume: false,
                },
            ],
            invariants: Vec::new(),
            inits: vec![integer_initializer],
            methods: vec![Method {
                self_kind: SelfKind::Mut,
                f: function("flip_sign", Ty::Unit, Vec::new()),
            }],
            deinit: None,
            span: Span::new(0, 1),
        });
        let mut alias = function(
            "alias",
            Ty::Unit,
            vec![Stmt::Return {
                value: None,
                span: Span::new(0, 1),
            }],
        );
        alias.params = vec![
            parameter("left", Ty::borrow(Mutability::Mut, Ty::Class(1))),
            parameter("right", Ty::borrow(Mutability::Mut, Ty::Class(1))),
        ];
        let mutable_reference = Ty::borrow(Mutability::Mut, Ty::Class(1));
        let mut forward = function(
            "forward_alias",
            Ty::Unit,
            vec![
                Stmt::ExprStmt(call_with(
                    "alias",
                    Ty::Unit,
                    vec![
                        typed_variable("reference", mutable_reference.clone()),
                        typed_variable("reference", mutable_reference.clone()),
                    ],
                )),
                Stmt::Return {
                    value: None,
                    span: Span::new(0, 1),
                },
            ],
        );
        forward.params = vec![parameter("reference", mutable_reference.clone())];
        forwarded_alias.fns.push(alias);
        forwarded_alias.fns.push(forward);
        forwarded_alias.fns.push(function(
            "integer_alias_entry",
            Ty::Int(IntTy::I32),
            vec![
                Stmt::VarDecl {
                    ty: Some(Ty::Class(1)),
                    name: "value".into(),
                    name_span: Span::new(0, 1),
                    init: expression(
                        ExprKind::CtorCall {
                            class: "Integer".into(),
                            class_span: Span::new(0, 1),
                            type_args: Vec::new(),
                            init: "make".into(),
                            args: vec![
                                fixed_class_constructor(),
                                expression(ExprKind::IntLit(0), Ty::Int(IntTy::U64)),
                            ],
                        },
                        Ty::Class(1),
                    ),
                    mutable: true,
                },
                Stmt::ExprStmt(call_with(
                    "forward_alias",
                    Ty::Unit,
                    vec![expression(
                        ExprKind::Borrow {
                            array: "value".into(),
                            field: None,
                            mutable: true,
                        },
                        mutable_reference,
                    )],
                )),
                Stmt::Return {
                    value: Some(expression(ExprKind::IntLit(42), Ty::Int(IntTy::I32))),
                    span: Span::new(0, 1),
                },
            ],
        ));
        let error = emit_program(
            &forwarded_alias,
            1,
            &EmitOptions {
                entry: Some("integer_alias_entry".into()),
            },
        );
        let error = error.unwrap_err();
        assert_eq!(error[0].name, "backend.unsupported");
        assert!(error[0].label.contains("overlapping borrows"));

        let alias = forwarded_alias
            .fns
            .iter_mut()
            .find(|function| function.name == "alias")
            .unwrap();
        alias.params[1] = parameter("sign", Ty::Int(IntTy::U64));
        let forward = forwarded_alias
            .fns
            .iter_mut()
            .find(|function| function.name == "forward_alias")
            .unwrap();
        let Stmt::ExprStmt(Expr {
            kind: ExprKind::Call { args, .. },
            ..
        }) = &mut forward.body[0]
        else {
            unreachable!()
        };
        args[1] = expression(
            ExprKind::ClassField {
                obj: "reference".into(),
                obj_span: Span::new(0, 1),
                field: "neg".into(),
            },
            Ty::Int(IntTy::U64),
        );
        let error = emit_program(
            &forwarded_alias,
            1,
            &EmitOptions {
                entry: Some("integer_alias_entry".into()),
            },
        )
        .unwrap_err();
        assert_eq!(error[0].name, "backend.unsupported");
        assert!(error[0].label.contains("overlapping borrows"));

        let mut discarded_result = fixed_class_program();
        discarded_result.fns.push(function(
            "make",
            Ty::Class(0),
            vec![Stmt::Return {
                value: Some(fixed_class_constructor()),
                span: Span::new(0, 1),
            }],
        ));
        discarded_result.fns[1]
            .body
            .insert(1, Stmt::ExprStmt(call("make", Ty::Class(0))));
        let error = emit_program(&discarded_result, 1, &options).unwrap_err();
        assert_eq!(error[0].name, "backend.class_unsupported");
        assert!(error[0].label.contains("bind or return"));

        let control = ControlProgram::build(&discarded_result)
            .expect("unsupported lowering still retains the discarded-temp action");
        let mut respanned = discarded_result.clone();
        let Stmt::ExprStmt(expression) = &mut respanned.fns[1].body[1] else {
            unreachable!()
        };
        expression.span = Span::new(90, 91);
        let mismatch = emit_program_with_control(&respanned, &control, 1, &options)
            .expect_err("LLVM must exact-consume the retained action before refusing the subset");
        assert_eq!(mismatch[0].name, "internal.control_plan_invalid");
        assert!(mismatch[0].label.contains("discarded class temporary"));
    }

    #[test]
    fn constructor_dependencies_follow_the_checked_nominal_class() {
        let mut result = fixed_class_program();
        result.classes.push(result.classes[0].clone());
        result.fns.push(function(
            "duplicate_constructor_entry",
            Ty::Int(IntTy::I32),
            vec![
                Stmt::VarDecl {
                    ty: Some(Ty::Class(1)),
                    name: "value".into(),
                    name_span: Span::new(0, 1),
                    init: expression(
                        ExprKind::CtorCall {
                            class: "Nat".into(),
                            class_span: Span::new(0, 1),
                            type_args: Vec::new(),
                            init: "new".into(),
                            args: Vec::new(),
                        },
                        Ty::Class(1),
                    ),
                    mutable: false,
                },
                Stmt::Return {
                    value: Some(expression(ExprKind::IntLit(42), Ty::Int(IntTy::I32))),
                    span: Span::new(0, 1),
                },
            ],
        ));

        let ir = emit_program(
            &result,
            1,
            &EmitOptions {
                entry: Some("duplicate_constructor_entry".into()),
            },
        )
        .unwrap();
        assert!(ir.contains("define internal void @__sable_v0_c1_i_3_new__p_(ptr %self)"));
        assert!(ir.contains("call void @__sable_v0_c1_i_3_new__p_(ptr %v0)"));
    }

    #[test]
    fn fixed_owner_validation_fails_closed_without_recursive_or_self_name_panics() {
        let mut cyclic = fixed_class_program();
        let integer = |child| ClassDecl {
            is_pub: false,
            name: "Integer".into(),
            name_span: Span::new(0, 1),
            type_params: Vec::new(),
            type_bounds: Vec::new(),
            proof_reuse: ProofReuse::None,
            fields: vec![
                Field {
                    name: "mag".into(),
                    ty: Ty::Class(child),
                    span: Span::new(0, 1),
                    must_consume: false,
                },
                Field {
                    name: "neg".into(),
                    ty: Ty::Int(IntTy::U64),
                    span: Span::new(0, 1),
                    must_consume: false,
                },
            ],
            invariants: Vec::new(),
            inits: Vec::new(),
            methods: vec![Method {
                self_kind: SelfKind::Mut,
                f: function("flip_sign", Ty::Unit, Vec::new()),
            }],
            deinit: None,
            span: Span::new(0, 1),
        };
        cyclic.classes = vec![integer(1), integer(0)];
        let error = require_fixed_class(&cyclic, 0, Span::new(0, 1), "cycle probe")
            .expect_err("cyclic forged Integer declarations must fail closed");
        assert_eq!(error[0].name, "backend.class_unsupported");
        assert!(error[0].title.contains("exact native Nat shape"));

        let mut invalid_receiver = fixed_class_program();
        let mut bad_method = function(
            "bad_method",
            Ty::Unit,
            vec![Stmt::ExprStmt(expression(
                ExprKind::MethodCall {
                    recv: "receiver".into(),
                    recv_span: Span::new(0, 1),
                    method: "flip_sign".into(),
                    method_span: Span::new(0, 1),
                    args: Vec::new(),
                },
                Ty::Unit,
            ))],
        );
        bad_method.params = vec![parameter(
            "receiver",
            Ty::borrow(Mutability::Mut, Ty::Class(99)),
        )];
        invalid_receiver.fns.push(bad_method);
        let error = callable_dependencies(&invalid_receiver, Callable::Function(2))
            .expect_err("invalid receiver class indices must diagnose before emission");
        assert_eq!(error[0].name, "backend.class_unsupported");
        assert!(error[0].title.contains("invalid checked class index"));

        let mut free_self = fixed_class_program();
        let entry = &mut free_self.fns[1];
        let Stmt::VarDecl { name, .. } = &mut entry.body[0] else {
            unreachable!()
        };
        *name = "self".into();
        let Stmt::ExprStmt(Expr {
            kind: ExprKind::Call { args, .. },
            ..
        }) = &mut entry.body[1]
        else {
            unreachable!()
        };
        let ExprKind::Borrow { array, .. } = &mut args[0].kind else {
            unreachable!()
        };
        *array = "self".into();
        emit_program(
            &free_self,
            1,
            &EmitOptions {
                entry: Some("entry".into()),
            },
        )
        .expect("a free-function owner named self uses its ordinary local slot");
    }
}
