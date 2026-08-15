//! Strict textual LLVM IR lowering for the verified scalar, Boolean-option,
//! bounded POD-record, owned-local Boolean-array, local `u32`-array, and
//! fixed-owner class core with internal borrows, returns, and named moves
//! (ADRs 0058--0059).
//!
//! The backend lowers scalar storage, calls, comparisons, and structured
//! control flow.  A construct is either lowered with its Sable meaning or
//! rejected with a source diagnostic; there is no silent fallback and no
//! unchecked arithmetic.

use crate::VerifiedProgram;
use crate::ast::{
    AffineOptionTy, BinOp, ClassDecl, Expr, ExprKind, Fn, IntTy, Mutability, Program, RecordDecl,
    SelfKind, Stmt, Ty, UnOp,
};
use crate::diag::Diagnostic;
use crate::span::Span;
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
    let selected = select_callables(program, root_span_end, options)?;
    validate_acyclic(program, &selected)?;
    for &index in &selected.functions {
        validate_function(program, &program.fns[index], root_span_end)?;
    }
    for &(class, initializer) in &selected.initializers {
        validate_initializer(
            program,
            class,
            &program.classes[class].inits[initializer],
            root_span_end,
        )?;
    }
    for &(class, method) in &selected.methods {
        validate_method(
            program,
            class,
            method,
            &program.classes[class].methods[method],
            root_span_end,
        )?;
    }

    let selected_set: HashSet<usize> = selected.functions.iter().copied().collect();
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
    for &(class, initializer) in &selected.initializers {
        FunctionEmitter::new_initializer(program, class, initializer, &mut support)
            .emit(&mut definitions)?;
        definitions.push('\n');
    }
    for &(class, method) in &selected.methods {
        FunctionEmitter::new_method(program, class, method, &mut support).emit(&mut definitions)?;
        definitions.push('\n');
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
            .find(|parameter| matches!(parameter.ty, Ty::AffineOption(_)))
        {
            return Err(vec![affine_option_unsupported(
                parameter.span,
                "LLVM entry parameter",
                parameter.ty.clone(),
            )]);
        }
        if matches!(function.ret, Ty::AffineOption(_)) {
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
        let class = match receiver_ty {
            Ty::Class(class) | Ty::ClassRef(class, _) => class,
            other => {
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
    if let Some(parameter) = function
        .params
        .iter()
        .find(|parameter| matches!(parameter.ty, Ty::AffineOption(_)))
    {
        return Err(vec![affine_option_unsupported(
            parameter.span,
            "function parameter",
            parameter.ty.clone(),
        )]);
    }
    if matches!(function.ret, Ty::AffineOption(_)) {
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
            "function return type",
        )?;
    }
    let mut locals = ValidationLocals::new();
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
    )
    .map(|_| ())
}

#[derive(Clone, PartialEq, Eq)]
struct InitializerValidation {
    class: usize,
    fields_initialized: Vec<bool>,
}

fn validate_initializer(
    program: &Program,
    class: usize,
    initializer: &Fn,
    root_span_end: usize,
) -> Result<(), Vec<BackendError>> {
    let declaration = require_fixed_class(
        program,
        class,
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
    let mut locals = ValidationLocals::new();
    for parameter in &initializer.params {
        require_initializer_parameter(
            program,
            root_span_end,
            parameter.ty.clone(),
            parameter.span,
        )?;
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
    Ok(())
}

fn validate_method(
    program: &Program,
    class: usize,
    method_index: usize,
    method: &crate::ast::Method,
    root_span_end: usize,
) -> Result<(), Vec<BackendError>> {
    let declaration = require_fixed_class(program, class, method.f.name_span, "selected method")?;
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
    let mut locals = ValidationLocals::new();
    locals.insert(
        "self".into(),
        ValidationLocal {
            ty: Ty::ClassRef(class, Mutability::Mut),
            mutable: true,
        },
        method.f.name_span,
    )?;
    validate_block(
        program,
        &method.f.body,
        root_span_end,
        &mut locals,
        Ty::Unit,
        None,
        Some((class, method.self_kind)),
    )
    .map(|_| ())
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
}

impl ValidationLocals {
    fn new() -> Self {
        Self {
            scopes: vec![HashMap::new()],
            declared: HashSet::new(),
            moved_classes: HashSet::new(),
        }
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
}

fn validate_block(
    program: &Program,
    statements: &[Stmt],
    root_span_end: usize,
    locals: &mut ValidationLocals,
    ret_ty: Ty,
    mut initializer: Option<&mut InitializerValidation>,
    method: Option<(usize, SelfKind)>,
) -> Result<bool, Vec<BackendError>> {
    let mut returned = false;
    for statement in statements {
        if returned {
            break;
        }
        match statement {
            Stmt::Decl {
                ty,
                name,
                name_span,
                init,
                mutable,
            } => {
                if matches!(ty, Ty::AffineOption(_)) {
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
                    if is_owned_bool_array(&ty.clone()) {
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
                if matches!(ty, Ty::AffineOption(_)) {
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
                    if is_owned_bool_array(&ty.clone()) {
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
                if matches!(local.ty, Ty::AffineOption(_)) {
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
                returned = validate_block(
                    program,
                    body,
                    root_span_end,
                    locals,
                    ret_ty.clone(),
                    initializer.as_deref_mut(),
                    method,
                )?;
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                validate_bool_expr(program, cond, "`if` condition", root_span_end, locals)?;
                let base_initializer = initializer.as_deref().cloned();
                let before_moved = locals.moved_classes.clone();
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
                )?;
                locals.pop_scope();
                let then_moved = locals.moved_classes.clone();
                locals.moved_classes = before_moved.clone();
                let mut else_initializer = base_initializer.clone();
                let (else_returned, else_moved) = if let Some(else_block) = else_block {
                    locals.push_scope();
                    let else_returned = validate_block(
                        program,
                        else_block,
                        root_span_end,
                        locals,
                        ret_ty.clone(),
                        else_initializer.as_mut(),
                        method,
                    )?;
                    locals.pop_scope();
                    (else_returned, locals.moved_classes.clone())
                } else {
                    (false, before_moved.clone())
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
                locals.moved_classes = match (then_returned, else_returned) {
                    (true, true) => before_moved,
                    (true, false) => else_moved,
                    (false, true) => then_moved,
                    (false, false) => then_moved,
                };
                returned = then_returned && else_returned;
            }
            Stmt::While { cond, body, .. } => {
                validate_bool_expr(program, cond, "`while` condition", root_span_end, locals)?;
                let before = initializer.as_deref().cloned();
                let before_moved = locals.moved_classes.clone();
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
                locals.moved_classes = before_moved;
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
                ..
            } => {
                reject_named_affine_option(locals, array, *array_span, "array exposure source")?;
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
    }
    Ok(returned)
}

fn is_owned_bool_array(ty: &Ty) -> bool {
    ty.is_owned_array_of(&Ty::Bool)
}

fn is_owned_u32_array(ty: Ty) -> bool {
    ty.is_owned_array_of(&Ty::Int(IntTy::U32))
}

fn is_u32_array(ty: &Ty) -> bool {
    ty.is_array_of(&Ty::Int(IntTy::U32))
}

fn is_owned_native_array(ty: &Ty) -> bool {
    is_owned_bool_array(&ty.clone()) || is_owned_u32_array(ty.clone())
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
        && declaration.fields[0].ty == Ty::array(Ty::Int(IntTy::U32), Mutability::Owned)
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
            && child_declaration.fields[0].ty == Ty::array(Ty::Int(IntTy::U32), Mutability::Owned)
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
        Ty::Array(element, Mutability::Shared) if element.as_ref() == &Ty::Int(IntTy::U32) => {
            Ok(())
        }
        Ty::Int(integer) if !matches!(integer, IntTy::TParam(_)) => Ok(()),
        Ty::Bool => Ok(()),
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

fn validate_fixed_class_initializer(
    program: &Program,
    class: usize,
    expression: &Expr,
    root_span_end: usize,
    locals: &mut ValidationLocals,
) -> Result<(), Vec<BackendError>> {
    let declaration =
        require_fixed_class(program, class, expression.span, "class local initializer")?;
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
            "expected a direct constructor, internal class-returning call, or named owner move",
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
            Ty::ClassRef(..) => {
                validate_class_borrow_argument(program, argument, parameter.ty.clone(), locals)?;
            }
            Ty::Array(element, Mutability::Shared | Mutability::Mut)
                if element.as_ref() == &Ty::Int(IntTy::U32) =>
            {
                validate_u32_array_borrow_argument(program, argument, parameter.ty.clone(), locals)?
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
    locals: &ValidationLocals,
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
        if matches!(
            parameter.ty,
            Ty::ClassRef(_, Mutability::Shared | Mutability::Mut)
        ) {
            validate_class_borrow_argument(program, argument, parameter.ty.clone(), locals)?;
        } else if matches!(
            parameter.ty.as_array(),
            Some((&Ty::Int(IntTy::U32), Mutability::Shared | Mutability::Mut))
        ) {
            validate_u32_array_borrow_argument(program, argument, parameter.ty.clone(), locals)?;
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
    let declaration = require_fixed_class(program, class, field_span, "member field assignment")?;
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
            Ty::Array(element, Mutability::Owned) if element.as_ref() == &Ty::Int(IntTy::U32) => {
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
            "method field replacement is outside the concrete `Integer` surface the LLVM backend lowers",
            field_span,
            "a lowered method may assign only the scalar `Integer.neg` field",
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
    locals: &ValidationLocals,
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
    if declaration_field.ty != Ty::array(Ty::Int(IntTy::U32), Mutability::Owned)
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
    let class = match local.ty {
        Ty::Class(class) | Ty::ClassRef(class, Mutability::Shared | Mutability::Mut) => class,
        _ => {
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

fn affine_bool_option_ty() -> Ty {
    Ty::AffineOption(AffineOptionTy::array(Ty::Bool))
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
        if matches!(local.ty, Ty::AffineOption(_)) {
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
    locals: &ValidationLocals,
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
            require_expr_type(
                payload,
                Ty::array(Ty::Bool, Mutability::Owned),
                "affine-option payload",
            )?;
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
    require_expr_type(
        expression,
        Ty::array(Ty::Bool, Mutability::Owned),
        "affine-option take result",
    )?;
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
        return if matches!(source.ty, Ty::AffineOption(_)) {
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
    locals: &ValidationLocals,
    local: &str,
    allow_take: bool,
) -> Result<(), Vec<BackendError>> {
    let expected = Ty::array(Ty::Bool, Mutability::Owned);
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
    locals: &ValidationLocals,
) -> Result<(), Vec<BackendError>> {
    let expected = Ty::array(Ty::Int(IntTy::U32), Mutability::Owned);
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
    locals: &ValidationLocals,
) -> Result<(), Vec<BackendError>> {
    let Some(local) = locals.get(array) else {
        return Err(vec![unsupported(
            array_span,
            format!("array store names unknown or out-of-scope local `{array}`"),
        )]);
    };
    if !is_owned_native_array(&local.ty)
        && local.ty != Ty::array(Ty::Int(IntTy::U32), Mutability::Mut)
    {
        return Err(vec![unsupported(
            array_span,
            format!(
                "array store target `{array}` has unsupported LLVM type `{}`",
                local.ty.name()
            ),
        )]);
    }
    if is_owned_native_array(&local.ty) && !local.mutable {
        return Err(vec![unsupported(
            array_span,
            format!("array store targets immutable owned array `{array}`"),
        )]);
    }
    validate_expr(program, index, root_span_end, locals)?;
    require_expr_type(index, Ty::Int(IntTy::U64), "array store index")?;
    if is_owned_bool_array(&local.ty) {
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

fn validate_u32_array_borrow_argument(
    program: &Program,
    argument: &Expr,
    expected: Ty,
    locals: &ValidationLocals,
) -> Result<(), Vec<BackendError>> {
    let Some((&Ty::Int(IntTy::U32), expected_mutability)) = expected.as_array() else {
        unreachable!("called only for a checked `u32` array borrow parameter")
    };
    if !matches!(expected_mutability, Mutability::Shared | Mutability::Mut) {
        return Err(vec![unsupported(
            argument.span,
            "owned arrays cannot cross an LLVM call boundary",
        )]);
    }
    require_expr_type(argument, expected, "`u32` array borrow argument")?;
    let ExprKind::Borrow {
        array,
        field,
        mutable,
    } = &argument.kind
    else {
        return Err(vec![unsupported(
            argument.span,
            "borrowed `u32` array parameters require an explicit named borrow",
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
        if field_ty != Ty::array(Ty::Int(IntTy::U32), Mutability::Owned) {
            return Err(vec![diag(
                "backend.class_unsupported",
                "array field borrow has the wrong native type",
                argument.span,
                format!("`{array}.{field}` has type `{}`", field_ty.name()),
            )]);
        }
        return Ok(());
    }
    let Some((&Ty::Int(IntTy::U32), source_mutability)) = source.ty.as_array() else {
        return Err(vec![unsupported(
            argument.span,
            format!("array borrow source `{array}` is not a native `u32` array"),
        )]);
    };
    if *mutable
        && (source_mutability == Mutability::Shared
            || (source_mutability == Mutability::Owned && !source.mutable))
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
    let Ty::ClassRef(class, expected_mutability @ (Mutability::Shared | Mutability::Mut)) =
        expected
    else {
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
        if !matches!(source.ty, Ty::ClassRef(source_class, source_mutability)
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
    if !matches!(source.ty, Ty::Class(source_class) | Ty::ClassRef(source_class, _) if source_class == class)
    {
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
    let mutable_source = match source.ty {
        Ty::Class(_) => source.mutable,
        Ty::ClassRef(_, Mutability::Mut) => true,
        _ => false,
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
        if matches!(parameter.ty, Ty::ClassRef(_, Mutability::Mut)) {
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
        ExprKind::Var(name) => match locals.get(name).map(|local| local.ty) {
            Some(Ty::Class(_)) | Some(Ty::ClassRef(_, Mutability::Mut)) => {
                places.push((name.clone(), true, expression.span));
            }
            Some(Ty::ClassRef(_, Mutability::Shared)) => {
                places.push((name.clone(), false, expression.span));
            }
            _ => {}
        },
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
    receiver: &str,
    receiver_span: Span,
    method_name: &str,
    args: &[Expr],
    locals: &ValidationLocals,
) -> Result<(), Vec<BackendError>> {
    let Some(local) = locals.get(receiver) else {
        return Err(vec![unsupported(
            receiver_span,
            format!("method receiver names unknown local `{receiver}`"),
        )]);
    };
    if matches!(local.ty, Ty::Class(_)) {
        locals.require_live_class(receiver, receiver_span, "method receiver")?;
    }
    let class = match local.ty {
        Ty::Class(class) | Ty::ClassRef(class, _) => class,
        other => {
            return Err(vec![diag(
                "backend.class_unsupported",
                "native method receiver is not a class",
                receiver_span,
                format!("`{receiver}` has type `{}`", other.name()),
            )]);
        }
    };
    let declaration = require_fixed_class(program, class, receiver_span, "method receiver")?;
    let Some(method) = declaration
        .methods
        .iter()
        .find(|candidate| candidate.f.name == method_name)
    else {
        return Err(vec![diag(
            "backend.method_missing",
            "native method was not found on its receiver",
            expression.span,
            format!("class `{}` has no method `{method_name}`", declaration.name),
        )]);
    };
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
    let receiver_is_mutable = match local.ty {
        Ty::Class(_) => local.mutable,
        Ty::ClassRef(_, Mutability::Mut) => true,
        _ => false,
    };
    if !receiver_is_mutable {
        return Err(vec![diag(
            "backend.class_unsupported",
            "mutable method receiver is not mutable",
            receiver_span,
            format!("`{receiver}` cannot receive `&mut self`"),
        )]);
    }
    require_expr_type(expression, Ty::Unit, "native method result")
}

fn validate_expr(
    program: &Program,
    expression: &Expr,
    root_span_end: usize,
    locals: &ValidationLocals,
) -> Result<(), Vec<BackendError>> {
    if let ExprKind::IsSome { operand } = &expression.kind {
        if matches!(operand.ty, Some(Ty::AffineOption(_))) {
            return validate_affine_option_is_some(expression, operand, locals);
        }
    }
    if let Some(ty @ Ty::AffineOption(_)) = &expression.ty {
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
            if matches!(local.ty, Ty::Array(..)) {
                return Err(vec![unsupported(
                    expression.span,
                    format!("array local `{name}` cannot be transported as a value"),
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
            if let Some(ty @ Ty::AffineOption(_)) = &operand.ty {
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
            if matches!(local.ty, Ty::AffineOption(_)) {
                return Err(vec![affine_option_unsupported(
                    *array_span,
                    "array index base",
                    local.ty,
                )]);
            }
            if !is_owned_bool_array(&local.ty) && !is_u32_array(&local.ty) {
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
            let element_ty = if is_owned_bool_array(&local.ty) {
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
            if matches!(local.ty, Ty::AffineOption(_)) {
                return Err(vec![affine_option_unsupported(
                    expression.span,
                    "array length base",
                    local.ty,
                )]);
            }
            if !is_owned_bool_array(&local.ty) && !is_u32_array(&local.ty) {
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
        ExprKind::MethodCall {
            recv,
            recv_span,
            method,
            args,
            ..
        } => {
            validate_native_method_call(program, expression, recv, *recv_span, method, args, locals)
        }
        ExprKind::ClassFieldIndex {
            obj,
            obj_span,
            field,
            index,
        } => {
            let (_, _, field_ty) =
                validate_fixed_class_field_base(program, locals, obj, field, *obj_span)?;
            if field_ty != Ty::array(Ty::Int(IntTy::U32), Mutability::Owned) {
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
            if field_ty != Ty::array(Ty::Int(IntTy::U32), Mutability::Owned) {
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
            let (_, _, field_ty) =
                validate_fixed_class_field_base(program, locals, "self", field, expression.span)?;
            let Ty::Int(integer) = field_ty else {
                return Err(vec![diag(
                    "backend.class_unsupported",
                    "method field read is outside the concrete `Integer` surface the LLVM backend lowers",
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
    let Some(ref ty @ Ty::AffineOption(_)) = operand.ty else {
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
    locals: &ValidationLocals,
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
        if matches!(field.ty, Ty::AffineOption(_)) {
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
        Ty::Int(integer) if !matches!(integer, IntTy::TParam(_)) => Ok(()),
        Ty::Bool | Ty::Unit => Ok(()),
        Ty::Option(payload) if payload.as_ref() == &Ty::Bool => Ok(()),
        Ty::AffineOption(_) => Err(vec![affine_option_unsupported(span, role, ty)]),
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
        Ty::Int(integer) if !matches!(integer, IntTy::TParam(_)) => Ok(()),
        Ty::Bool => Ok(()),
        Ty::Option(payload) if payload.as_ref() == &Ty::Bool => Ok(()),
        ty if is_affine_bool_option(&ty.clone()) => Ok(()),
        Ty::AffineOption(_) => Err(vec![affine_option_unsupported(span, role, ty)]),
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
        Ty::Int(integer) if !matches!(integer, IntTy::TParam(_)) => Ok(()),
        Ty::Bool => Ok(()),
        Ty::Array(element, Mutability::Shared | Mutability::Mut)
            if element.as_ref() == &Ty::Int(IntTy::U32) =>
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
        Ty::ClassRef(class, Mutability::Shared) => {
            require_fixed_class(program, class, span, role).map(|_| ())
        }
        Ty::ClassRef(class, Mutability::Mut) => {
            let declaration = require_fixed_class(program, class, span, role)?;
            if declaration.name == "Integer" {
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
        Ty::AffineOption(_) => Err(vec![affine_option_unsupported(span, role, ty)]),
        Ty::Record(record) => require_record_value(program, root_span_end, record, span, role),
        _ => Err(vec![unsupported(
            span,
            format!(
                "{role} type `{}` has no LLVM value representation; the backend lowers concrete integers, `bool`, borrowed `u32` arrays, fixed-owner classes, and integer-field records as values",
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

    fn require_class(&mut self, program: &Program, class: usize) {
        if !self.classes.insert(class) {
            return;
        }
        for field in &program.classes[class].fields {
            match &field.ty {
                Ty::Array(element, Mutability::Owned)
                    if element.as_ref() == &Ty::Int(IntTy::U32) =>
                {
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

    fn emit_record_type(record: usize, declaration: &RecordDecl, out: &mut String) {
        let fields = declaration
            .fields
            .iter()
            .map(|field| llvm_ty(field.ty.clone()))
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
        if self.needs_array_bool {
            out.push_str(LLVM_ARRAY_BOOL);
            out.push_str(" = type { ptr, i64 }\n\n");
        }
        if self.needs_array_u32 {
            out.push_str(LLVM_ARRAY_U32);
            out.push_str(" = type { ptr, i64 }\n\n");
        }
        if self.needs_array_bool || self.needs_array_u32 {
            out.push_str(
                "; target runtime hooks for owned array storage; allocation size is bytes\n\
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
            let fields = program.classes[*class]
                .fields
                .iter()
                .map(|field| llvm_ty(field.ty.clone()))
                .collect::<Vec<_>>()
                .join(", ");
            out.push_str(&format!(
                "{} = type {{ {fields} }}\n\n",
                llvm_class_ty(*class)
            ));
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
                 8 option value of none, 9 array OOM, 10 array index OOB\n\
                 ; type_info bytes: result/destination, lhs/source, rhs; \
                 type codes u8..u64,i8..i64 = 1..8\n\
                 ; array traps use type_info 0: OOM lhs=len/rhs=0; \
                 OOB lhs=index/rhs=len\n\
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

#[derive(Clone)]
enum OwnedCleanup {
    BoolArray(String),
    U32Array(String),
    AffineBoolOption(String),
    FixedClass(String, usize),
}

struct FunctionEmitter<'a, 'support> {
    program: &'a Program,
    function: &'a Fn,
    support: &'support mut ModuleSupport,
    initializer_class: Option<usize>,
    method: Option<(usize, usize)>,
    locals: HashMap<String, Local>,
    /// Entry-block scratch owners for class reassignment. Each RHS is fully
    /// evaluated here before the old destination is destroyed, preserving
    /// expressions that borrow their own assignment target.
    class_reassignment_slots: HashMap<String, String>,
    late_entry_allocas: Vec<String>,
    next_local: usize,
    next_temp: usize,
    next_block: usize,
    lines: Vec<String>,
    /// Name of the block currently accepting instructions.  `None` means
    /// that its terminator has been emitted; a sibling or merge may still be
    /// started afterwards.
    current_block: Option<String>,
    /// Ownership-bearing locals initialized on the current structured path,
    /// grouped by lexical lifetime. An `unsafe` block deliberately shares its
    /// caller's scope; `if` branches and loop bodies push one of their own.
    cleanup_scopes: Vec<Vec<OwnedCleanup>>,
}

impl<'a, 'support> FunctionEmitter<'a, 'support> {
    fn new(program: &'a Program, function: &'a Fn, support: &'support mut ModuleSupport) -> Self {
        Self {
            program,
            function,
            support,
            initializer_class: None,
            method: None,
            locals: HashMap::new(),
            class_reassignment_slots: HashMap::new(),
            late_entry_allocas: Vec::new(),
            next_local: 0,
            next_temp: 0,
            next_block: 0,
            lines: Vec::new(),
            current_block: Some("entry".into()),
            cleanup_scopes: vec![Vec::new()],
        }
    }

    fn new_initializer(
        program: &'a Program,
        class: usize,
        initializer: usize,
        support: &'support mut ModuleSupport,
    ) -> Self {
        let mut emitter = Self::new(program, &program.classes[class].inits[initializer], support);
        emitter.initializer_class = Some(class);
        emitter
    }

    fn new_method(
        program: &'a Program,
        class: usize,
        method: usize,
        support: &'support mut ModuleSupport,
    ) -> Self {
        let mut emitter = Self::new(program, &program.classes[class].methods[method].f, support);
        emitter.method = Some((class, method));
        emitter
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
        let explicit_parameters = self
            .function
            .params
            .iter()
            .enumerate()
            .map(|(index, parameter)| format!("{} %p{index}", llvm_ty(parameter.ty.clone())))
            .collect::<Vec<_>>();
        let implicit_parameter = self
            .initializer_class
            .or(self.method.map(|(class, _)| class))
            .map(|_| "ptr %self".to_string())
            .or_else(|| {
                matches!(self.function.ret, Ty::Class(_)).then(|| "ptr %result".to_string())
            });
        let parameters = if let Some(implicit_parameter) = implicit_parameter {
            std::iter::once(implicit_parameter)
                .chain(explicit_parameters)
                .collect::<Vec<_>>()
                .join(", ")
        } else {
            explicit_parameters.join(", ")
        };
        let symbol = self
            .initializer_class
            .map(|class| mangle_initializer(class, self.function))
            .or_else(|| {
                self.method
                    .map(|(class, _)| mangle_method(class, self.function))
            })
            .unwrap_or_else(|| mangle(self.function));
        let return_ty = if matches!(self.function.ret, Ty::Class(_)) {
            "void".to_string()
        } else {
            llvm_ty(self.function.ret.clone())
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
            let slot = self.new_slot();
            self.instruction(format!("{slot} = alloca {}", llvm_ty(ty.clone())));
            self.locals.insert(
                name.clone(),
                Local {
                    ty: ty.clone(),
                    slot,
                },
            );
        }
        let mut assignment_targets = BTreeSet::new();
        collect_assignment_targets(&self.function.body, &mut assignment_targets);
        for name in assignment_targets {
            let ty = self
                .locals
                .get(&name)
                .expect("validated assignment target was preallocated")
                .ty
                .clone();
            if let Ty::Class(class) = ty {
                let slot = self.new_slot();
                self.instruction(format!("{slot} = alloca {}", llvm_class_ty(class)));
                self.class_reassignment_slots.insert(name, slot);
            }
        }
        for (index, (name, ty)) in parameters.iter().enumerate() {
            let slot = self
                .locals
                .get(name)
                .expect("parameter slot was preallocated")
                .slot
                .clone();
            self.instruction(format!(
                "store {} %p{index}, ptr {slot}",
                llvm_ty(ty.clone())
            ));
            if let Ty::Class(class) = ty {
                self.cleanup_scopes[0].push(OwnedCleanup::FixedClass(name.clone(), *class));
            }
        }

        self.emit_block(&self.function.body)?;
        if self.current_block.is_some() {
            if self.function.ret == Ty::Unit {
                self.emit_current_scope_cleanups();
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
            ty if is_owned_bool_array(&ty.clone()) => self.support.require_array_bool(),
            ty if is_u32_array(&ty.clone()) => self.support.require_array_u32(),
            ty if is_affine_bool_option(&ty.clone()) => {
                self.support.require_affine_option_bool_array()
            }
            Ty::Record(record) => self.support.require_record(record),
            Ty::Class(class) | Ty::ClassRef(class, _) => {
                self.support.require_class(self.program, class)
            }
            Ty::AffineOption(_) => {
                unreachable!("affine option escaped LLVM validation into support collection")
            }
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
                    let Some(local) = self.locals.get(name) else {
                        return Err(vec![unsupported(
                            *name_span,
                            format!("LLVM local `{name}` was not declared"),
                        )]);
                    };
                    let ty = local.ty.clone();
                    let slot = local.slot.clone();
                    if let Ty::Class(class) = ty {
                        let scratch = self
                            .class_reassignment_slots
                            .get(name)
                            .expect("validated class assignment has entry scratch")
                            .clone();
                        // Evaluate completely before destroying the old value:
                        // real Nat assignments borrow their own destination.
                        self.emit_fixed_class_into(class, &scratch, value)?;
                        self.emit_fixed_class_drop(name, class);
                        self.emit_fixed_class_move(class, &slot, &scratch);
                        continue;
                    }
                    let emitted = self.emit_expr(value)?;
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
                        if let Ty::Class(class) = self.function.ret {
                            self.emit_fixed_class_into(class, "%result", value)?;
                            self.emit_all_cleanups();
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
                            self.emit_all_cleanups();
                            self.terminate("ret void");
                        } else {
                            self.emit_all_cleanups();
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
                        self.emit_all_cleanups();
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
                Stmt::Store {
                    array,
                    index,
                    value,
                    ..
                } => self.emit_native_array_store(array, index, value)?,
                Stmt::FieldAssign { field, value, .. } => {
                    let class = self
                        .initializer_class
                        .or(self.method.map(|(class, _)| class))
                        .expect("validated field assignment is in a class member");
                    let (field_index, field_ty) = self.class_field(class, field);
                    let field_slot = self.emit_class_field_slot(class, "%self", field_index);
                    match field_ty {
                        Ty::Array(element, Mutability::Owned)
                            if element.as_ref() == &Ty::Int(IntTy::U32) =>
                        {
                            let value = self.emit_fresh_u32_array(value)?;
                            self.instruction(format!(
                                "store {LLVM_ARRAY_U32} {}, ptr {field_slot}",
                                value.operand.expect("owned class field initializer")
                            ));
                        }
                        Ty::Class(child) => {
                            self.emit_fixed_class_into(child, &field_slot, value)?;
                        }
                        Ty::Int(_) => {
                            let value = self.emit_expr(value)?;
                            self.instruction(format!(
                                "store {} {}, ptr {field_slot}",
                                llvm_ty(field_ty),
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
            if let Ty::Class(class) = ty {
                self.emit_fixed_class_into(class, &slot, init)?;
                self.cleanup_scopes
                    .last_mut()
                    .expect("class declaration has a lexical cleanup scope")
                    .push(OwnedCleanup::FixedClass(name.to_owned(), class));
                return Ok(());
            }
            let value = if is_owned_bool_array(&ty.clone()) {
                match &init.kind {
                    ExprKind::OptTake { option, .. } => self.emit_affine_option_take(option)?,
                    _ => self.emit_fresh_bool_array(init)?,
                }
            } else if is_owned_u32_array(ty.clone()) {
                self.emit_fresh_u32_array(init)?
            } else if is_affine_bool_option(&ty.clone()) {
                self.emit_affine_bool_option_initializer(init)?
            } else {
                self.emit_expr(init)?
            };
            self.instruction(format!(
                "store {} {}, ptr {slot}",
                llvm_ty(ty.clone()),
                value.operand.expect("local initializer is non-unit")
            ));
            if is_owned_bool_array(&ty.clone()) {
                self.cleanup_scopes
                    .last_mut()
                    .expect("array declaration has a lexical cleanup scope")
                    .push(OwnedCleanup::BoolArray(name.to_owned()));
            } else if is_owned_u32_array(ty.clone()) {
                self.cleanup_scopes
                    .last_mut()
                    .expect("array declaration has a lexical cleanup scope")
                    .push(OwnedCleanup::U32Array(name.to_owned()));
            } else if is_affine_bool_option(&ty) {
                self.cleanup_scopes
                    .last_mut()
                    .expect("affine option declaration has a lexical cleanup scope")
                    .push(OwnedCleanup::AffineBoolOption(name.to_owned()));
            }
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
        self.cleanup_scopes.push(Vec::new());
        self.emit_block(then_block)?;
        let then_reaches_merge = self.current_block.is_some();
        if then_reaches_merge {
            self.emit_current_scope_cleanups();
            self.terminate(format!("br label %{merge_label}"));
        }
        self.cleanup_scopes.pop();

        let else_reaches_merge = if let Some(else_block) = else_block {
            self.start_block(false_label);
            self.cleanup_scopes.push(Vec::new());
            self.emit_block(else_block)?;
            let reaches = self.current_block.is_some();
            if reaches {
                self.emit_current_scope_cleanups();
                self.terminate(format!("br label %{merge_label}"));
            }
            self.cleanup_scopes.pop();
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
        self.cleanup_scopes.push(Vec::new());
        self.emit_block(body)?;
        if self.current_block.is_some() {
            self.emit_current_scope_cleanups();
            self.terminate(format!("br label %{header_label}"));
        }
        self.cleanup_scopes.pop();

        // The header's false edge always reaches this block, even when every
        // body path returns.
        self.start_block(exit_label);
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
            mangle_initializer(class, initializer),
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
                    mangle(function),
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
            lowered.push(format!(
                "{} {}",
                llvm_ty(parameter.ty.clone()),
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
            ExprKind::CtorCall { .. } | ExprKind::Call { .. } => {
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
        match ty {
            Ty::Class(class) => (class, slot),
            Ty::ClassRef(class, Mutability::Shared | Mutability::Mut) => {
                let pointer = self.new_temp();
                self.instruction(format!("{pointer} = load ptr, ptr {slot}"));
                (class, pointer)
            }
            _ => unreachable!("validated fixed-owner class base type"),
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
        self.support.require_array_bool();
        match &expression.kind {
            ExprKind::ArrayLit(elements) => self.emit_bool_array_literal(elements),
            ExprKind::AllocArray { len, init, .. } => self.emit_bool_array_allocation(len, init),
            ExprKind::OptTake { option, .. } => self.emit_affine_option_take(option),
            _ => unreachable!("validated fresh Boolean-array initializer"),
        }
    }

    fn emit_fresh_u32_array(&mut self, expression: &Expr) -> Result<Value, Vec<BackendError>> {
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
            ty: Ty::array(Ty::Bool, Mutability::Owned),
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
                ty: Ty::array(Ty::Bool, crate::ast::Mutability::Owned),
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
                ty: Ty::array(Ty::Int(IntTy::U32), Mutability::Owned),
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
            ty: Ty::array(Ty::Bool, crate::ast::Mutability::Owned),
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
            ty: Ty::array(Ty::Int(IntTy::U32), Mutability::Owned),
            operand: Some(descriptor),
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
        if is_owned_bool_array(&ty) {
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

    fn emit_current_scope_cleanups(&mut self) {
        let cleanups = self
            .cleanup_scopes
            .last()
            .expect("cleanup has a function scope")
            .iter()
            .rev()
            .cloned()
            .collect::<Vec<_>>();
        for cleanup in cleanups {
            self.emit_owned_cleanup(cleanup);
        }
    }

    fn emit_all_cleanups(&mut self) {
        let cleanups = self
            .cleanup_scopes
            .iter()
            .rev()
            .flat_map(|scope| scope.iter().rev())
            .cloned()
            .collect::<Vec<_>>();
        for cleanup in cleanups {
            self.emit_owned_cleanup(cleanup);
        }
    }

    fn emit_owned_cleanup(&mut self, cleanup: OwnedCleanup) {
        match cleanup {
            OwnedCleanup::BoolArray(name) => self.emit_bool_array_drop(&name),
            OwnedCleanup::U32Array(name) => self.emit_u32_array_drop(&name),
            OwnedCleanup::AffineBoolOption(name) => self.emit_affine_bool_option_drop(&name),
            OwnedCleanup::FixedClass(name, class) => self.emit_fixed_class_drop(&name, class),
        }
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

    fn emit_fixed_class_drop(&mut self, object: &str, class: usize) {
        let slot = self
            .locals
            .get(object)
            .expect("validated fixed-owner class local")
            .slot
            .clone();
        self.emit_fixed_class_drop_from_slot(&slot, class);
    }

    fn emit_fixed_class_drop_from_slot(&mut self, slot: &str, class: usize) {
        let fields = self.program.classes[class]
            .fields
            .iter()
            .enumerate()
            .map(|(index, field)| (index, field.ty.clone()))
            .collect::<Vec<_>>();
        for (field_index, field_ty) in fields.into_iter().rev() {
            let field_slot = self.emit_class_field_slot(class, slot, field_index);
            match field_ty {
                Ty::Array(element, Mutability::Owned)
                    if element.as_ref() == &Ty::Int(IntTy::U32) =>
                {
                    self.emit_u32_array_drop_from_slot(&field_slot);
                }
                Ty::Class(child) => self.emit_fixed_class_drop_from_slot(&field_slot, child),
                Ty::Int(_) => {}
                _ => unreachable!("validated native class cleanup field"),
            }
        }
        self.instruction(format!(
            "store {} zeroinitializer, ptr {slot}",
            llvm_class_ty(class)
        ));
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
        match &expression.kind {
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
                self.instruction(format!("{temp} = load {}, ptr {slot}", llvm_ty(ty.clone())));
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
                if is_owned_bool_array(&ty) {
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
                let (_, len) = if is_owned_bool_array(&ty) {
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
                let value = self.new_temp();
                self.instruction(format!(
                    "{value} = load {}, ptr {field_slot}",
                    llvm_ty(field_ty.clone())
                ));
                Ok(Value {
                    ty: field_ty,
                    operand: Some(value),
                })
            }
            ExprKind::SelfField { field } => {
                let (field_ty, field_slot) = self.class_field_slot("self", field);
                let value = self.new_temp();
                self.instruction(format!(
                    "{value} = load {}, ptr {field_slot}",
                    llvm_ty(field_ty.clone())
                ));
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
                    let next = self.new_temp();
                    self.instruction(format!(
                        "{next} = insertvalue {record_ty} {aggregate}, {} {}, {index}",
                        llvm_ty(field.ty.clone()),
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
                if matches!(operand.ty, Some(Ty::AffineOption(_))) {
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
                let call = format!(
                    "call {} @{}({})",
                    llvm_ty(function.ret.clone()),
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
                        ty: function.ret.clone(),
                        operand: Some(temp),
                    })
                }
            }
            ExprKind::MethodCall {
                recv, method, args, ..
            } => {
                debug_assert!(args.is_empty());
                let (class, receiver) = self.class_base_pointer(recv);
                let declaration = &self.program.classes[class];
                let method = declaration
                    .methods
                    .iter()
                    .find(|candidate| candidate.f.name == *method)
                    .expect("validated native method");
                self.instruction(format!(
                    "call void @{}(ptr {receiver})",
                    mangle_method(class, &method.f)
                ));
                Ok(Value {
                    ty: Ty::Unit,
                    operand: None,
                })
            }
            ExprKind::Borrow { array, field, .. }
                if matches!(expression.ty, Some(Ty::ClassRef(_, _))) =>
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
                        .expect("validated named `u32` array borrow")
                        .slot
                        .clone()
                };
                let descriptor = self.new_temp();
                self.instruction(format!("{descriptor} = load {LLVM_ARRAY_U32}, ptr {slot}"));
                Ok(Value {
                    ty: expression.ty.clone().expect("validated borrow type"),
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

fn collect_assignment_targets(statements: &[Stmt], targets: &mut BTreeSet<String>) {
    for statement in statements {
        match statement {
            Stmt::Assign { name, .. } => {
                targets.insert(name.clone());
            }
            Stmt::If {
                then_block,
                else_block,
                ..
            } => {
                collect_assignment_targets(then_block, targets);
                if let Some(else_block) = else_block {
                    collect_assignment_targets(else_block, targets);
                }
            }
            Stmt::While { body, .. } | Stmt::Unsafe { body, .. } => {
                collect_assignment_targets(body, targets);
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

pub(crate) fn llvm_ty(ty: Ty) -> String {
    match ty {
        Ty::Int(integer) => format!("i{}", integer.bits()),
        Ty::Bool => "i1".into(),
        Ty::Unit => "void".into(),
        Ty::Option(payload) if payload.as_ref() == &Ty::Bool => LLVM_OPTION_BOOL.into(),
        ty if is_owned_bool_array(&ty.clone()) => LLVM_ARRAY_BOOL.into(),
        ty if is_u32_array(&ty.clone()) => LLVM_ARRAY_U32.into(),
        ty if is_affine_bool_option(&ty.clone()) => LLVM_AFFINE_OPTION_BOOL_ARRAY.into(),
        Ty::Class(class) => llvm_class_ty(class),
        Ty::ClassRef(_, Mutability::Shared | Mutability::Mut) => "ptr".into(),
        Ty::Record(record) => llvm_record_ty(record),
        Ty::AffineOption(_) => {
            unreachable!("affine option escaped LLVM validation into type lowering")
        }
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

pub(crate) fn type_code(ty: Ty) -> String {
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
        Ty::Option(payload) if payload.as_ref() == &Ty::Bool => "ob".into(),
        Ty::Array(element, Mutability::Shared) if element.as_ref() == &Ty::Int(IntTy::U32) => {
            "au32s".into()
        }
        Ty::Array(element, Mutability::Mut) if element.as_ref() == &Ty::Int(IntTy::U32) => {
            "au32m".into()
        }
        Ty::ClassRef(class, Mutability::Shared) => format!("c{class}s"),
        Ty::ClassRef(class, Mutability::Mut) => format!("c{class}m"),
        Ty::Class(class) => format!("c{class}o"),
        Ty::Record(record) => format!("r{record}"),
        Ty::AffineOption(_) => {
            unreachable!("affine option escaped LLVM validation into symbol mangling")
        }
        _ => unreachable!("type without an LLVM runtime representation validated out"),
    }
}

fn mangle(function: &Fn) -> String {
    let params = function
        .params
        .iter()
        .map(|parameter| type_code(parameter.ty.clone()))
        .collect::<Vec<_>>()
        .join("_");
    format!(
        "__sable_v0_f_{}_{}__p_{}__r_{}",
        function.name.len(),
        function.name,
        params,
        type_code(function.ret.clone())
    )
}

fn mangle_initializer(class: usize, initializer: &Fn) -> String {
    let params = initializer
        .params
        .iter()
        .map(|parameter| type_code(parameter.ty.clone()))
        .collect::<Vec<_>>()
        .join("_");
    format!(
        "__sable_v0_c{class}_i_{}_{}__p_{params}",
        initializer.name.len(),
        initializer.name
    )
}

fn mangle_method(class: usize, method: &Fn) -> String {
    let params = method
        .params
        .iter()
        .map(|parameter| type_code(parameter.ty.clone()))
        .collect::<Vec<_>>()
        .join("_");
    format!(
        "__sable_v0_c{class}_m_{}_{}__p_{params}__r_{}",
        method.name.len(),
        method.name,
        type_code(method.ret.clone())
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

fn affine_option_unsupported(span: Span, role: &str, ty: Ty) -> BackendError {
    debug_assert!(matches!(ty, Ty::AffineOption(_)));
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
        AffineOptionTy, ExternInfo, Field, GenericTy, Method, Param, Program, ProofReuse,
        RecordField, SelfKind, StorageLayout, Ty, TypeArg,
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
        expression(kind, Ty::option(Ty::Bool))
    }

    fn bool_option_variable(name: &str) -> Expr {
        bool_option(ExprKind::Var(name.into()))
    }

    fn bool_array_ty() -> Ty {
        Ty::array(Ty::Bool, crate::ast::Mutability::Owned)
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

    fn u32_array_ty(mutability: Mutability) -> Ty {
        Ty::array(Ty::Int(IntTy::U32), mutability)
    }

    fn u32_array_literal(values: &[u32]) -> Expr {
        expression(
            ExprKind::ArrayLit(
                values
                    .iter()
                    .map(|value| expression(ExprKind::IntLit((*value).into()), Ty::Int(IntTy::U32)))
                    .collect(),
            ),
            u32_array_ty(Mutability::Owned),
        )
    }

    fn u32_array_alloc(len: Expr, init: Expr) -> Expr {
        expression(
            ExprKind::AllocArray {
                elem: Ty::Int(IntTy::U32),
                len: Box::new(len),
                init: Box::new(init),
            },
            u32_array_ty(Mutability::Owned),
        )
    }

    fn u32_array_borrow(name: &str, mutability: Mutability) -> Expr {
        expression(
            ExprKind::Borrow {
                array: name.into(),
                field: None,
                mutable: mutability == Mutability::Mut,
            },
            u32_array_ty(mutability),
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
            Ty::ClassRef(0, Mutability::Shared),
        )
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
        inspect.params = vec![parameter("value", Ty::ClassRef(0, Mutability::Shared))];
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
                ty: u32_array_ty(Mutability::Owned),
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
        let affine_bool = Ty::AffineOption(AffineOptionTy::array(Ty::Bool));
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
        let affine_integer = Ty::AffineOption(AffineOptionTy::array(Ty::Int(IntTy::I32)));
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
                validate_fresh_bool_array_initializer(&empty, &take, 1, &locals, destination, true)
                    .expect_err("forged take source/destination must be rejected"),
            );
        }

        assert_affine_error(
            validate_expr(&empty, &affine_take("pending"), 1, &locals)
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
                &locals,
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
        let option_decl = |name: &str, len: u64| Stmt::Decl {
            ty: affine.clone(),
            name: name.into(),
            name_span: Span::new(0, 1),
            init: Some(affine_some_alloc(len, true)),
            mutable: true,
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
    fn boolean_option_does_not_open_parameters_entries_or_other_payloads() {
        let option = Ty::option(Ty::Bool);
        let bool_array = Ty::array(Ty::Bool, crate::ast::Mutability::Owned);
        let mut parameterized = function(
            "parameterized",
            Ty::Bool,
            vec![Stmt::Return {
                value: Some(expression(ExprKind::BoolLit(false), Ty::Bool)),
                span: Span::new(0, 1),
            }],
        );
        parameterized.params = vec![parameter("value", option.clone())];
        let parameter_error =
            emit_program(&program(vec![parameterized]), 1, &EmitOptions::default()).unwrap_err();
        assert_eq!(parameter_error[0].name, "backend.unsupported");
        assert!(parameter_error[0].label.contains("function parameter"));

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
        let owned = u32_array_ty(Mutability::Owned);
        let shared = u32_array_ty(Mutability::Shared);
        let mutable = u32_array_ty(Mutability::Mut);
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
    fn u32_array_backend_revalidates_borrow_positions_capabilities_and_aliases() {
        let owned = u32_array_ty(Mutability::Owned);
        let shared = u32_array_ty(Mutability::Shared);
        let mutable = u32_array_ty(Mutability::Mut);
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
        assert!(error[0].label.contains("unsupported LLVM type"));
    }

    #[test]
    fn owned_boolean_arrays_lower_bytes_guards_and_reverse_cleanups() {
        let array = bool_array_ty();
        let len = expression(ExprKind::IntLit(3), Ty::Int(IntTy::U64));
        let mut f = function(
            "arrays",
            Ty::Bool,
            vec![
                Stmt::Decl {
                    ty: array.clone(),
                    name: "first".into(),
                    name_span: Span::new(0, 1),
                    init: Some(bool_array_literal(&[true, false])),
                    mutable: true,
                },
                Stmt::Unsafe {
                    kw_span: Span::new(0, 1),
                    body: vec![Stmt::Decl {
                        ty: array,
                        name: "second".into(),
                        name_span: Span::new(0, 1),
                        init: Some(bool_array_alloc(
                            len,
                            expression(ExprKind::BoolLit(true), Ty::Bool),
                        )),
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

        let literal = expression(
            ExprKind::ArrayLit(vec![
                call("lit_first", Ty::Bool),
                call("lit_second", Ty::Bool),
            ]),
            bool_array_ty(),
        );
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
                    init: Some(bool_array_alloc(
                        call("allocation_length", Ty::Int(IntTy::U64)),
                        call("allocation_init", Ty::Bool),
                    )),
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

        let subject_symbol = mangle(&subject);
        let call_marker = |function: &Fn| {
            format!(
                "call {} @{}()",
                llvm_ty(function.ret.clone()),
                mangle(function)
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
            Ty::array(Ty::Int(IntTy::I32), crate::ast::Mutability::Shared),
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
                    ty: Ty::array(Ty::Int(IntTy::I32), crate::ast::Mutability::Owned),
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
        refresh.params = vec![parameter("old", Ty::ClassRef(0, Mutability::Shared))];
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
            parameter("borrowed", Ty::ClassRef(0, Mutability::Shared)),
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
            parameter("left", Ty::ClassRef(1, Mutability::Mut)),
            parameter("right", Ty::ClassRef(1, Mutability::Mut)),
        ];
        let mutable_reference = Ty::ClassRef(1, Mutability::Mut);
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
        bad_method.params = vec![parameter("receiver", Ty::ClassRef(99, Mutability::Mut))];
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
