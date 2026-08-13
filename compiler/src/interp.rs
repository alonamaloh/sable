//! `sable test`: the tree-walking interpreter with trap semantics
//! (design §9). Every partial operation is checked exactly where the
//! verifier would emit a VC — overflow, bounds, division — and every
//! monitorable contract (pre, post, invariant, variant) is evaluated
//! dynamically via `speceval`. Unmonitorable clauses are reported as
//! skipped, never guessed.
//!
//! This is a dev tool in the sanitizer category: its results are not a
//! verification claim, and test functions are never verified.

use crate::ast::*;
use crate::speceval::{self, GhostDefs, SpecArray, SpecEnv, SpecVal};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::rc::Rc;

#[derive(Debug, Clone)]
pub enum RtVal {
    Int(i128),
    Bool(bool),
    Arr(Rc<RefCell<RtArray>>),
    /// An ordinary option. The checked payload type is retained even for
    /// `none`, because the dynamic proof monitor must implement the typed
    /// `Option.value = getD default` model (`0` for integers, `false` for
    /// booleans) after a function returns.
    Opt {
        payload: ValueTy,
        value: Option<Box<RtVal>>,
    },
    PtrOpt(Option<(i128, i128)>),
    /// A POD record is a plain copyable value, distinct from an affine
    /// class object and its destructor-bearing field storage (ADR 0054).
    Record {
        record: usize,
        fields: HashMap<String, RtVal>,
    },
    Obj {
        class: usize,
        fields: Rc<RefCell<HashMap<String, RtVal>>>,
    },
    /// A raw pointer: allocation id plus byte offset (ADR 0025/0026).
    Ptr(i128, i128),
    /// Sanitizer-only shadow state for an erased resource map. The machine
    /// still carries no authority value; this set independently catches an
    /// absent take or duplicate put in unverified `test_` code.
    ResMap(Rc<RefCell<HashSet<i128>>>),
    Unit,
}

/// Runtime arrays retain their checked payload even when empty. Integer
/// widths remain explicit so snapshots and literal/allocation construction
/// cannot silently change the array's source type.
#[derive(Debug, Clone)]
pub enum RtArray {
    Int { payload: IntTy, values: Vec<i128> },
    Bool(Vec<bool>),
}

#[derive(Clone, Copy)]
pub enum RtArrayElem {
    Int(i128),
    Bool(bool),
}

impl fmt::Display for RtArrayElem {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RtArrayElem::Int(value) => value.fmt(formatter),
            RtArrayElem::Bool(value) => value.fmt(formatter),
        }
    }
}

pub enum RtArrayIter<'a> {
    Int(std::slice::Iter<'a, i128>),
    Bool(std::slice::Iter<'a, bool>),
}

impl Iterator for RtArrayIter<'_> {
    type Item = RtArrayElem;

    fn next(&mut self) -> Option<RtArrayElem> {
        match self {
            RtArrayIter::Int(values) => values.next().copied().map(RtArrayElem::Int),
            RtArrayIter::Bool(values) => values.next().copied().map(RtArrayElem::Bool),
        }
    }
}

impl RtArray {
    pub fn len(&self) -> usize {
        match self {
            RtArray::Int { values, .. } => values.len(),
            RtArray::Bool(values) => values.len(),
        }
    }

    pub fn iter(&self) -> RtArrayIter<'_> {
        match self {
            RtArray::Int { values, .. } => RtArrayIter::Int(values.iter()),
            RtArray::Bool(values) => RtArrayIter::Bool(values.iter()),
        }
    }

    fn from_values(payload: ValueTy, values: Vec<RtVal>) -> RtArray {
        match payload {
            ValueTy::Int(integer) if !matches!(integer, IntTy::TParam(_)) => RtArray::Int {
                payload: integer,
                values: values
                    .into_iter()
                    .map(|value| match value {
                        RtVal::Int(value) => value,
                        _ => unreachable!("checked: integer array element"),
                    })
                    .collect(),
            },
            ValueTy::Bool => RtArray::Bool(
                values
                    .into_iter()
                    .map(|value| match value {
                        RtVal::Bool(value) => value,
                        _ => unreachable!("checked: Boolean array element"),
                    })
                    .collect(),
            ),
            _ => unreachable!("interpreter guard rejected unsupported array payload"),
        }
    }

    fn repeat(payload: ValueTy, value: RtVal, len: usize) -> RtArray {
        match (payload, value) {
            (ValueTy::Int(integer), RtVal::Int(value)) if !matches!(integer, IntTy::TParam(_)) => {
                RtArray::Int {
                    payload: integer,
                    values: vec![value; len],
                }
            }
            (ValueTy::Bool, RtVal::Bool(value)) => RtArray::Bool(vec![value; len]),
            _ => unreachable!("checked: array initializer matches its payload"),
        }
    }

    fn get(&self, index: usize) -> RtVal {
        match self {
            RtArray::Int { values, .. } => RtVal::Int(values[index]),
            RtArray::Bool(values) => RtVal::Bool(values[index]),
        }
    }

    fn set(&mut self, index: usize, value: RtVal) {
        match (self, value) {
            (RtArray::Int { values, .. }, RtVal::Int(value)) => values[index] = value,
            (RtArray::Bool(values), RtVal::Bool(value)) => values[index] = value,
            _ => unreachable!("checked: array store value matches its payload"),
        }
    }

    fn int_values(&self) -> Option<&[i128]> {
        match self {
            RtArray::Int { values, .. } => Some(values),
            RtArray::Bool(_) => None,
        }
    }

    fn set_int(&mut self, index: usize, value: i128) {
        match self {
            RtArray::Int { values, .. } => values[index] = value,
            RtArray::Bool(_) => unreachable!("interpreter guard rejects Boolean exposure"),
        }
    }

    fn to_spec(&self) -> SpecArray {
        match self {
            RtArray::Int { payload, values } => SpecArray::Int {
                payload: *payload,
                values: values.clone(),
            },
            RtArray::Bool(values) => SpecArray::Bool(values.clone()),
        }
    }
}

pub struct TestReport {
    pub name: String,
    /// Err carries a rendered failure message.
    pub outcome: Result<(), String>,
    /// Clauses that could not be checked dynamically (text, reason).
    pub skipped: Vec<(String, String)>,
}

/// One ordered profile-mediated MMIO observation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MmioEvent {
    Read {
        address: i128,
        width: u8,
        value: i128,
    },
    Write {
        address: i128,
        width: u8,
        value: i128,
    },
}

/// Interpreter outcome plus the externally observable device trace.
pub struct ObservedRun {
    pub outcome: Result<RtVal, String>,
    pub mmio: Vec<MmioEvent>,
    /// Selected test profile and number of status-oracle observations.
    pub uart_profile: Option<i128>,
    pub uart_cursor: usize,
}

struct Trap {
    message: String,
    span: crate::span::Span,
    /// This failure is the machine's `undef`, not a trap. The interpreter
    /// is allowed to be *more precise* than the machine — it says which
    /// rule was broken — as long as it agrees on the classification, which
    /// is what the differential harness compares (ADR 0025).
    undef: bool,
}

type IResult<T> = Result<T, Trap>;

const FUEL: u64 = 50_000_000;

/// Raw `Program` callers need the same explicit domain boundary as normal
/// checked callers: newly executable Boolean arrays are owned locals only.
/// Integer arrays retain their established positions; Boolean arrays do not
/// acquire a parameter, return, field, borrow, or exposure ABI in G1.4b.
fn validate_interp_program(program: &Program) -> Result<(), String> {
    // Retained generic templates are proof artifacts and are never executed by
    // the interpreter.  They intentionally contain `ValueTy::Param`; validate
    // only the executable, monomorphized portion of the program.
    for function in &program.fns {
        validate_interp_fn(function)?;
    }

    for class in &program.classes {
        for field in &class.fields {
            validate_interp_nonlocal_option_position(
                field.ty,
                &format!("field `{}.{}`", class.name, field.name),
            )?;
        }
        for init in &class.inits {
            validate_interp_fn(init)?;
        }
        for method in &class.methods {
            validate_interp_fn(&method.f)?;
        }
        if let Some(deinit) = &class.deinit {
            validate_interp_stmts(deinit, &mut HashMap::new())?;
        }
    }

    for record in &program.records {
        for field in &record.fields {
            validate_interp_nonlocal_option_position(
                field.ty,
                &format!("field `{}.{}`", record.name, field.name),
            )?;
        }
    }

    Ok(())
}

fn validate_interp_fn(function: &Fn) -> Result<(), String> {
    let mut locals = HashMap::new();
    for param in &function.params {
        validate_interp_nonlocal_option_position(param.ty, &format!("parameter `{}`", param.name))?;
        locals.insert(param.name.clone(), param.ty);
    }
    if matches!(function.ret, Ty::Array(ValueTy::Bool, _)) {
        return Err(format!(
            "interp.array_position_unsupported: return type of `{}` is a Boolean array; G1.4b supports Boolean arrays only as owned locals",
            function.name
        ));
    }
    validate_interp_ty(function.ret, &format!("return type of `{}`", function.name))?;
    validate_interp_stmts(&function.body, &mut locals)
}

/// G1.1 gives ordinary value options local/return semantics only. Keep raw
/// `Program` callers behind the same boundary as the checker: a parameter or
/// stored class/record field must not acquire an accidental Option ABI merely
/// because the interpreter knows how to execute a local `option<bool>`.
fn validate_interp_nonlocal_option_position(ty: Ty, context: &str) -> Result<(), String> {
    if matches!(ty, Ty::Option(_)) {
        return Err(format!(
            "interp.option_position_unsupported: {context} is option-valued; \
             G1.1 supports ordinary options only as returns and locals"
        ));
    }
    if matches!(ty, Ty::Array(ValueTy::Bool, _)) {
        return Err(format!(
            "interp.array_position_unsupported: {context} is a Boolean array; \
             G1.4b supports Boolean arrays only as owned locals"
        ));
    }
    validate_interp_ty(ty, context)
}

fn affine_option_interp_error(ty: Ty, context: &str) -> String {
    format!(
        "interp.affine_option_unsupported: `{}` is represented but has no move, take, join, destruction, or runtime semantics in {context}",
        ty.name()
    )
}

fn validate_interp_ty(ty: Ty, context: &str) -> Result<(), String> {
    match ty {
        Ty::AffineOption(_) => Err(affine_option_interp_error(ty, context)),
        Ty::Array(ValueTy::Bool, Mutability::Owned) => Ok(()),
        Ty::Array(ValueTy::Bool, _) => Err(format!(
            "interp.array_position_unsupported: {context} is a borrowed Boolean array; \
             G1.4b supports Boolean arrays only as owned locals"
        )),
        Ty::Array(payload, _) => validate_interp_array_payload(payload, context),
        Ty::Option(payload) => validate_interp_option_payload(payload, context),
        Ty::Param(_) | Ty::Int(IntTy::TParam(_)) | Ty::Raw(IntTy::TParam(_)) => Err(format!(
            "interp.type_parameter_unsupported: {context} contains an unresolved type parameter"
        )),
        _ => Ok(()),
    }
}

fn validate_interp_array_payload(payload: ValueTy, context: &str) -> Result<(), String> {
    match payload {
        ValueTy::Int(integer) if !matches!(integer, IntTy::TParam(_)) => Ok(()),
        ValueTy::Bool => Ok(()),
        _ => Err(format!(
            "interp.aggregate_payload_unsupported: {context} has array payload `{}`; \
             the interpreter currently executes only concrete integer and Boolean payloads",
            payload.name()
        )),
    }
}

fn validate_interp_option_payload(payload: ValueTy, context: &str) -> Result<(), String> {
    match payload {
        ValueTy::Int(integer) if !matches!(integer, IntTy::TParam(_)) => Ok(()),
        ValueTy::Bool => Ok(()),
        _ => Err(format!(
            "interp.aggregate_payload_unsupported: {context} has option payload `{}`; \
             the interpreter currently executes only concrete integer and Boolean option payloads",
            payload.name()
        )),
    }
}

fn validate_interp_stmts(stmts: &[Stmt], locals: &mut HashMap<String, Ty>) -> Result<(), String> {
    for stmt in stmts {
        match stmt {
            Stmt::Decl { ty, init, name, .. } => {
                validate_interp_ty(*ty, &format!("declaration `{name}`"))?;
                if let Some(init) = init {
                    validate_interp_expr(init, locals)?;
                    validate_interp_sink(*ty, init, locals, &format!("declaration `{name}`"))?;
                } else if matches!(ty, Ty::Array(ValueTy::Bool, _)) {
                    return Err(format!(
                        "interp.array_position_unsupported: Boolean array local `{name}` must be initialized by an owned literal or allocation"
                    ));
                }
                locals.insert(name.clone(), *ty);
            }
            Stmt::Assign { name, value, .. } => {
                let destination = locals.get(name).copied().ok_or_else(|| {
                    format!("interp.unknown_local: assignment to unknown local `{name}`")
                })?;
                if matches!(destination, Ty::Array(ValueTy::Bool, _)) {
                    return Err(format!(
                        "interp.array_position_unsupported: Boolean array `{name}` cannot be rebound; use an element store"
                    ));
                }
                validate_interp_sink(destination, value, locals, &format!("assignment `{name}`"))?;
            }
            Stmt::ExprStmt(value) => {
                validate_interp_expr(value, locals)?;
                reject_bool_array_transport(value, locals, "expression statement")?;
            }
            Stmt::FieldAssign { value, .. } => {
                validate_interp_expr(value, locals)?;
                reject_bool_array_transport(value, locals, "field assignment")?;
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                validate_interp_sink(Ty::Bool, cond, locals, "if condition")?;
                let mut then_locals = locals.clone();
                validate_interp_stmts(then_block, &mut then_locals)?;
                if let Some(else_block) = else_block {
                    let mut else_locals = locals.clone();
                    validate_interp_stmts(else_block, &mut else_locals)?;
                }
            }
            Stmt::Return { value, .. } => {
                if let Some(value) = value {
                    if matches!(value.ty, Some(Ty::Array(ValueTy::Bool, _))) {
                        return Err(
                            "interp.array_position_unsupported: returning a Boolean array; G1.4b supports Boolean arrays only as owned locals"
                                .into(),
                        );
                    }
                    validate_interp_expr(value, locals)?;
                    reject_bool_array_transport(value, locals, "return")?;
                }
            }
            Stmt::Assert(_) => {}
            Stmt::VarDecl { name, init, ty, .. } => {
                if let Some(ty) = ty {
                    validate_interp_ty(*ty, &format!("inferred declaration `{name}`"))?;
                }
                validate_interp_expr(init, locals)?;
                let inferred = (*ty).or(init.ty).ok_or_else(|| {
                    format!("interp.missing_type: inferred declaration `{name}` has no type")
                })?;
                validate_interp_sink(inferred, init, locals, &format!("declaration `{name}`"))?;
                locals.insert(name.clone(), inferred);
            }
            Stmt::FieldStore { index, value, .. } => {
                validate_interp_sink(
                    Ty::Int(IntTy::U64),
                    index,
                    locals,
                    "array field store index",
                )?;
                validate_interp_expr(value, locals)?;
                reject_bool_array_transport(value, locals, "array field store")?;
            }
            Stmt::Store {
                array,
                index,
                value,
                ..
            } => {
                let array_ty = locals.get(array).copied().ok_or_else(|| {
                    format!("interp.unknown_local: store names unknown array `{array}`")
                })?;
                let Ty::Array(payload, _) = array_ty else {
                    return Err(format!(
                        "interp.not_array: store target `{array}` is not an array"
                    ));
                };
                let element_ty = value_ty(payload).ok_or_else(|| {
                    format!(
                        "interp.aggregate_payload_unsupported: store target `{array}` has unsupported payload `{}`",
                        payload.name()
                    )
                })?;
                validate_interp_sink(Ty::Int(IntTy::U64), index, locals, "array store index")?;
                validate_interp_sink(element_ty, value, locals, "array store value")?;
            }
            Stmt::While { cond, body, .. } => {
                validate_interp_sink(Ty::Bool, cond, locals, "while condition")?;
                let mut body_locals = locals.clone();
                validate_interp_stmts(body, &mut body_locals)?;
            }
            Stmt::Unsafe { body, .. } => {
                validate_interp_stmts(body, locals)?;
            }
            Stmt::Expose {
                array,
                ptr,
                res,
                body,
                ..
            } => {
                if locals.get(array) == Some(&Ty::Array(ValueTy::Bool, Mutability::Owned)) {
                    return Err(format!(
                        "interp.array_position_unsupported: exposure of Boolean array `{array}`; G1.4b Boolean arrays are safe owned locals only"
                    ));
                }
                let mut body_locals = locals.clone();
                body_locals.insert(ptr.clone(), Ty::Raw(IntTy::U8));
                body_locals.insert(res.clone(), Ty::Res(ResKind::RawSpan));
                validate_interp_stmts(body, &mut body_locals)?;
            }
            Stmt::StaticAlloc { size, ptr, res, .. } => {
                validate_interp_sink(Ty::Int(IntTy::U64), size, locals, "static allocation size")?;
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
                validate_interp_sink(Ty::Int(IntTy::U64), size, locals, "system allocation size")?;
                locals.insert(ptr.clone(), Ty::Raw(IntTy::U8));
                locals.insert(res.clone(), Ty::Res(ResKind::RawSpan));
                locals.insert(release.clone(), Ty::Res(ResKind::SystemDealloc));
            }
            Stmt::SystemDealloc {
                ptr, res, release, ..
            } => {
                validate_interp_expr(ptr, locals)?;
                reject_bool_array_transport_if_present(ptr, locals, "system deallocation pointer")?;
                validate_interp_expr(res, locals)?;
                reject_bool_array_transport_if_present(
                    res,
                    locals,
                    "system deallocation resource",
                )?;
                validate_interp_expr(release, locals)?;
                reject_bool_array_transport_if_present(
                    release,
                    locals,
                    "system deallocation release token",
                )?;
            }
        }
    }
    Ok(())
}

fn validate_interp_expr(expr: &Expr, locals: &HashMap<String, Ty>) -> Result<(), String> {
    // Resolve source places independently of their cached annotations.  Raw
    // AST callers must not be able to relabel an affine option and send it
    // through the ordinary `RtVal::Opt` implementation.
    let named_source = match &expr.kind {
        ExprKind::Var(name)
        | ExprKind::Index { array: name, .. }
        | ExprKind::Len { array: name }
        | ExprKind::Borrow { array: name, .. }
        | ExprKind::MethodCall { recv: name, .. }
        | ExprKind::ClassField { obj: name, .. }
        | ExprKind::RecordField { obj: name, .. }
        | ExprKind::ClassFieldLen { obj: name, .. }
        | ExprKind::ClassFieldIndex { obj: name, .. } => Some(name),
        _ => None,
    };
    if let Some(ty @ Ty::AffineOption(_)) = named_source.and_then(|name| locals.get(name)).copied()
    {
        return Err(affine_option_interp_error(ty, "expression source"));
    }
    if let Some(ty) = expr.ty {
        validate_interp_ty(ty, "expression annotation")?;
    }
    if matches!(expr.ty, Some(Ty::Array(ValueTy::Bool, _)))
        && !matches!(
            expr.kind,
            ExprKind::ArrayLit(_) | ExprKind::AllocArray { .. } | ExprKind::Var(_)
        )
    {
        return Err(
            "interp.array_position_unsupported: only owned Boolean array literals, allocations, and their local places are executable"
                .into(),
        );
    }

    match &expr.kind {
        ExprKind::Index { array, index, .. } => {
            let array_ty = locals.get(array).copied().ok_or_else(|| {
                format!("interp.unknown_local: index names unknown array `{array}`")
            })?;
            let Ty::Array(payload, _) = array_ty else {
                return Err(format!(
                    "interp.not_array: indexed local `{array}` is not an array"
                ));
            };
            validate_interp_sink(Ty::Int(IntTy::U64), index, locals, "array index")?;
            let result_ty = value_ty(payload).ok_or_else(|| {
                format!(
                    "interp.aggregate_payload_unsupported: indexed array `{array}` has unsupported payload `{}`",
                    payload.name()
                )
            })?;
            require_cached_type(expr, result_ty, "array index result")?;
        }
        ExprKind::AllocArray { elem, len, init } => {
            validate_interp_array_payload(*elem, "alloc_array")?;
            let expected = Ty::Array(*elem, Mutability::Owned);
            require_cached_type(expr, expected, "alloc_array result")?;
            validate_interp_sink(Ty::Int(IntTy::U64), len, locals, "alloc_array length")?;
            validate_interp_sink(
                value_ty(*elem).expect("validated concrete interpreter array payload"),
                init,
                locals,
                "alloc_array initializer",
            )?;
        }
        ExprKind::Widen { target, arg } | ExprKind::Narrow { target, arg } => {
            if matches!(target, IntTy::TParam(_)) {
                return Err(
                    "interp.type_parameter_unsupported: conversion target contains an unresolved type parameter"
                        .into(),
                );
            }
            validate_interp_expr(arg, locals)?;
            if !matches!(
                semantic_interp_ty(arg, locals)?,
                Ty::Int(integer) if !matches!(integer, IntTy::TParam(_))
            ) {
                return Err(
                    "interp.expression_type: integer conversion operand must have a concrete integer type"
                        .into(),
                );
            }
            require_cached_type(expr, Ty::Int(*target), "integer conversion result")?;
        }
        ExprKind::Call {
            type_args, args, ..
        }
        | ExprKind::CtorCall {
            type_args, args, ..
        } => {
            if !type_args.is_empty() {
                return Err(
                    "interp.type_parameter_unsupported: generic type arguments escaped monomorphization"
                        .into(),
                );
            }
            for arg in args {
                validate_interp_expr(arg, locals)?;
                reject_bool_array_transport(arg, locals, "call argument")?;
            }
            reject_bool_array_result(expr, "call result")?;
        }
        ExprKind::Unary { op, operand } => match op {
            UnOp::Not => {
                validate_interp_sink(Ty::Bool, operand, locals, "Boolean negation operand")?;
                require_cached_type(expr, Ty::Bool, "Boolean negation result")?;
            }
            UnOp::Neg => {
                validate_interp_expr(operand, locals)?;
                let operand_ty = semantic_interp_ty(operand, locals)?;
                if !matches!(operand_ty, Ty::Int(integer) if !matches!(integer, IntTy::TParam(_))) {
                    return Err(
                        "interp.expression_type: negation operand must be a concrete integer"
                            .into(),
                    );
                }
                require_cached_type(expr, operand_ty, "integer negation result")?;
            }
        },
        ExprKind::IsSome { operand } => {
            validate_interp_expr(operand, locals)?;
            let operand_ty = semantic_interp_ty(operand, locals)?;
            if !matches!(operand_ty, Ty::Option(_) | Ty::OptionRaw(_)) {
                return Err(format!(
                    "interp.option_operand: `.is_some` needs an option, found `{}`",
                    operand_ty.name()
                ));
            }
            require_cached_type(expr, Ty::Bool, "`.is_some` result")?;
        }
        ExprKind::OptValue { operand } => {
            validate_interp_expr(operand, locals)?;
            let operand_ty = semantic_interp_ty(operand, locals)?;
            let result_ty = option_value_ty(operand_ty).ok_or_else(|| {
                format!(
                    "interp.option_operand: `.value` needs an option, found `{}`",
                    operand_ty.name()
                )
            })?;
            require_cached_type(expr, result_ty, "`.value` result")?;
        }
        ExprKind::SomeE(operand) => {
            validate_interp_expr(operand, locals)?;
            reject_bool_array_transport(operand, locals, "option payload")?;
        }
        ExprKind::Binary { op, lhs, rhs, .. } => match op {
            BinOp::And | BinOp::Or => {
                validate_interp_sink(Ty::Bool, lhs, locals, "Boolean left operand")?;
                validate_interp_sink(Ty::Bool, rhs, locals, "Boolean right operand")?;
                require_cached_type(expr, Ty::Bool, "Boolean operator result")?;
            }
            op => {
                validate_interp_expr(lhs, locals)?;
                validate_interp_expr(rhs, locals)?;
                let left = semantic_interp_ty(lhs, locals)?;
                let right = semantic_interp_ty(rhs, locals)?;
                if left != right
                    || !matches!(left, Ty::Int(integer) if !matches!(integer, IntTy::TParam(_)))
                {
                    return Err(
                        "interp.expression_type: integer operator operands must have one concrete integer type"
                            .into(),
                    );
                }
                require_cached_type(
                    expr,
                    if op.is_comparison() { Ty::Bool } else { left },
                    "integer operator result",
                )?;
            }
        },
        ExprKind::RawOp { args, .. }
        | ExprKind::DeviceOp { args, .. }
        | ExprKind::ResOp { args, .. }
        | ExprKind::TraitCall { args, .. }
        | ExprKind::RecordLit { args, .. } => {
            for arg in args {
                validate_interp_expr(arg, locals)?;
                reject_bool_array_transport(arg, locals, "operation argument")?;
            }
            reject_bool_array_result(expr, "operation result")?;
        }
        ExprKind::MethodCall { recv, args, .. } => {
            reject_bool_array_named_receiver(recv, locals, "method receiver")?;
            for arg in args {
                validate_interp_expr(arg, locals)?;
                reject_bool_array_transport(arg, locals, "method argument")?;
            }
            reject_bool_array_result(expr, "method result")?;
        }
        ExprKind::ArrayLit(elements) => {
            let Some(Ty::Array(payload, Mutability::Owned)) = expr.ty else {
                return Err(
                    "interp.array_literal_type: array literal must have an owned array annotation"
                        .into(),
                );
            };
            validate_interp_array_payload(payload, "array literal")?;
            let element_ty =
                value_ty(payload).expect("validated concrete interpreter array literal payload");
            for element in elements {
                validate_interp_sink(element_ty, element, locals, "array literal element")?;
            }
        }
        ExprKind::SelfFieldIndex { index, .. } => {
            validate_interp_sink(Ty::Int(IntTy::U64), index, locals, "self field array index")?;
            reject_bool_array_result(expr, "array field index result")?;
        }
        ExprKind::ClassFieldIndex { obj, index, .. } => {
            reject_bool_array_named_receiver(obj, locals, "class-field index receiver")?;
            validate_interp_sink(
                Ty::Int(IntTy::U64),
                index,
                locals,
                "class field array index",
            )?;
            reject_bool_array_result(expr, "array field index result")?;
        }
        ExprKind::IntLit(_) => {
            if !matches!(expr.ty, Some(Ty::Int(integer)) if !matches!(integer, IntTy::TParam(_))) {
                return Err(
                    "interp.literal_type: integer literal lacks a concrete integer type".into(),
                );
            }
        }
        ExprKind::BoolLit(_) => require_cached_type(expr, Ty::Bool, "Boolean literal")?,
        ExprKind::Var(name) => {
            let ty = locals.get(name).copied().ok_or_else(|| {
                format!("interp.unknown_local: expression names unknown local `{name}`")
            })?;
            if let Some(cached) = expr.ty {
                if cached != ty && !ty.is_resource() {
                    return Err(format!(
                        "interp.expression_type: local `{name}` has type `{}` but its expression is annotated `{}`",
                        ty.name(),
                        cached.name()
                    ));
                }
            }
        }
        ExprKind::Len { array } => {
            if !matches!(locals.get(array), Some(Ty::Array(..))) {
                return Err(format!(
                    "interp.unknown_local: length names unknown or non-array local `{array}`"
                ));
            }
            require_cached_type(expr, Ty::Int(IntTy::U64), "array length")?;
        }
        ExprKind::NoneE => {}
        ExprKind::SelfField { .. } | ExprKind::SelfFieldLen { .. } => {
            reject_bool_array_result(expr, "field access")?
        }
        ExprKind::ClassField { obj, .. }
        | ExprKind::RecordField { obj, .. }
        | ExprKind::ClassFieldLen { obj, .. } => {
            reject_bool_array_named_receiver(obj, locals, "field receiver")?;
            reject_bool_array_result(expr, "field access")?;
        }
        ExprKind::Borrow { array, .. } => {
            if locals.get(array) == Some(&Ty::Array(ValueTy::Bool, Mutability::Owned)) {
                return Err(format!(
                    "interp.array_position_unsupported: borrow of Boolean array `{array}`; G1.4b Boolean arrays are owned locals only"
                ));
            }
        }
    }
    Ok(())
}

fn value_ty(payload: ValueTy) -> Option<Ty> {
    match payload {
        ValueTy::Int(IntTy::TParam(_)) => None,
        ValueTy::Int(integer) => Some(Ty::Int(integer)),
        ValueTy::Bool => Some(Ty::Bool),
        ValueTy::Record(_) | ValueTy::Param(_) => None,
    }
}

fn option_value_ty(option: Ty) -> Option<Ty> {
    match option {
        Ty::Option(payload) => value_ty(payload),
        Ty::OptionRaw(record) => Some(Ty::RawRecord(record)),
        _ => None,
    }
}

fn reject_bool_array_named_receiver(
    name: &str,
    locals: &HashMap<String, Ty>,
    context: &str,
) -> Result<(), String> {
    if matches!(locals.get(name), Some(Ty::Array(ValueTy::Bool, _))) {
        return Err(format!(
            "interp.array_position_unsupported: {context} `{name}` is a Boolean array, not an object"
        ));
    }
    Ok(())
}

fn require_cached_type(expr: &Expr, expected: Ty, context: &str) -> Result<(), String> {
    if expr.ty == Some(expected) {
        Ok(())
    } else {
        Err(format!(
            "interp.expression_type: {context} must have type `{}`, found `{}`",
            expected.name(),
            expr.ty.map_or_else(|| "<missing>".into(), Ty::name)
        ))
    }
}

fn semantic_interp_ty(expr: &Expr, locals: &HashMap<String, Ty>) -> Result<Ty, String> {
    match &expr.kind {
        ExprKind::BoolLit(_) => Ok(Ty::Bool),
        ExprKind::IntLit(_) => match expr.ty {
            Some(ty @ Ty::Int(integer)) if !matches!(integer, IntTy::TParam(_)) => Ok(ty),
            _ => Err("interp.literal_type: integer literal lacks a concrete integer type".into()),
        },
        ExprKind::Var(name) => locals.get(name).copied().ok_or_else(|| {
            format!("interp.unknown_local: expression names unknown local `{name}`")
        }),
        ExprKind::Index { array, .. } => match locals.get(array).copied() {
            Some(Ty::Array(payload, _)) => value_ty(payload).ok_or_else(|| {
                format!("interp.aggregate_payload_unsupported: `{array}` has unsupported payload")
            }),
            _ => Err(format!(
                "interp.not_array: indexed local `{array}` is not an array"
            )),
        },
        ExprKind::Len { .. } => Ok(Ty::Int(IntTy::U64)),
        ExprKind::AllocArray { elem, .. } => Ok(Ty::Array(*elem, Mutability::Owned)),
        ExprKind::ArrayLit(_) => expr
            .ty
            .ok_or_else(|| "interp.array_literal_type: missing array literal type".into()),
        ExprKind::Unary { op, .. } => match op {
            UnOp::Not => Ok(Ty::Bool),
            UnOp::Neg => expr
                .ty
                .ok_or_else(|| "interp.expression_type: missing negation type".into()),
        },
        ExprKind::Binary { op, .. }
            if matches!(op, BinOp::And | BinOp::Or) || op.is_comparison() =>
        {
            Ok(Ty::Bool)
        }
        ExprKind::Widen { target, .. } | ExprKind::Narrow { target, .. } => Ok(Ty::Int(*target)),
        _ => expr
            .ty
            .ok_or_else(|| "interp.expression_type: expression has no cached type".into()),
    }
}

fn validate_interp_sink(
    expected: Ty,
    expr: &Expr,
    locals: &HashMap<String, Ty>,
    context: &str,
) -> Result<(), String> {
    validate_interp_expr(expr, locals)?;
    let actual = semantic_interp_ty(expr, locals)?;
    if actual != expected {
        return Err(format!(
            "interp.expression_type: {context} expects `{}`, found `{}`",
            expected.name(),
            actual.name()
        ));
    }
    if matches!(expected, Ty::Array(ValueTy::Bool, _))
        && !matches!(
            expr.kind,
            ExprKind::ArrayLit(_) | ExprKind::AllocArray { .. }
        )
    {
        return Err(format!(
            "interp.array_position_unsupported: {context} receives a Boolean array through an unsupported transport; only owned literals and allocations are executable"
        ));
    }
    Ok(())
}

fn reject_bool_array_transport(
    expr: &Expr,
    locals: &HashMap<String, Ty>,
    context: &str,
) -> Result<(), String> {
    // Checked affine-resource places deliberately may have no cached `Expr.ty`:
    // their sealed operand position is the typing authority.  This guard only
    // needs to recognize Boolean-array transport, so do not demand unrelated
    // scalar/resource metadata here.  Named locals are resolved from the
    // active environment to prevent a forged cache from hiding an array.
    let transports_bool_array = match &expr.kind {
        ExprKind::Var(name) => matches!(locals.get(name), Some(Ty::Array(ValueTy::Bool, _))),
        _ => matches!(expr.ty, Some(Ty::Array(ValueTy::Bool, _))),
    };
    if transports_bool_array {
        return Err(format!(
            "interp.array_position_unsupported: {context} transports a Boolean array; G1.4b Boolean arrays are owned locals only"
        ));
    }
    Ok(())
}

/// Resource operands may intentionally omit cached `Expr::ty` metadata.
/// This narrower boundary check rejects the newly executable Boolean-array
/// representation without turning that established erasure convention into
/// a new annotation requirement.
fn reject_bool_array_transport_if_present(
    expr: &Expr,
    locals: &HashMap<String, Ty>,
    context: &str,
) -> Result<(), String> {
    let is_bool_array = matches!(expr.ty, Some(Ty::Array(ValueTy::Bool, _)))
        || matches!(
            &expr.kind,
            ExprKind::Var(name)
                if matches!(locals.get(name), Some(Ty::Array(ValueTy::Bool, _)))
        );
    if is_bool_array {
        return Err(format!(
            "interp.array_position_unsupported: {context} cannot receive a Boolean array"
        ));
    }
    Ok(())
}

fn reject_bool_array_result(expr: &Expr, context: &str) -> Result<(), String> {
    if matches!(expr.ty, Some(Ty::Array(ValueTy::Bool, _))) {
        return Err(format!(
            "interp.array_position_unsupported: {context} is a Boolean array; G1.4b permits only owned literal/allocation results"
        ));
    }
    Ok(())
}

/// Most resources are wholly erased even in the interpreter. A resource map
/// alone carries sanitizer shadow metadata so invalid test code can be caught
/// independently of Lean; that metadata must follow ordinary Sable calls even
/// though no backend ABI receives it.
fn has_resource_shadow(ty: Ty) -> bool {
    matches!(
        ty,
        Ty::Res(ResKind::ResourceMapPointsToU64)
            | Ty::ResRef(ResKind::ResourceMapPointsToU64, _)
            | Ty::Res(ResKind::ResourceMapPointsToRecord(_))
            | Ty::ResRef(ResKind::ResourceMapPointsToRecord(_), _)
    )
}

pub fn run_tests(program: &Program, mods: &crate::modules::ModuleSet) -> Vec<TestReport> {
    if let Err(error) = validate_interp_program(program) {
        return program
            .fns
            .iter()
            .filter(|function| function.name.starts_with("test_"))
            .map(|function| TestReport {
                name: function.name.clone(),
                outcome: Err(error.clone()),
                skipped: Vec::new(),
            })
            .collect();
    }

    let source = mods.combined_source.as_str();
    let ghosts = GhostDefs::from_items(&program.ghosts);
    let fns: HashMap<&str, &Fn> = program.fns.iter().map(|f| (f.name.as_str(), f)).collect();
    let classes = &program.classes;

    program
        .fns
        .iter()
        .filter(|f| f.name.starts_with("test_"))
        .map(|test| {
            let mut interp = Interp {
                fns: &fns,
                classes,
                records: &program.records,
                ghosts: &ghosts,
                source,
                fuel: FUEL,
                skipped: Vec::new(),
                raw: RawHeap::default(),
                world: None,
                uart: None,
            };
            let outcome = interp.call(test, Vec::new()).map(|_| ()).map_err(|trap| {
                let (file, line, col) = mods.locate(trap.span.start);
                format!("{} ({file}:{line}:{col})", trap.message)
            });
            TestReport {
                name: test.name.clone(),
                outcome,
                skipped: interp.skipped,
            }
        })
        .collect()
}

/// Run one zero-argument function, returning its value or the raw trap
/// message (no source location) — the interpreter side of the SVM
/// differential harness.
pub fn run_fn(
    program: &Program,
    mods: &crate::modules::ModuleSet,
    name: &str,
) -> Result<RtVal, String> {
    run_fn_observed(program, mods, name).outcome
}

/// Run one zero-argument function while retaining its ordered MMIO trace.
/// Existing callers that observe only the return/trap keep using `run_fn`.
pub fn run_fn_observed(
    program: &Program,
    mods: &crate::modules::ModuleSet,
    name: &str,
) -> ObservedRun {
    if let Err(error) = validate_interp_program(program) {
        return ObservedRun {
            outcome: Err(error),
            mmio: Vec::new(),
            uart_profile: None,
            uart_cursor: 0,
        };
    }

    let ghosts = GhostDefs::from_items(&program.ghosts);
    let fns: HashMap<&str, &Fn> = program.fns.iter().map(|f| (f.name.as_str(), f)).collect();
    let f = fns[name];
    let mut interp = Interp {
        fns: &fns,
        classes: &program.classes,
        records: &program.records,
        ghosts: &ghosts,
        source: mods.combined_source.as_str(),
        fuel: FUEL,
        skipped: Vec::new(),
        raw: RawHeap::default(),
        world: None,
        uart: None,
    };
    let outcome = interp.call(f, Vec::new()).map_err(|trap| {
        if trap.undef {
            format!("undef: {}", trap.message)
        } else {
            trap.message
        }
    });
    let mmio = interp
        .uart
        .as_ref()
        .map_or_else(Vec::new, |uart| uart.events.clone());
    let uart_profile = interp.uart.as_ref().map(|uart| uart.script);
    let uart_cursor = interp.uart.as_ref().map_or(0, |uart| uart.cursor);
    ObservedRun {
        outcome,
        mmio,
        uart_profile,
        uart_cursor,
    }
}

enum Flow {
    Normal,
    Return(RtVal),
}

struct Interp<'a> {
    fns: &'a HashMap<&'a str, &'a Fn>,
    classes: &'a [ClassDecl],
    records: &'a [RecordDecl],
    ghosts: &'a GhostDefs,
    source: &'a str,
    fuel: u64,
    skipped: Vec<(String, String)>,
    raw: RawHeap,
    /// `None` until a test asks for one. A program cannot conjure the
    /// world; only `posix_world` can, and only in a test.
    world: Option<PosixWorld>,
    /// `None` until a test selects a scripted UART profile.
    uart: Option<ScriptedUart>,
}

/// The interpreter's raw heap. It mirrors the SVM's: a fresh-provenance
/// counter and allocations that are marked dead rather than removed, so a
/// stale pointer stays distinguishable from a fresh one (ADR 0025).
///
/// Exposure is modelled the way the SVM models it — copy the array's
/// bytes into a fresh loan allocation, run the body, copy the final bytes
/// back — because that is what makes the escape rules observable: a
/// pointer that outlived its exposure would name a dead allocation.
#[derive(Default)]
struct RawHeap {
    next: i128,
    allocs: HashMap<i128, RawAlloc>,
}

struct RawAlloc {
    live: bool,
    /// `None` is uninitialized: distinct from any byte value.
    bytes: Vec<Option<i128>>,
    /// Starts of abstract typed `u64` extents. `None` is a typed but
    /// uninitialized cell; `Some(v)` is initialized. Bytes covered by a
    /// cell are inaccessible until the uninitialized cell is converted
    /// back (ADR 0031).
    cells_u64: HashMap<i128, Option<i128>>,
    /// Starts of abstract record-typed extents. The record index is the
    /// executable type tag; values stay abstract rather than serialized.
    cells_record: HashMap<i128, RecordCell>,
}

struct RecordCell {
    record: usize,
    layout: StorageLayout,
    value: Option<RtVal>,
}

impl RawHeap {
    fn fresh(&mut self, bytes: Vec<Option<i128>>) -> i128 {
        let id = self.next;
        self.next += 1;
        self.allocs.insert(
            id,
            RawAlloc {
                live: true,
                bytes,
                cells_u64: HashMap::new(),
                cells_record: HashMap::new(),
            },
        );
        id
    }

    fn live_at(&self, alloc: i128, off: i128) -> Option<&RawAlloc> {
        let al = self.allocs.get(&alloc)?;
        let covered = al
            .cells_u64
            .keys()
            .any(|start| *start <= off && off < *start + IntTy::U64.layout().size);
        let record_covered = al
            .cells_record
            .iter()
            .any(|(start, cell)| *start <= off && off < *start + cell.layout.size);
        if al.live && off >= 0 && (off as usize) < al.bytes.len() && !covered && !record_covered {
            Some(al)
        } else {
            None
        }
    }
}

/// The scripted external world `sable test` plays against.
///
/// A contract cannot predict a short read or an I/O error, so those live
/// here and never in the view (ADR 0028). The `script` argument to
/// `posix_world` selects the schedule, which is what makes external
/// behaviour something a test *author* controls rather than something that
/// happens to them.
struct PosixWorld {
    /// The byte stream descriptors read from, indexed by absolute position.
    data: Vec<i128>,
    /// How many descriptors the world has handed out.
    fds: i128,
    /// Descriptors whose *authority* has been adopted. The world can
    /// supply each one once: affinity governs a token that exists, and
    /// this is what stops a second one being minted beside it.
    claimed: HashSet<i128>,
    /// Which read attempts misbehave, by 0-based call index: `Short(k)`
    /// transfers `k` bytes, `Fail(e)` returns `-e`.
    schedule: Vec<ReadOutcome>,
    /// How many reads have happened.
    reads: usize,
    /// Positions, by descriptor.
    pos: Vec<i128>,
}

#[derive(Clone, Copy)]
enum ReadOutcome {
    Full,
    Short(i128),
    Fail(i128),
}

impl PosixWorld {
    /// Scripts are numbered so a test can name one. Each is deliberately
    /// small and deliberately nasty: the interesting cases are the ones a
    /// caller is tempted to assume away.
    fn scripted(script: i128) -> PosixWorld {
        let data: Vec<i128> = (0..16).map(|i| (i * 7 + 3) % 256).collect();
        let schedule = match script {
            // Everything succeeds.
            0 => vec![],
            // The second read is short by half.
            1 => vec![ReadOutcome::Full, ReadOutcome::Short(2)],
            // The first read fails outright (EIO).
            2 => vec![ReadOutcome::Fail(5)],
            // Short, then a failure, then fine again.
            _ => vec![
                ReadOutcome::Short(1),
                ReadOutcome::Fail(5),
                ReadOutcome::Full,
            ],
        };
        PosixWorld {
            data,
            fds: 3,
            claimed: HashSet::new(),
            schedule,
            reads: 0,
            pos: vec![0; 3],
        }
    }

    fn next_outcome(&mut self) -> ReadOutcome {
        let out = self
            .schedule
            .get(self.reads)
            .copied()
            .unwrap_or(ReadOutcome::Full);
        self.reads += 1;
        out
    }
}

struct ScriptedUart {
    script: i128,
    cursor: usize,
    ready: bool,
    events: Vec<MmioEvent>,
}

impl ScriptedUart {
    fn new(script: i128) -> ScriptedUart {
        ScriptedUart {
            script,
            cursor: 0,
            ready: false,
            events: Vec::new(),
        }
    }

    fn status(&mut self) -> i128 {
        let value = match self.script {
            0 => 1,
            1 if self.cursor < 2 => 0,
            1 => 1,
            _ => 0,
        };
        self.cursor += 1;
        self.ready = value != 0;
        self.events.push(MmioEvent::Read {
            address: 4096,
            width: 8,
            value,
        });
        value
    }

    fn write(&mut self, byte: i128) {
        self.events.push(MmioEvent::Write {
            address: 4097,
            width: 8,
            value: byte,
        });
        self.ready = false;
    }
}

/// A place a value can be moved out of or dropped: a local, or a field of
/// the enclosing `self`. These are the roots of the checker's `Place`, at
/// the depth the program language can name.
enum RtPlace {
    Local(String),
    SelfField(String),
}

impl RtPlace {
    /// How the place is spelled in a diagnostic.
    fn name(&self) -> String {
        match self {
            RtPlace::Local(n) => n.clone(),
            RtPlace::SelfField(f) => format!("self.{f}"),
        }
    }
}

struct Frame {
    vars: HashMap<String, RtVal>,
    /// Entry-state scalar params (post clauses mean entry values for
    /// by-value params) and entry snapshots of &mut state (`old a`,
    /// `old self`).
    entry_scalars: HashMap<String, RtVal>,
    olds: HashMap<String, SpecVal>,
    /// Member context: the class index and its field storage.
    self_ctx: Option<(usize, Rc<RefCell<HashMap<String, RtVal>>>)>,
}

impl<'a> Interp<'a> {
    /// The deterministic test shims. An extern has no Sable body, so
    /// `sable test` has to supply one — and it is keyed on the *audit id*,
    /// not the name, because the id is what names the contract version the
    /// program was verified against (ADR 0027).
    ///
    /// An unknown id traps. Running the body as a no-op would let a
    /// contract appear to hold because nothing happened, which is the one
    /// outcome a monitor must never produce.
    fn call_extern(
        &mut self,
        f: &'a Fn,
        args: Vec<RtVal>,
        span: crate::span::Span,
    ) -> IResult<RtVal> {
        let info = f.extern_info.as_ref().expect("checked: extern");
        match info.audit_id.as_str() {
            "test.fill.v1" => {
                let (RtVal::Ptr(a, off), RtVal::Int(n), RtVal::Int(v)) =
                    (args[0].clone(), args[1].clone(), args[2].clone())
                else {
                    unreachable!("checked: (raw<u8>, u64, u8)")
                };
                for i in 0..n {
                    if self.raw.live_at(a, off + i).is_none() {
                        return Err(Trap {
                            undef: true,
                            message: format!("`{}` writes out of bounds: {a}+{}", f.name, off + i),
                            span,
                        });
                    }
                    self.raw.allocs.get_mut(&a).expect("live_at checked").bytes
                        [(off + i) as usize] = Some(v);
                }
                Ok(RtVal::Unit)
            }
            "test.checksum.v1" => {
                let (RtVal::Ptr(a, off), RtVal::Int(n)) = (args[0].clone(), args[1].clone()) else {
                    unreachable!("checked: (raw<u8>, u64)")
                };
                let mut sum: i128 = 0;
                for i in 0..n {
                    match self
                        .raw
                        .live_at(a, off + i)
                        .map(|al| al.bytes[(off + i) as usize])
                    {
                        Some(Some(b)) => sum += b,
                        _ => {
                            return Err(Trap {
                                undef: true,
                                message: format!(
                                    "`{}` reads out of bounds or uninitialized: {a}+{}",
                                    f.name,
                                    off + i
                                ),
                                span,
                            });
                        }
                    }
                }
                Ok(RtVal::Int(sum))
            }
            // POSIX-shaped shims against the scripted world. Short reads
            // and failures come from the script, not from the contract:
            // no contract can predict them, which is why a caller has to
            // handle every outcome its post admits (ADR 0028).
            "posix.read.v1" => {
                let (RtVal::Int(fd), RtVal::Ptr(a, off), RtVal::Int(n)) =
                    (args[0].clone(), args[1].clone(), args[2].clone())
                else {
                    unreachable!("checked: (i32, raw<u8>, u64)")
                };
                let Some(w) = self.world.as_mut() else {
                    return Err(Trap {
                        undef: false,
                        message: format!("`{}` called with no world in play", f.name),
                        span,
                    });
                };
                if fd < 0 || fd >= w.fds {
                    return Err(Trap {
                        undef: true,
                        message: format!("`{}`: descriptor {fd} was never handed out", f.name),
                        span,
                    });
                }
                let want = match w.next_outcome() {
                    ReadOutcome::Full => n,
                    ReadOutcome::Short(k) => k.min(n),
                    ReadOutcome::Fail(e) => return Ok(RtVal::Int(-e)),
                };
                let pos = w.pos[fd as usize];
                let avail = (w.data.len() as i128 - pos).max(0);
                let got = want.min(avail);
                let bytes: Vec<i128> = (0..got).map(|i| w.data[(pos + i) as usize]).collect();
                w.pos[fd as usize] = pos + got;
                for (i, b) in bytes.iter().enumerate() {
                    let at = off + i as i128;
                    if self.raw.live_at(a, at).is_none() {
                        return Err(Trap {
                            undef: true,
                            message: format!("`{}` writes out of bounds: {a}+{at}", f.name),
                            span,
                        });
                    }
                    self.raw.allocs.get_mut(&a).expect("live_at checked").bytes[at as usize] =
                        Some(*b);
                }
                Ok(RtVal::Int(got))
            }
            "posix.close.v2" => {
                let RtVal::Int(fd) = args[0].clone() else {
                    unreachable!("checked: i32")
                };
                let Some(w) = self.world.as_mut() else {
                    return Err(Trap {
                        undef: false,
                        message: format!("`{}` called with no world in play", f.name),
                        span,
                    });
                };
                if fd < 0 || fd >= w.fds {
                    return Err(Trap {
                        undef: true,
                        message: format!("`{}`: descriptor {fd} was never handed out", f.name),
                        span,
                    });
                }
                // Closing twice is a *checker* error — the `OpenFile` is
                // affine — so the shim need not police it, and the fact
                // that it cannot is the point: the discipline is static.
                Ok(RtVal::Int(0))
            }
            other => Err(Trap {
                undef: false,
                message: format!(
                    "no test shim for audited extern `{}` (audit id `{other}`)",
                    f.name
                ),
                span,
            }),
        }
    }

    fn call(&mut self, f: &'a Fn, args: Vec<RtVal>) -> IResult<RtVal> {
        let mut frame = Frame {
            vars: HashMap::new(),
            entry_scalars: HashMap::new(),
            olds: HashMap::new(),
            self_ctx: None,
        };
        for (p, v) in f
            .params
            .iter()
            .filter(|p| !p.ty.is_resource() || has_resource_shadow(p.ty))
            .zip(args)
        {
            match (&v, p.ty) {
                (RtVal::Arr(a), Ty::Array(_, Mutability::Mut)) => {
                    frame
                        .olds
                        .insert(p.name.clone(), SpecVal::Arr(a.borrow().to_spec()));
                }
                // `&mut C`: the borrow shares storage with the caller, so
                // the bare name reads the current state and `old p` needs
                // the value it had at entry. `spec_of` copies.
                (obj @ RtVal::Obj { .. }, Ty::ClassRef(_, Mutability::Mut)) => {
                    if let Some(sv) = spec_of(obj) {
                        frame.olds.insert(p.name.clone(), sv);
                    }
                }
                (RtVal::Arr(_), _) => {}
                _ => {
                    frame.entry_scalars.insert(p.name.clone(), v.clone());
                }
            }
            frame.vars.insert(p.name.clone(), v);
        }
        // Erased parameters are absent from the runtime argument vector, but
        // their source-level places still exist inside the callee. A unit
        // placeholder lets an owned parameter be moved into a mutable local
        // (and then borrowed by an intrinsic) without pretending that an ABI
        // value was passed. Resource-map parameters keep their real sanitizer
        // shadow value from the loop above.
        for p in &f.params {
            if p.ty.is_resource() && !has_resource_shadow(p.ty) {
                frame.vars.insert(p.name.clone(), RtVal::Unit);
            }
        }

        for pre in &f.pres {
            self.check_clause(&frame, pre, None, &format!("pre of `{}`", f.name))?;
        }

        let flow = self.exec_block(&f.body, &mut frame)?;
        let result = match flow {
            Flow::Return(v) => v,
            Flow::Normal => RtVal::Unit,
        };

        for post in &f.posts {
            self.check_clause(
                &frame,
                post,
                Some(&result),
                &format!("post of `{}`", f.name),
            )?;
        }
        self.drop_owned_params(&f.params, &mut frame)?;
        Ok(result)
    }

    /// Owned parameters die with the frame, after the contract has been
    /// checked against them. A by-value class or array argument was handed
    /// over, so the callee is who destroys it — unless the body moved it on,
    /// in which case its place is already empty.
    fn drop_owned_params(&mut self, params: &[Param], frame: &mut Frame) -> IResult<()> {
        for p in params.iter().rev() {
            if matches!(p.ty, Ty::Class(_) | Ty::Array(_, Mutability::Owned)) {
                self.drop_place(&RtPlace::Local(p.name.clone()), frame)?;
            }
        }
        Ok(())
    }

    /// Contract-clause check with the right environment: entry values for
    /// by-value params, current contents for arrays, snapshots for `old`.
    fn check_clause(
        &mut self,
        frame: &Frame,
        clause: &crate::scan::Clause,
        result: Option<&RtVal>,
        what: &str,
    ) -> IResult<()> {
        let mut vars: HashMap<String, SpecVal> = HashMap::new();
        for (name, v) in &frame.vars {
            let val = if let Some(entry) = frame.entry_scalars.get(name) {
                entry
            } else {
                v
            };
            if let Some(sv) = spec_of(val) {
                vars.insert(name.clone(), sv);
            }
        }
        // A by-value parameter the body handed on is gone from its place,
        // but a contract speaks about the *value* it was given, and a value
        // outlives the transfer of authority (ADR 0024): the post of an
        // `init` that stores its argument in a field still says what the
        // field got.
        for (name, v) in &frame.entry_scalars {
            if !frame.vars.contains_key(name) {
                if let Some(sv) = spec_of(v) {
                    vars.insert(name.clone(), sv);
                }
            }
        }
        if let Some((class, fields)) = &frame.self_ctx {
            let obj = RtVal::Obj {
                class: *class,
                fields: fields.clone(),
            };
            if let Some(sv) = spec_of(&obj) {
                vars.insert("self".into(), sv);
            }
            for (k, v) in fields.borrow().iter() {
                if let Some(sv) = spec_of(v) {
                    vars.insert(k.clone(), sv);
                }
            }
        }
        if let Some(r) = result {
            if let Some(sv) = spec_of(r) {
                vars.insert("result".into(), sv);
            }
        }
        let env = SpecEnv {
            vars,
            olds: frame.olds.clone(),
            ghosts: self.ghosts,
        };
        match speceval::eval_clause(&clause.text, &env) {
            Ok(true) => Ok(()),
            Ok(false) => Err(Trap {
                undef: false,
                message: format!("{what} violated: {}", clause.text.replace('\n', " ")),
                span: clause.span,
            }),
            Err(um) => {
                self.skipped.push((clause.text.replace('\n', " "), um.0));
                Ok(())
            }
        }
    }

    /// Loop-clause check in the *current* frame (invariants speak about
    /// current values, including mutated by-value params).
    fn check_loop_clause(
        &mut self,
        frame: &Frame,
        clause: &crate::scan::Clause,
        what: &str,
    ) -> IResult<()> {
        let mut vars: HashMap<String, SpecVal> = HashMap::new();
        for (name, v) in &frame.vars {
            if let Some(sv) = spec_of(v) {
                vars.insert(name.clone(), sv);
            }
        }
        if let Some((class, fields)) = &frame.self_ctx {
            let obj = RtVal::Obj {
                class: *class,
                fields: fields.clone(),
            };
            if let Some(sv) = spec_of(&obj) {
                vars.insert("self".into(), sv);
            }
            for (k, v) in fields.borrow().iter() {
                if let Some(sv) = spec_of(v) {
                    vars.insert(k.clone(), sv);
                }
            }
        }
        let env = SpecEnv {
            vars,
            olds: frame.olds.clone(),
            ghosts: self.ghosts,
        };
        match speceval::eval_clause(&clause.text, &env) {
            Ok(true) => Ok(()),
            Ok(false) => Err(Trap {
                undef: false,
                message: format!("{what} violated: {}", clause.text.replace('\n', " ")),
                span: clause.span,
            }),
            Err(um) => {
                self.skipped.push((clause.text.replace('\n', " "), um.0));
                Ok(())
            }
        }
    }

    /// Run a block that owns its declarations: whatever it declares is
    /// destroyed at the closing brace, in reverse declaration order.
    fn exec_block(&mut self, stmts: &[Stmt], frame: &mut Frame) -> IResult<Flow> {
        let mut locals: Vec<String> = Vec::new();
        let out = self.exec_stmts(stmts, frame, &mut locals);
        // RAII: drop block-local values in reverse declaration order.
        // A local the block moved away is no longer in its place, which is
        // the whole reason a move removes it: the value belongs to whoever
        // took it, and this scope has nothing left to destroy.
        //
        // The drops run whether the block fell off its end or returned,
        // but not after a trap: a trapped program has stopped, and running
        // destructors past the failure would report the *second* thing that
        // went wrong.
        let out = out?;
        for name in locals.iter().rev() {
            self.drop_place(&RtPlace::Local(name.clone()), frame)?;
        }
        Ok(out)
    }

    /// Run a block whose declarations belong to the *enclosing* scope.
    ///
    /// `unsafe { ... }` and an exposure body are markers, not scopes: the
    /// checker keeps their locals in the function (ADR 0026), so a value
    /// declared inside one is still live at the closing brace and must not
    /// be destroyed there. The two sides have to agree about this, and the
    /// checker's answer is the language's.
    fn exec_open_block(
        &mut self,
        stmts: &[Stmt],
        frame: &mut Frame,
        locals: &mut Vec<String>,
    ) -> IResult<Flow> {
        self.exec_stmts(stmts, frame, locals)
    }

    fn exec_stmts(
        &mut self,
        stmts: &[Stmt],
        frame: &mut Frame,
        locals: &mut Vec<String>,
    ) -> IResult<Flow> {
        let mut out = Flow::Normal;
        for stmt in stmts {
            if let Stmt::VarDecl { name, .. } | Stmt::Decl { name, .. } = stmt {
                locals.push(name.clone());
            }
            match self.exec_stmt(stmt, frame, locals)? {
                Flow::Normal => {}
                ret => {
                    out = ret;
                    break;
                }
            }
        }
        Ok(out)
    }

    /// Remove a value from its source place, returning it.
    ///
    /// This is what makes a move a move at runtime: the source stops
    /// holding the value, so no later drop — of the scope, of the object,
    /// of the field — can reach it a second time. Every ownership transfer
    /// goes through here.
    fn take_place(&mut self, place: &RtPlace, frame: &mut Frame) -> Option<RtVal> {
        match place {
            RtPlace::Local(name) => frame.vars.remove(name.as_str()),
            RtPlace::SelfField(field) => {
                let (_, fields) = frame.self_ctx.clone()?;
                let v = fields.borrow_mut().remove(field.as_str());
                v
            }
        }
    }

    /// Take a value out of a place and destroy it: at scope exit, and
    /// wherever a place is overwritten. A place holding no value — moved
    /// away, or never initialized — has nothing to drop.
    fn drop_place(&mut self, place: &RtPlace, frame: &mut Frame) -> IResult<()> {
        let held = match place {
            RtPlace::Local(name) => frame.vars.get(name.as_str()).cloned(),
            RtPlace::SelfField(field) => frame
                .self_ctx
                .as_ref()
                .and_then(|(_, fields)| fields.borrow().get(field.as_str()).cloned()),
        };
        match held {
            Some(RtVal::Obj { class, fields }) => {
                // Out of its place *before* the destructor runs: a `deinit`
                // that reached the dying value through its own name would
                // see a value that no longer belongs to anyone.
                self.take_place(place, frame);
                self.drop_value(class, &fields, &place.name())
            }
            Some(RtVal::Arr(_)) => {
                // Arrays have no destructor, but an owned local still dies
                // at its lexical boundary. Removing the binding here is
                // observable through the backing Rc: branch and loop-body
                // storage must not remain live until the whole frame ends.
                // This is a drop, not a move; an array transferred through
                // `eval_moved` has already left its source place.
                self.take_place(place, frame);
                Ok(())
            }
            _ => Ok(()),
        }
    }

    /// The source place of an expression, if it names one. A call or a
    /// constructor is already a temporary: it has no source to clear.
    ///
    /// The two roots here are the two the program language can name as an
    /// ownership source, and they are the roots of the checker's `Place`.
    fn source_place(e: &Expr) -> Option<RtPlace> {
        match &e.kind {
            ExprKind::Var(n) => Some(RtPlace::Local(n.clone())),
            ExprKind::SelfField { field } => Some(RtPlace::SelfField(field.clone())),
            _ => None,
        }
    }

    /// Evaluate an expression in a position that *takes* the value, and
    /// clear its source place if it named one. Declarations, assignments,
    /// field assignments, arguments, and returns all transfer ownership,
    /// and they all transfer it the same way.
    ///
    /// Classes, owned arrays, and resource-map sanitizer shadows have runtime
    /// identity and leave a named source place when transferred. Boolean-array
    /// transport remains rejected by the checked owned-local slice; fresh
    /// literals and allocations have no source place to clear. Other resources
    /// are erased (ADR 0024), and scalars are copied.
    fn eval_moved(&mut self, e: &Expr, frame: &mut Frame) -> IResult<RtVal> {
        let v = self.eval(e, frame)?;
        if matches!(v, RtVal::Obj { .. } | RtVal::Arr(_) | RtVal::ResMap(_)) {
            if let Some(place) = Self::source_place(e) {
                self.take_place(&place, frame);
            }
        }
        Ok(v)
    }

    /// Evaluate an expression passed to an erased resource parameter for its
    /// runtime effects, then discard its proof-only value. A resource place
    /// itself has no runtime read to perform; constructors, transformations,
    /// and ordinary calls still execute, preserving source call-by-value
    /// order even though no value crosses the callee's runtime signature.
    fn eval_erased_resource_arg(&mut self, e: &Expr, frame: &mut Frame) -> IResult<()> {
        // The checked formal parameter or sealed primitive operand is the
        // authority for erasedness here. Resource variables and borrows may
        // have no cached `Expr::ty`: their checker arms return as soon as the
        // expected resource type has been validated. A present annotation
        // must still agree with the caller's contract.
        debug_assert!(e.ty.map_or(true, Ty::is_resource));
        match &e.kind {
            ExprKind::Var(_) | ExprKind::Borrow { .. } | ExprKind::SelfField { .. } => Ok(()),
            _ => {
                self.eval_moved(e, frame)?;
                Ok(())
            }
        }
    }

    /// Operand evaluation for a resource transformation whose result is
    /// erased. Nested resource expressions recurse through the same effect
    /// boundary; ordinary operands use their normal runtime evaluator.
    fn eval_erased_resource_operand(&mut self, e: &Expr, frame: &mut Frame) -> IResult<()> {
        if e.ty.is_some_and(Ty::is_resource) {
            self.eval_erased_resource_arg(e, frame)
        } else {
            self.eval_moved(e, frame)?;
            Ok(())
        }
    }

    /// Drop one class value: invariant, body, then the remaining fields in
    /// reverse declaration order. A field the body moved out is *not*
    /// dropped again — a moved field is somebody else's now, and dropping
    /// it twice is the failure the affine discipline exists to prevent.
    fn drop_value(
        &mut self,
        class: usize,
        fields: &Rc<RefCell<HashMap<String, RtVal>>>,
        what: &str,
    ) -> IResult<()> {
        let cd = self.classes[class].clone();
        self.check_invariants_at(&cd, fields, what)?;
        if let Some(body) = cd.deinit.clone() {
            let mut frame = Frame {
                vars: HashMap::new(),
                entry_scalars: HashMap::new(),
                olds: HashMap::new(),
                self_ctx: Some((class, fields.clone())),
            };
            self.exec_block(&body, &mut frame)?;
        }
        // The remaining fields, in reverse declaration order. A field the
        // body handed on is gone from the map, which is exactly the record
        // of "already somebody else's".
        for f in cd.fields.iter().rev() {
            let held = fields.borrow().get(f.name.as_str()).cloned();
            if let Some(RtVal::Obj {
                class: fc,
                fields: ff,
            }) = held
            {
                self.drop_value(fc, &ff, &format!("{what}.{}", f.name))?;
            }
        }
        Ok(())
    }

    fn check_invariants_at(
        &mut self,
        class: &ClassDecl,
        fields: &Rc<RefCell<HashMap<String, RtVal>>>,
        what: &str,
    ) -> IResult<()> {
        let mut vars: HashMap<String, SpecVal> = HashMap::new();
        let obj = RtVal::Obj {
            class: 0,
            fields: fields.clone(),
        };
        if let Some(sv) = spec_of(&obj) {
            vars.insert("self".into(), sv);
        }
        for (k, v) in fields.borrow().iter() {
            if let Some(sv) = spec_of(v) {
                vars.insert(k.clone(), sv);
            }
        }
        let env = SpecEnv {
            vars,
            olds: HashMap::new(),
            ghosts: self.ghosts,
        };
        for inv in &class.invariants {
            match speceval::eval_clause(&inv.text, &env) {
                Ok(true) => {}
                Ok(false) => {
                    return Err(Trap {
                        undef: false,
                        message: format!(
                            "class invariant of `{}` violated at `{what}`: {}",
                            class.name,
                            inv.text.replace('\n', " ")
                        ),
                        span: inv.span,
                    });
                }
                Err(um) => {
                    self.skipped.push((inv.text.replace('\n', " "), um.0));
                }
            }
        }
        Ok(())
    }

    fn exec_stmt(
        &mut self,
        stmt: &Stmt,
        frame: &mut Frame,
        locals: &mut Vec<String>,
    ) -> IResult<Flow> {
        self.burn(stmt_span(stmt))?;
        match stmt {
            Stmt::Decl { name, init, .. } => {
                if let Some(e) = init {
                    let v = self.eval_moved(e, frame)?;
                    frame.vars.insert(name.clone(), v);
                }
                Ok(Flow::Normal)
            }
            Stmt::Assign { name, value, .. } => {
                let v = self.eval_moved(value, frame)?;
                // Overwriting a place destroys what it held: the same drop
                // as at scope exit, destructor and fields included. The
                // new value goes in afterwards, so a self-assignment
                // cannot destroy what it is about to store.
                self.drop_place(&RtPlace::Local(name.clone()), frame)?;
                frame.vars.insert(name.clone(), v);
                Ok(Flow::Normal)
            }
            // `unsafe { ... }` is a marker: the block runs like any other.
            Stmt::Unsafe { body, .. } => self.exec_open_block(body, frame, locals),
            Stmt::StaticAlloc { size, ptr, res, .. } => {
                let RtVal::Int(n) = self.eval(size, frame)? else {
                    unreachable!("checked: u64 literal")
                };
                let alloc = self.raw.fresh(vec![None; n as usize]);
                frame.vars.insert(ptr.clone(), RtVal::Ptr(alloc, 0));
                frame.vars.insert(res.clone(), RtVal::Unit);
                Ok(Flow::Normal)
            }
            Stmt::SystemAlloc {
                size,
                ptr,
                res,
                release,
                ..
            } => {
                let RtVal::Int(n) = self.eval(size, frame)? else {
                    unreachable!("checked: u64 literal")
                };
                let alloc = self.raw.fresh(vec![None; n as usize]);
                frame.vars.insert(ptr.clone(), RtVal::Ptr(alloc, 0));
                frame.vars.insert(res.clone(), RtVal::Unit);
                frame.vars.insert(release.clone(), RtVal::Unit);
                Ok(Flow::Normal)
            }
            Stmt::SystemDealloc {
                ptr,
                res,
                release,
                kw_span,
            } => {
                let RtVal::Ptr(alloc, off) = self.eval(ptr, frame)? else {
                    unreachable!("checked: raw pointer")
                };
                self.eval_moved(res, frame)?;
                self.eval_moved(release, frame)?;
                let Some(al) = self.raw.allocs.get_mut(&alloc) else {
                    return Err(Trap {
                        undef: true,
                        message: format!("system_dealloc names absent allocation {alloc}"),
                        span: *kw_span,
                    });
                };
                if off != 0 || !al.live {
                    return Err(Trap {
                        undef: true,
                        message: format!("system_dealloc needs a live base pointer: {alloc}+{off}"),
                        span: *kw_span,
                    });
                }
                al.live = false;
                Ok(Flow::Normal)
            }
            // Exposure: copy the array's bytes into a fresh loan
            // allocation, run the body, copy the final bytes back, and
            // kill the allocation. Modelling it as a real copy is what
            // makes a leaked pointer observable at runtime rather than
            // silently fine (ADR 0026).
            Stmt::Expose {
                kw_span,
                array,
                mutable,
                ptr,
                res,
                body,
                ..
            } => {
                let RtVal::Arr(a) = frame.vars[array.as_str()].clone() else {
                    unreachable!("checked: u8 array")
                };
                let bytes: Vec<Option<i128>> = a
                    .borrow()
                    .int_values()
                    .expect("interpreter guard rejects Boolean exposure")
                    .iter()
                    .copied()
                    .map(Some)
                    .collect();
                let n = bytes.len();
                let alloc = self.raw.fresh(bytes);
                frame.vars.insert(ptr.clone(), RtVal::Ptr(alloc, 0));
                // The resource has no runtime representation (ADR 0024);
                // the binding exists so the body's names resolve.
                frame.vars.insert(res.clone(), RtVal::Unit);
                // An exposure body is a scope on both sides: the loan ends
                // at the closing brace, so anything the body declared ends
                // with it (ADR 0030). `unsafe { ... }` is the other case —
                // vocabulary, no lifetime, no scope.
                let flow = self.exec_block(body, frame)?;
                let final_bytes = self
                    .raw
                    .allocs
                    .get(&alloc)
                    .map(|al| al.bytes.clone())
                    .expect("the loan allocation is ours");
                if *mutable {
                    for (i, b) in final_bytes.iter().enumerate().take(n) {
                        match b {
                            Some(v) => a.borrow_mut().set_int(i, *v),
                            None => {
                                return Err(Trap {
                                    undef: false,
                                    message: format!(
                                        "exposure of `{array}` ends with byte {i} \
                                         uninitialized"
                                    ),
                                    span: *kw_span,
                                });
                            }
                        }
                    }
                }
                if let Some(al) = self.raw.allocs.get_mut(&alloc) {
                    al.live = false;
                }
                frame.vars.remove(ptr.as_str());
                frame.vars.remove(res.as_str());
                Ok(flow)
            }
            Stmt::ExprStmt(e) => {
                // A discarded class value is a temporary that nothing
                // names, and it dies at the end of the statement that made
                // it. It is the one owned value with no place, so it is
                // also the one drop that cannot go through `drop_place`.
                let v = self.eval(e, frame)?;
                if let RtVal::Obj { class, fields } = v {
                    self.drop_value(class, &fields, "temporary")?;
                }
                Ok(Flow::Normal)
            }
            Stmt::Assert(clause) => {
                self.check_clause(frame, clause, None, "inline assert")?;
                Ok(Flow::Normal)
            }
            Stmt::VarDecl { name, init, .. } => {
                let v = self.eval_moved(init, frame)?;
                frame.vars.insert(name.clone(), v);
                Ok(Flow::Normal)
            }
            Stmt::FieldAssign { field, value, .. } => {
                let v = self.eval_moved(value, frame)?;
                // A field is a place like any other: overwriting it
                // destroys what it held. An `init` is the exception —
                // there is nothing there yet — and `drop_place` on an
                // uninitialized field finds nothing to do.
                self.drop_place(&RtPlace::SelfField(field.clone()), frame)?;
                let (_, fields) = frame.self_ctx.clone().expect("checked: member ctx");
                fields.borrow_mut().insert(field.clone(), v);
                Ok(Flow::Normal)
            }
            Stmt::FieldStore {
                field,
                field_span,
                index,
                value,
            } => {
                let idx = self.eval_int(index, frame)?;
                let val = self.eval(value, frame)?;
                let (_, fields) = frame.self_ctx.clone().expect("checked: member ctx");
                let arr = match fields.borrow().get(field.as_str()) {
                    Some(RtVal::Arr(a)) => a.clone(),
                    _ => unreachable!("checked: array field initialized"),
                };
                let len = arr.borrow().len() as i128;
                if idx < 0 || idx >= len {
                    return Err(Trap {
                        undef: false,
                        message: format!("store index out of bounds: index {idx}, length {len}"),
                        span: *field_span,
                    });
                }
                arr.borrow_mut().set(idx as usize, val);
                Ok(Flow::Normal)
            }
            Stmt::Store {
                array,
                array_span,
                index,
                value,
            } => {
                let idx = self.eval_int(index, frame)?;
                let val = self.eval(value, frame)?;
                let RtVal::Arr(a) = frame.vars[array.as_str()].clone() else {
                    unreachable!()
                };
                let len = a.borrow().len() as i128;
                if idx < 0 || idx >= len {
                    return Err(Trap {
                        undef: false,
                        message: format!("store index out of bounds: index {idx}, length {len}"),
                        span: *array_span,
                    });
                }
                a.borrow_mut().set(idx as usize, val);
                Ok(Flow::Normal)
            }
            Stmt::Return { value, .. } => {
                // Returning a place is a move: the value leaves with the
                // caller, so the scopes unwinding behind it must not find
                // it still sitting in its source and destroy it.
                let v = match value {
                    Some(e) => self.eval_moved(e, frame)?,
                    None => RtVal::Unit,
                };
                Ok(Flow::Return(v))
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                if self.eval_bool(cond, frame)? {
                    self.exec_block(then_block, frame)
                } else if let Some(eb) = else_block {
                    self.exec_block(eb, frame)
                } else {
                    Ok(Flow::Normal)
                }
            }
            Stmt::While {
                cond,
                invariants,
                variant,
                kw_span,
                body,
            } => {
                loop {
                    self.burn(*kw_span)?;
                    for inv in invariants {
                        self.check_loop_clause(frame, inv, "loop invariant")?;
                    }

                    // VCgen's measure is the loop-head value, before an
                    // effectful condition runs. Save it now, but report an
                    // unmonitorable measure only if the condition is true:
                    // the verifier owes descent only on a body path.
                    let head_variant = variant.as_ref().map(|v| (v, self.variant_value(frame, v)));
                    if !self.eval_bool(cond, frame)? {
                        break;
                    }

                    let monitored_head = match head_variant {
                        Some((v, Ok(v0))) => {
                            if v0 < 0 {
                                return Err(Trap {
                                    undef: false,
                                    message: format!("loop variant is negative ({v0}): {}", v.text),
                                    span: v.span,
                                });
                            }
                            Some((v, v0))
                        }
                        Some((v, Err(um))) => {
                            self.skipped.push((v.text.replace('\n', " "), um.0));
                            None
                        }
                        None => None,
                    };

                    match self.exec_block(body, frame)? {
                        Flow::Normal => {}
                        ret => return Ok(ret),
                    }

                    // Check the same transition as the preservation VC:
                    // head measure v0, then condition + body, then v1. Doing
                    // this immediately also covers the final body iteration,
                    // whose following condition may be false.
                    if let Some((v, v0)) = monitored_head {
                        match self.variant_value(frame, v) {
                            Ok(v1) if v1 >= v0 => {
                                return Err(Trap {
                                    undef: false,
                                    message: format!(
                                        "loop variant did not decrease ({v0} → {v1}): {}",
                                        v.text
                                    ),
                                    span: v.span,
                                });
                            }
                            Ok(_) => {}
                            Err(um) => {
                                self.skipped.push((v.text.replace('\n', " "), um.0));
                            }
                        }
                    }
                }
                Ok(Flow::Normal)
            }
        }
    }

    /// Evaluate a variant measure numerically by evaluating the program
    /// expression through the spec evaluator (variants are Int-valued).
    fn variant_value(
        &self,
        frame: &Frame,
        clause: &crate::scan::Clause,
    ) -> Result<i128, speceval::Unmonitorable> {
        let mut vars: HashMap<String, SpecVal> = HashMap::new();
        for (name, v) in &frame.vars {
            if let Some(sv) = spec_of(v) {
                vars.insert(name.clone(), sv);
            }
        }
        let env = SpecEnv {
            vars,
            olds: frame.olds.clone(),
            ghosts: self.ghosts,
        };
        speceval::eval_int_expr(&clause.text, &env)
    }

    fn construct(
        &mut self,
        ci: usize,
        init_name: &str,
        args: Vec<RtVal>,
        span: crate::span::Span,
    ) -> IResult<RtVal> {
        self.burn(span)?;
        let class = self.classes[ci].clone();
        let ifn = class
            .inits
            .iter()
            .find(|i| i.name == init_name)
            .expect("checked: init exists")
            .clone();
        let fields = Rc::new(RefCell::new(HashMap::new()));
        let mut frame = Frame {
            vars: HashMap::new(),
            entry_scalars: HashMap::new(),
            olds: HashMap::new(),
            self_ctx: Some((ci, fields.clone())),
        };
        for (p, v) in ifn.params.iter().zip(args) {
            match (&v, p.ty) {
                (obj @ RtVal::Obj { .. }, Ty::ClassRef(_, Mutability::Mut)) => {
                    if let Some(sv) = spec_of(obj) {
                        frame.olds.insert(p.name.clone(), sv);
                    }
                }
                _ => {
                    frame.entry_scalars.insert(p.name.clone(), v.clone());
                }
            }
            frame.vars.insert(p.name.clone(), v);
        }
        for pre in &ifn.pres {
            self.check_clause(
                &frame,
                pre,
                None,
                &format!("pre of `{}::{}`", class.name, ifn.name),
            )?;
        }
        self.exec_block(&ifn.body, &mut frame)?;
        for post in &ifn.posts {
            self.check_clause(
                &frame,
                post,
                None,
                &format!("post of `{}::{}`", class.name, ifn.name),
            )?;
        }
        self.check_invariants_at(
            &class,
            &fields,
            &format!("{}::{} exit", class.name, ifn.name),
        )?;
        self.drop_owned_params(&ifn.params, &mut frame)?;
        Ok(RtVal::Obj { class: ci, fields })
    }

    fn invoke(
        &mut self,
        ci: usize,
        method: &str,
        fields: Rc<RefCell<HashMap<String, RtVal>>>,
        args: Vec<RtVal>,
    ) -> IResult<RtVal> {
        let class = self.classes[ci].clone();
        let m = class
            .methods
            .iter()
            .find(|m| m.f.name == method)
            .expect("checked: method exists")
            .clone();
        let mut frame = Frame {
            vars: HashMap::new(),
            entry_scalars: HashMap::new(),
            olds: HashMap::new(),
            self_ctx: Some((ci, fields.clone())),
        };
        // Entry snapshot for `old self` (and post-checking of by-value
        // params).
        let entry_obj = RtVal::Obj {
            class: ci,
            fields: Rc::new(RefCell::new(
                fields
                    .borrow()
                    .iter()
                    .map(|(k, v)| (k.clone(), deep_copy(v)))
                    .collect(),
            )),
        };
        if let Some(sv) = spec_of(&entry_obj) {
            frame.olds.insert("self".into(), sv);
        }
        for (p, v) in m.f.params.iter().zip(args) {
            match (&v, p.ty) {
                // `&mut C`: the borrow shares storage with the caller, so
                // `old p` needs the value it had at entry. `spec_of` copies.
                (obj @ RtVal::Obj { .. }, Ty::ClassRef(_, Mutability::Mut)) => {
                    if let Some(sv) = spec_of(obj) {
                        frame.olds.insert(p.name.clone(), sv);
                    }
                }
                _ => {
                    frame.entry_scalars.insert(p.name.clone(), v.clone());
                }
            }
            frame.vars.insert(p.name.clone(), v);
        }
        for pre in &m.f.pres {
            self.check_clause(
                &frame,
                pre,
                None,
                &format!("pre of `{}::{method}`", class.name),
            )?;
        }
        let flow = self.exec_block(&m.f.body, &mut frame)?;
        let result = match flow {
            Flow::Return(v) => v,
            Flow::Normal => RtVal::Unit,
        };
        if m.self_kind == SelfKind::Mut {
            self.check_invariants_at(&class, &fields, &format!("{}::{method} exit", class.name))?;
        }
        for post in &m.f.posts {
            self.check_clause(
                &frame,
                post,
                Some(&result),
                &format!("post of `{}::{method}`", class.name),
            )?;
        }
        self.drop_owned_params(&m.f.params, &mut frame)?;
        Ok(result)
    }

    fn eval_int(&mut self, e: &Expr, frame: &mut Frame) -> IResult<i128> {
        match self.eval(e, frame)? {
            RtVal::Int(n) => Ok(n),
            _ => unreachable!("checked: int expression"),
        }
    }

    fn eval_bool(&mut self, e: &Expr, frame: &mut Frame) -> IResult<bool> {
        match self.eval(e, frame)? {
            RtVal::Bool(b) => Ok(b),
            _ => unreachable!("checked: bool expression"),
        }
    }

    fn eval(&mut self, e: &Expr, frame: &mut Frame) -> IResult<RtVal> {
        self.burn(e.span)?;
        match &e.kind {
            ExprKind::IntLit(n) => Ok(RtVal::Int(*n)),
            ExprKind::BoolLit(b) => Ok(RtVal::Bool(*b)),
            ExprKind::Var(name) => Ok(frame.vars[name.as_str()].clone()),
            // Resource transformations redistribute authority, which is
            // a static notion: at runtime there is nothing to move and
            // nothing to return (ADR 0024). `posix_world` is the
            // exception: the *script* it selects is real runtime state,
            // and a test controlling it is what "scripted world" means.
            ExprKind::ResOp { op, args, .. } => {
                match op {
                    ResOp::TestWorld => {
                        let script = self.eval_int(&args[0], frame)?;
                        self.world = Some(PosixWorld::scripted(script));
                    }
                    ResOp::TestUart => {
                        if self.uart.is_some() {
                            return Err(Trap {
                                undef: true,
                                message: "test_uart: a UART profile is already selected".into(),
                                span: e.span,
                            });
                        }
                        let script = self.eval_int(&args[0], frame)?;
                        self.uart = Some(ScriptedUart::new(script));
                    }
                    // Adoption spends the world's claim on a descriptor.
                    // The VC is what makes a second adoption unreachable;
                    // this is the monitor saying so independently, the
                    // same two layers the raw operations have.
                    ResOp::OpenFileOf => {
                        self.eval_erased_resource_arg(&args[0], frame)?;
                        let fd = self.eval_int(&args[1], frame)?;
                        if let Some(w) = &mut self.world {
                            if fd < 0 || fd >= w.fds {
                                return Err(Trap {
                                    undef: false,
                                    message: format!(
                                        "open_file: descriptor {fd} is not open in this world"
                                    ),
                                    span: e.span,
                                });
                            }
                            if !w.claimed.insert(fd) {
                                return Err(Trap {
                                    undef: false,
                                    message: format!(
                                        "open_file: descriptor {fd}'s authority has already \
                                         been handed out"
                                    ),
                                    span: e.span,
                                });
                            }
                        }
                    }
                    ResOp::ResourceMapEmpty => {
                        return Ok(RtVal::ResMap(Rc::new(RefCell::new(HashSet::new()))));
                    }
                    ResOp::ResourceMapTake => {
                        let RtVal::ResMap(entries) = self.eval(&args[0], frame)? else {
                            unreachable!("checked: resource map borrow")
                        };
                        let key = self.eval_int(&args[1], frame)?;
                        if !entries.borrow_mut().remove(&key) {
                            return Err(Trap {
                                undef: false,
                                message: format!("resource_map_take: key {key} is absent"),
                                span: e.span,
                            });
                        }
                    }
                    ResOp::ResourceMapPut => {
                        let RtVal::ResMap(entries) = self.eval(&args[0], frame)? else {
                            unreachable!("checked: resource map borrow")
                        };
                        let key = self.eval_int(&args[1], frame)?;
                        self.eval_erased_resource_arg(&args[2], frame)?;
                        // The consumed cell is ordinary erased authority; only the
                        // aggregate's key set has sanitizer shadow state.
                        if !entries.borrow_mut().insert(key) {
                            return Err(Trap {
                                undef: false,
                                message: format!("resource_map_put: key {key} is already occupied"),
                                span: e.span,
                            });
                        }
                    }
                    // The remaining transformations are proof-state
                    // transitions. Their result is erased, but evaluating
                    // their operands may run ordinary calls or a nested
                    // profile/resource constructor, so visit every operand
                    // in source order before discarding the result.
                    _ => {
                        for arg in args {
                            self.eval_erased_resource_operand(arg, frame)?;
                        }
                    }
                }
                Ok(RtVal::Unit)
            }
            ExprKind::DeviceOp { op, args, .. } => match op {
                DeviceOp::UartStatus => {
                    let Some(uart) = &mut self.uart else {
                        return Err(Trap {
                            undef: true,
                            message: "uart_status: no UART profile selected".into(),
                            span: e.span,
                        });
                    };
                    Ok(RtVal::Int(uart.status()))
                }
                DeviceOp::UartWrite => {
                    if self.uart.is_none() {
                        return Err(Trap {
                            undef: true,
                            message: "uart_write: no UART profile selected".into(),
                            span: e.span,
                        });
                    }
                    let byte = self.eval_int(&args[0], frame)?;
                    let uart = self.uart.as_mut().expect("checked above");
                    if !uart.ready {
                        return Err(Trap {
                            undef: true,
                            message: "uart_write: transmitter is not ready".into(),
                            span: e.span,
                        });
                    }
                    uart.write(byte);
                    Ok(RtVal::Unit)
                }
            },
            // The raw operations. Each classification here must match the
            // machine's: a trap is a trap, and everything the SVM calls
            // `undef` is a trap with a precise message — the reference
            // interpreter may say *which* rule was broken while agreeing
            // on the outcome class (ADR 0025).
            ExprKind::RawOp { op, args, .. } => {
                let vals: Vec<RtVal> = {
                    let mut vs = Vec::with_capacity(args.len());
                    for a in args {
                        vs.push(self.eval(a, frame)?);
                    }
                    vs
                };
                let ptr_at = |i: usize| match vals[i] {
                    RtVal::Ptr(a, o) => (a, o),
                    _ => unreachable!("checked: raw<u8> argument"),
                };
                let int_at = |i: usize| match vals[i] {
                    RtVal::Int(n) => n,
                    _ => unreachable!("checked: integer argument"),
                };
                // Every way a raw operation can fail is the machine's
                // `undef`: the static semantics is what makes these
                // unreachable, so there is no defined runtime behavior to
                // trap into (ADR 0025).
                let bad = |msg: String| Trap {
                    undef: true,
                    message: msg,
                    span: e.span,
                };
                match op {
                    RawOp::Offset => {
                        let (a, o) = ptr_at(0);
                        Ok(RtVal::Ptr(a, o + int_at(1)))
                    }
                    RawOp::CastRecord(_) => {
                        let (a, o) = ptr_at(0);
                        Ok(RtVal::Ptr(a, o))
                    }
                    RawOp::PointerOffsetRecord(_) => {
                        let (_, o) = ptr_at(0);
                        Ok(RtVal::Int(o))
                    }
                    RawOp::Load8 => {
                        let (a, o) = ptr_at(0);
                        match self.raw.live_at(a, o).map(|al| al.bytes[o as usize]) {
                            Some(Some(b)) => Ok(RtVal::Int(b)),
                            Some(None) => Err(bad(format!(
                                "raw_load8 reads uninitialized byte {o} of allocation {a}"
                            ))),
                            None => Err(bad(format!(
                                "raw_load8 out of bounds or after free: {a}+{o}"
                            ))),
                        }
                    }
                    RawOp::Store8 => {
                        let (a, o) = ptr_at(0);
                        let w = int_at(1);
                        if self.raw.live_at(a, o).is_none() {
                            return Err(bad(format!(
                                "raw_store8 out of bounds or after free: {a}+{o}"
                            )));
                        }
                        self.raw.allocs.get_mut(&a).expect("live_at checked").bytes[o as usize] =
                            Some(w);
                        Ok(RtVal::Unit)
                    }
                    RawOp::Copy => {
                        let (sa, so) = ptr_at(0);
                        let (da, do_) = ptr_at(1);
                        let n = int_at(2);
                        for i in 0..n {
                            let b = match self
                                .raw
                                .live_at(sa, so + i)
                                .map(|al| al.bytes[(so + i) as usize])
                            {
                                Some(Some(b)) => b,
                                Some(None) => {
                                    return Err(bad(format!(
                                        "raw_copy_nonoverlapping reads uninitialized byte \
                                         {} of allocation {sa}",
                                        so + i
                                    )));
                                }
                                None => {
                                    return Err(bad(format!(
                                        "raw_copy_nonoverlapping source out of bounds: \
                                         {sa}+{}",
                                        so + i
                                    )));
                                }
                            };
                            if self.raw.live_at(da, do_ + i).is_none() {
                                return Err(bad(format!(
                                    "raw_copy_nonoverlapping destination out of bounds: \
                                     {da}+{}",
                                    do_ + i
                                )));
                            }
                            self.raw.allocs.get_mut(&da).expect("live_at checked").bytes
                                [(do_ + i) as usize] = Some(b);
                        }
                        Ok(RtVal::Unit)
                    }
                    RawOp::IntoCellU64 => {
                        let (a, o) = ptr_at(0);
                        let layout = IntTy::U64.layout();
                        if o % layout.align != 0 {
                            return Err(bad(format!(
                                "raw_into_cell_u64 needs 8-byte alignment: {a}+{o}"
                            )));
                        }
                        for i in 0..layout.size {
                            if self.raw.live_at(a, o + i).is_none() {
                                return Err(bad(format!(
                                    "raw_into_cell_u64 needs eight raw bytes at {a}+{o}"
                                )));
                            }
                        }
                        self.raw
                            .allocs
                            .get_mut(&a)
                            .expect("live_at checked")
                            .cells_u64
                            .insert(o, None);
                        Ok(RtVal::Unit)
                    }
                    RawOp::FromCellU64 => {
                        let (a, o) = ptr_at(0);
                        let layout = IntTy::U64.layout();
                        let al = self.raw.allocs.get_mut(&a).ok_or_else(|| {
                            bad(format!("raw_from_cell_u64 names absent allocation {a}"))
                        })?;
                        if !al.live {
                            return Err(bad(format!(
                                "raw_from_cell_u64 names dead allocation {a}"
                            )));
                        }
                        match al.cells_u64.get(&o) {
                            Some(None) => {
                                al.cells_u64.remove(&o);
                                for i in 0..layout.size {
                                    al.bytes[(o + i) as usize] = Some(0);
                                }
                                Ok(RtVal::Unit)
                            }
                            _ => Err(bad(format!(
                                "raw_from_cell_u64 needs an uninitialized cell at {a}+{o}"
                            ))),
                        }
                    }
                    RawOp::IntoFreeHeader => {
                        let (a, o) = ptr_at(0);
                        let layout = IntTy::U64.layout();
                        let header_len = 2 * layout.size;
                        if o % layout.align != 0 {
                            return Err(bad(format!(
                                "raw_into_free_header needs 8-byte alignment: {a}+{o}"
                            )));
                        }
                        for i in 0..header_len {
                            if self.raw.live_at(a, o + i).is_none() {
                                return Err(bad(format!(
                                    "raw_into_free_header needs sixteen raw bytes at {a}+{o}"
                                )));
                            }
                        }
                        let al = self.raw.allocs.get_mut(&a).expect("live_at checked");
                        al.cells_u64.insert(o, None);
                        al.cells_u64.insert(o + layout.size, None);
                        Ok(RtVal::Unit)
                    }
                    RawOp::FromFreeHeader => {
                        let (a, o) = ptr_at(0);
                        let layout = IntTy::U64.layout();
                        let al = self.raw.allocs.get_mut(&a).ok_or_else(|| {
                            bad(format!("raw_from_free_header names absent allocation {a}"))
                        })?;
                        if !al.live {
                            return Err(bad(format!(
                                "raw_from_free_header names dead allocation {a}"
                            )));
                        }
                        if !matches!(al.cells_u64.get(&o), Some(None))
                            || !matches!(al.cells_u64.get(&(o + layout.size)), Some(None))
                        {
                            return Err(bad(format!(
                                "raw_from_free_header needs two uninitialized cells at {a}+{o}"
                            )));
                        }
                        al.cells_u64.remove(&o);
                        al.cells_u64.remove(&(o + layout.size));
                        for i in 0..(2 * layout.size) {
                            al.bytes[(o + i) as usize] = Some(0);
                        }
                        Ok(RtVal::Unit)
                    }
                    RawOp::HeaderInit => {
                        let (a, o) = ptr_at(0);
                        let size = int_at(1);
                        let next = int_at(2);
                        let layout = IntTy::U64.layout();
                        let al = self.raw.allocs.get_mut(&a).ok_or_else(|| {
                            bad(format!("raw_header_init names absent allocation {a}"))
                        })?;
                        if !al.live {
                            return Err(bad(format!("raw_header_init names dead allocation {a}")));
                        }
                        if !matches!(al.cells_u64.get(&o), Some(None))
                            || !matches!(al.cells_u64.get(&(o + layout.size)), Some(None))
                        {
                            return Err(bad(format!(
                                "raw_header_init needs two uninitialized cells at {a}+{o}"
                            )));
                        }
                        al.cells_u64.insert(o, Some(size));
                        al.cells_u64.insert(o + layout.size, Some(next));
                        Ok(RtVal::Unit)
                    }
                    RawOp::HeaderSize | RawOp::HeaderNext => {
                        let (a, o) = ptr_at(0);
                        let offset = if matches!(op, RawOp::HeaderSize) {
                            o
                        } else {
                            o + IntTy::U64.layout().size
                        };
                        match self
                            .raw
                            .allocs
                            .get(&a)
                            .filter(|al| al.live)
                            .and_then(|al| al.cells_u64.get(&offset))
                        {
                            Some(Some(w)) => Ok(RtVal::Int(*w)),
                            _ => Err(bad(format!(
                                "{} needs an initialized field at {a}+{offset}",
                                op.name()
                            ))),
                        }
                    }
                    RawOp::HeaderClear => {
                        let (a, o) = ptr_at(0);
                        let layout = IntTy::U64.layout();
                        let al = self.raw.allocs.get_mut(&a).ok_or_else(|| {
                            bad(format!("raw_header_clear names absent allocation {a}"))
                        })?;
                        if !al.live {
                            return Err(bad(format!("raw_header_clear names dead allocation {a}")));
                        }
                        if !matches!(al.cells_u64.get(&o), Some(Some(_)))
                            || !matches!(al.cells_u64.get(&(o + layout.size)), Some(Some(_)))
                        {
                            return Err(bad(format!(
                                "raw_header_clear needs two initialized cells at {a}+{o}"
                            )));
                        }
                        al.cells_u64.insert(o, None);
                        al.cells_u64.insert(o + layout.size, None);
                        Ok(RtVal::Unit)
                    }
                    RawOp::CellInitU64 => {
                        let (a, o) = ptr_at(0);
                        let w = int_at(1);
                        let al = self.raw.allocs.get_mut(&a).ok_or_else(|| {
                            bad(format!("raw_cell_init_u64 names absent allocation {a}"))
                        })?;
                        if !al.live {
                            return Err(bad(format!(
                                "raw_cell_init_u64 names dead allocation {a}"
                            )));
                        }
                        match al.cells_u64.get_mut(&o) {
                            Some(state @ None) => {
                                *state = Some(w);
                                Ok(RtVal::Unit)
                            }
                            _ => Err(bad(format!(
                                "raw_cell_init_u64 needs an uninitialized cell at {a}+{o}"
                            ))),
                        }
                    }
                    RawOp::CellReadU64 => {
                        let (a, o) = ptr_at(0);
                        match self
                            .raw
                            .allocs
                            .get(&a)
                            .filter(|al| al.live)
                            .and_then(|al| al.cells_u64.get(&o))
                        {
                            Some(Some(w)) => Ok(RtVal::Int(*w)),
                            _ => Err(bad(format!(
                                "raw_cell_read_u64 needs an initialized cell at {a}+{o}"
                            ))),
                        }
                    }
                    RawOp::CellTakeU64 => {
                        let (a, o) = ptr_at(0);
                        let al = self.raw.allocs.get_mut(&a).ok_or_else(|| {
                            bad(format!("raw_cell_take_u64 names absent allocation {a}"))
                        })?;
                        if !al.live {
                            return Err(bad(format!(
                                "raw_cell_take_u64 names dead allocation {a}"
                            )));
                        }
                        match al.cells_u64.get_mut(&o) {
                            Some(state @ Some(_)) => {
                                let w = state.take().expect("matched initialized cell");
                                Ok(RtVal::Int(w))
                            }
                            _ => Err(bad(format!(
                                "raw_cell_take_u64 needs an initialized cell at {a}+{o}"
                            ))),
                        }
                    }
                    RawOp::CellDropU64 => {
                        let (a, o) = ptr_at(0);
                        let al = self.raw.allocs.get_mut(&a).ok_or_else(|| {
                            bad(format!("raw_cell_drop_u64 names absent allocation {a}"))
                        })?;
                        if !al.live {
                            return Err(bad(format!(
                                "raw_cell_drop_u64 names dead allocation {a}"
                            )));
                        }
                        match al.cells_u64.get_mut(&o) {
                            Some(state @ Some(_)) => {
                                *state = None;
                                Ok(RtVal::Unit)
                            }
                            _ => Err(bad(format!(
                                "raw_cell_drop_u64 needs an initialized cell at {a}+{o}"
                            ))),
                        }
                    }
                    RawOp::IntoCellRecord(ri) => {
                        let (a, o) = ptr_at(0);
                        let layout = self.records[*ri].layout;
                        if o % layout.align != 0 {
                            return Err(bad(format!(
                                "raw_into_cell<{}> needs {}-byte alignment: {a}+{o}",
                                self.records[*ri].name, layout.align
                            )));
                        }
                        for i in 0..layout.size {
                            if self.raw.live_at(a, o + i).is_none() {
                                return Err(bad(format!(
                                    "raw_into_cell<{}> needs {} raw bytes at {a}+{o}",
                                    self.records[*ri].name, layout.size
                                )));
                            }
                        }
                        let al = self.raw.allocs.get_mut(&a).expect("live_at checked");
                        al.cells_record.insert(
                            o,
                            RecordCell {
                                record: *ri,
                                layout,
                                value: None,
                            },
                        );
                        Ok(RtVal::Unit)
                    }
                    RawOp::FromCellRecord(ri) => {
                        let (a, o) = ptr_at(0);
                        let al = self.raw.allocs.get_mut(&a).ok_or_else(|| {
                            bad(format!("raw_from_cell names absent allocation {a}"))
                        })?;
                        if !al.live {
                            return Err(bad(format!("raw_from_cell names dead allocation {a}")));
                        }
                        let Some(cell) = al.cells_record.get(&o) else {
                            return Err(bad(format!(
                                "raw_from_cell<{}> needs a typed cell at {a}+{o}",
                                self.records[*ri].name
                            )));
                        };
                        if cell.record != *ri || cell.value.is_some() {
                            return Err(bad(format!(
                                "raw_from_cell<{}> needs a matching uninitialized cell at {a}+{o}",
                                self.records[*ri].name
                            )));
                        }
                        let layout = cell.layout;
                        al.cells_record.remove(&o);
                        for i in 0..layout.size {
                            al.bytes[(o + i) as usize] = Some(0);
                        }
                        Ok(RtVal::Unit)
                    }
                    RawOp::CellInitRecord(ri) => {
                        let (a, o) = ptr_at(0);
                        let value = vals[1].clone();
                        let al = self.raw.allocs.get_mut(&a).ok_or_else(|| {
                            bad(format!("raw_cell_init names absent allocation {a}"))
                        })?;
                        let Some(cell) = al.cells_record.get_mut(&o) else {
                            return Err(bad(format!(
                                "raw_cell_init<{}> needs a typed cell at {a}+{o}",
                                self.records[*ri].name
                            )));
                        };
                        if !al.live || cell.record != *ri || cell.value.is_some() {
                            return Err(bad(format!(
                                "raw_cell_init<{}> needs a matching uninitialized cell at {a}+{o}",
                                self.records[*ri].name
                            )));
                        }
                        cell.value = Some(value);
                        Ok(RtVal::Unit)
                    }
                    RawOp::CellReadRecord(ri) => {
                        let (a, o) = ptr_at(0);
                        let value = self
                            .raw
                            .allocs
                            .get(&a)
                            .filter(|al| al.live)
                            .and_then(|al| al.cells_record.get(&o))
                            .filter(|cell| cell.record == *ri)
                            .and_then(|cell| cell.value.as_ref())
                            .cloned();
                        value.ok_or_else(|| {
                            bad(format!(
                                "raw_cell_read<{}> needs a matching initialized cell at {a}+{o}",
                                self.records[*ri].name
                            ))
                        })
                    }
                    RawOp::CellTakeRecord(ri) => {
                        let (a, o) = ptr_at(0);
                        let al = self.raw.allocs.get_mut(&a).ok_or_else(|| {
                            bad(format!("raw_cell_take names absent allocation {a}"))
                        })?;
                        let Some(cell) = al.cells_record.get_mut(&o) else {
                            return Err(bad(format!(
                                "raw_cell_take<{}> needs a typed cell at {a}+{o}",
                                self.records[*ri].name
                            )));
                        };
                        if !al.live || cell.record != *ri {
                            return Err(bad(format!(
                                "raw_cell_take<{}> needs a matching initialized cell at {a}+{o}",
                                self.records[*ri].name
                            )));
                        }
                        cell.value.take().ok_or_else(|| {
                            bad(format!(
                                "raw_cell_take<{}> needs an initialized cell at {a}+{o}",
                                self.records[*ri].name
                            ))
                        })
                    }
                    RawOp::CellDropRecord(ri) => {
                        let (a, o) = ptr_at(0);
                        let al = self.raw.allocs.get_mut(&a).ok_or_else(|| {
                            bad(format!("raw_cell_drop names absent allocation {a}"))
                        })?;
                        let Some(cell) = al.cells_record.get_mut(&o) else {
                            return Err(bad(format!(
                                "raw_cell_drop<{}> needs a typed cell at {a}+{o}",
                                self.records[*ri].name
                            )));
                        };
                        if !al.live || cell.record != *ri || cell.value.is_none() {
                            return Err(bad(format!(
                                "raw_cell_drop<{}> needs a matching initialized cell at {a}+{o}",
                                self.records[*ri].name
                            )));
                        }
                        cell.value = None;
                        Ok(RtVal::Unit)
                    }
                }
            }

            ExprKind::Len { array } => {
                let RtVal::Arr(a) = &frame.vars[array.as_str()] else {
                    unreachable!()
                };
                Ok(RtVal::Int(a.borrow().len() as i128))
            }
            ExprKind::Index { array, index, .. } => {
                let idx = self.eval_int(index, frame)?;
                let RtVal::Arr(a) = &frame.vars[array.as_str()] else {
                    unreachable!()
                };
                let arr = a.borrow();
                if idx < 0 || idx >= arr.len() as i128 {
                    return Err(Trap {
                        undef: false,
                        message: format!("index out of bounds: index {idx}, length {}", arr.len()),
                        span: e.span,
                    });
                }
                Ok(arr.get(idx as usize))
            }
            ExprKind::IsSome { operand } => match self.eval(operand, frame)? {
                RtVal::Opt { value, .. } => Ok(RtVal::Bool(value.is_some())),
                RtVal::PtrOpt(o) => Ok(RtVal::Bool(o.is_some())),
                _ => unreachable!("checked: option operand"),
            },
            ExprKind::OptValue { operand } => match self.eval(operand, frame)? {
                RtVal::Opt {
                    value: Some(value), ..
                } => Ok(*value),
                RtVal::PtrOpt(Some((a, o))) => Ok(RtVal::Ptr(a, o)),
                RtVal::Opt { value: None, .. } | RtVal::PtrOpt(None) => Err(Trap {
                    undef: false,
                    message: "`.value` of an empty option".into(),
                    span: e.span,
                }),
                _ => unreachable!("checked: option operand"),
            },
            ExprKind::TraitCall { .. } => {
                unreachable!("trait calls exist only in templates, never executed")
            }
            ExprKind::ClassField { obj, field, .. } => {
                let RtVal::Obj { fields, .. } = frame.vars[obj.as_str()].clone() else {
                    unreachable!("checked: class receiver")
                };
                let v = fields.borrow()[field.as_str()].clone();
                Ok(v)
            }
            ExprKind::RecordField { obj, field, .. } => {
                let RtVal::Record { fields, .. } = frame.vars[obj.as_str()].clone() else {
                    unreachable!("checked: record receiver")
                };
                Ok(fields[field.as_str()].clone())
            }
            ExprKind::ClassFieldLen { obj, field } => {
                let RtVal::Obj { fields, .. } = frame.vars[obj.as_str()].clone() else {
                    unreachable!("checked: class receiver")
                };
                let RtVal::Arr(a) = fields.borrow()[field.as_str()].clone() else {
                    unreachable!("checked: array field")
                };
                let n = a.borrow().len() as i128;
                Ok(RtVal::Int(n))
            }
            ExprKind::ClassFieldIndex {
                obj, field, index, ..
            } => {
                let RtVal::Obj { fields, .. } = frame.vars[obj.as_str()].clone() else {
                    unreachable!("checked: class receiver")
                };
                let RtVal::Arr(a) = fields.borrow()[field.as_str()].clone() else {
                    unreachable!("checked: array field")
                };
                let idx = self.eval_int(index, frame)?;
                let arr = a.borrow();
                if idx < 0 || idx as usize >= arr.len() {
                    return Err(Trap {
                        undef: false,
                        message: format!("index out of bounds: index {idx}, length {}", arr.len()),
                        span: e.span,
                    });
                }
                Ok(arr.get(idx as usize))
            }
            ExprKind::Widen { arg, .. } => self.eval(arg, frame),
            ExprKind::Narrow { target, arg } => {
                let v = self.eval_int(arg, frame)?;
                if v < target.min() || v > target.max() {
                    return Err(Trap {
                        undef: false,
                        message: format!(
                            "narrow out of range: {v} does not fit in `{}`",
                            target.name()
                        ),
                        span: e.span,
                    });
                }
                Ok(RtVal::Int(v))
            }
            ExprKind::SomeE(inner) => match e.ty {
                Some(Ty::Option(payload)) => {
                    let value = self.eval(inner, frame)?;
                    Ok(RtVal::Opt {
                        payload,
                        value: Some(Box::new(value)),
                    })
                }
                Some(Ty::OptionRaw(_)) => {
                    let RtVal::Ptr(a, o) = self.eval(inner, frame)? else {
                        unreachable!("checked: raw pointer option")
                    };
                    Ok(RtVal::PtrOpt(Some((a, o))))
                }
                _ => unreachable!("checked: option construction"),
            },
            ExprKind::NoneE => match e.ty {
                Some(Ty::Option(payload)) => Ok(RtVal::Opt {
                    payload,
                    value: None,
                }),
                Some(Ty::OptionRaw(_)) => Ok(RtVal::PtrOpt(None)),
                _ => unreachable!("checked: option construction"),
            },
            ExprKind::ArrayLit(elems) => {
                let Some(Ty::Array(payload, Mutability::Owned)) = e.ty else {
                    unreachable!("checked: owned array literal type")
                };
                let mut values = Vec::with_capacity(elems.len());
                for el in elems {
                    values.push(self.eval(el, frame)?);
                }
                Ok(RtVal::Arr(Rc::new(RefCell::new(RtArray::from_values(
                    payload, values,
                )))))
            }
            ExprKind::Borrow { array, field, .. } => {
                let base = if array == "self" {
                    let (class, fields) = frame.self_ctx.clone().expect("checked: member ctx");
                    RtVal::Obj { class, fields }
                } else {
                    frame.vars[array.as_str()].clone()
                };
                match field {
                    // `&x.f` — borrow the field's value, not the base
                    // (ADR 0020). Sharing the Rc is the borrow.
                    Some(f) => {
                        let RtVal::Obj { fields, .. } = base else {
                            unreachable!("checked: class base")
                        };
                        let v = fields.borrow()[f.as_str()].clone();
                        Ok(v)
                    }
                    None => Ok(base),
                }
            }
            ExprKind::AllocArray { elem, len, init } => {
                let n = self.eval_int(len, frame)?;
                let initial = self.eval(init, frame)?;
                // Defined allocation-failure behavior: the named OOM trap.
                if n < 0 || n > 50_000_000 {
                    return Err(Trap {
                        undef: false,
                        message: format!("OOM trap: alloc_array of length {n}"),
                        span: e.span,
                    });
                }
                Ok(RtVal::Arr(Rc::new(RefCell::new(RtArray::repeat(
                    *elem, initial, n as usize,
                )))))
            }
            ExprKind::SelfField { field } => {
                let (_, fields) = frame.self_ctx.clone().expect("checked: member ctx");
                let v = fields
                    .borrow()
                    .get(field.as_str())
                    .cloned()
                    .expect("checked: field initialized");
                Ok(v)
            }
            ExprKind::SelfFieldLen { field } => {
                let (_, fields) = frame.self_ctx.clone().expect("checked: member ctx");
                let arr = match fields.borrow().get(field.as_str()) {
                    Some(RtVal::Arr(a)) => a.clone(),
                    _ => unreachable!("checked: array field"),
                };
                let n = arr.borrow().len() as i128;
                Ok(RtVal::Int(n))
            }
            ExprKind::SelfFieldIndex { field, index } => {
                let idx = self.eval_int(index, frame)?;
                let (_, fields) = frame.self_ctx.clone().expect("checked: member ctx");
                let arr = match fields.borrow().get(field.as_str()) {
                    Some(RtVal::Arr(a)) => a.clone(),
                    _ => unreachable!("checked: array field"),
                };
                let len = arr.borrow().len() as i128;
                if idx < 0 || idx >= len {
                    return Err(Trap {
                        undef: false,
                        message: format!("index out of bounds: index {idx}, length {len}"),
                        span: e.span,
                    });
                }
                Ok(arr.borrow().get(idx as usize))
            }
            ExprKind::CtorCall {
                class, init, args, ..
            } => {
                let ci = self
                    .classes
                    .iter()
                    .position(|c| c.name == *class)
                    .expect("checked: class exists");
                let mut vals = Vec::with_capacity(args.len());
                for a in args {
                    vals.push(self.eval_moved(a, frame)?);
                }
                self.construct(ci, init, vals, e.span)
            }
            ExprKind::RecordLit { record, args, .. } => {
                let ri = self
                    .records
                    .iter()
                    .position(|r| r.name == *record)
                    .expect("checked: record exists");
                let field_names: Vec<String> = self.records[ri]
                    .fields
                    .iter()
                    .map(|field| field.name.clone())
                    .collect();
                let mut fields = HashMap::new();
                for (name, arg) in field_names.into_iter().zip(args) {
                    fields.insert(name, self.eval(arg, frame)?);
                }
                Ok(RtVal::Record { record: ri, fields })
            }
            ExprKind::MethodCall {
                recv, method, args, ..
            } => {
                let RtVal::Obj { class, fields } = frame.vars[recv.as_str()].clone() else {
                    unreachable!("checked: class receiver")
                };
                let mut vals = Vec::with_capacity(args.len());
                for a in args {
                    vals.push(self.eval_moved(a, frame)?);
                }
                self.invoke(class, method, fields, vals)
            }
            ExprKind::Unary { op, operand } => match op {
                UnOp::Not => {
                    let b = self.eval_bool(operand, frame)?;
                    Ok(RtVal::Bool(!b))
                }
                UnOp::Neg => {
                    let v = self.eval_int(operand, frame)?;
                    let Ty::Int(it) = e.ty.unwrap() else {
                        unreachable!()
                    };
                    self.check_range(-v, it, e, "negation")?;
                    Ok(RtVal::Int(-v))
                }
            },
            ExprKind::Binary { op, lhs, rhs, .. } => {
                if matches!(op, BinOp::And | BinOp::Or) {
                    let l = self.eval_bool(lhs, frame)?;
                    // Short-circuit, matching the VC semantics.
                    return Ok(RtVal::Bool(match op {
                        BinOp::And => l && self.eval_bool(rhs, frame)?,
                        BinOp::Or => l || self.eval_bool(rhs, frame)?,
                        _ => unreachable!(),
                    }));
                }
                let a = self.eval_int(lhs, frame)?;
                let b = self.eval_int(rhs, frame)?;
                if op.is_comparison() {
                    return Ok(RtVal::Bool(match op {
                        BinOp::Lt => a < b,
                        BinOp::Le => a <= b,
                        BinOp::Gt => a > b,
                        BinOp::Ge => a >= b,
                        BinOp::Eq => a == b,
                        BinOp::Ne => a != b,
                        _ => unreachable!(),
                    }));
                }
                let Ty::Int(it) = e.ty.unwrap() else {
                    unreachable!()
                };
                let val = match op {
                    BinOp::Add => a + b,
                    BinOp::Sub => a - b,
                    BinOp::Mul => a.checked_mul(b).ok_or_else(|| Trap {
                        undef: false,
                        message: "multiplication exceeds i128 (ghost width)".into(),
                        span: e.span,
                    })?,
                    BinOp::Div | BinOp::Rem => {
                        if b == 0 {
                            return Err(Trap {
                                undef: false,
                                message: "division by zero".into(),
                                span: rhs.span,
                            });
                        }
                        if *op == BinOp::Div && it.signed() && a == it.min() && b == -1 {
                            return Err(Trap {
                                undef: false,
                                message: format!(
                                    "Euclidean quotient overflows: {}.min / -1",
                                    it.name()
                                ),
                                span: e.span,
                            });
                        }
                        if *op == BinOp::Div {
                            a.div_euclid(b)
                        } else {
                            a.rem_euclid(b)
                        }
                    }
                    _ => unreachable!(),
                };
                if matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) {
                    self.check_range(val, it, e, op.symbol())?;
                }
                Ok(RtVal::Int(val))
            }
            ExprKind::Call { callee, args, .. } => {
                let f = self.fns[callee.as_str()];
                // Resource arguments are erased: authority is a static
                // notion, so it has no runtime representation to pass and
                // the callee's runtime signature does not have the
                // parameter at all (ADR 0024). Resource-map shadow metadata
                // is the sole interpreter-only exception, and it follows
                // verified Sable calls but never crosses an extern ABI.
                // A by-value class argument is a *move*, and moves clear
                // their source place — `eval_moved` is the same operation
                // the other transfers use.
                let mut vals = Vec::with_capacity(args.len());
                for (a, p) in args.iter().zip(&f.params) {
                    if p.ty.is_resource() && (f.extern_info.is_some() || !has_resource_shadow(p.ty))
                    {
                        self.eval_erased_resource_arg(a, frame)?;
                        continue;
                    }
                    vals.push(self.eval_moved(a, frame)?);
                }
                if f.extern_info.is_some() {
                    // The foreign implementation receives only ABI values:
                    // resources were already dropped above.
                    return self.call_extern(f, vals, e.span);
                }
                self.call(f, vals)
            }
        }
    }

    fn check_range(&self, val: i128, it: IntTy, e: &Expr, what: &str) -> IResult<()> {
        if val < it.min() || val > it.max() {
            let src = &self.source[e.span.start..e.span.end.min(self.source.len())];
            return Err(Trap {
                undef: false,
                message: format!(
                    "overflow: `{src}` = {val} does not fit in `{}` ({what})",
                    it.name()
                ),
                span: e.span,
            });
        }
        Ok(())
    }

    fn burn(&mut self, span: crate::span::Span) -> IResult<()> {
        if self.fuel == 0 {
            return Err(Trap {
                undef: false,
                message: "fuel exhausted (runaway loop or recursion?)".into(),
                span,
            });
        }
        self.fuel -= 1;
        Ok(())
    }
}

fn deep_copy(v: &RtVal) -> RtVal {
    match v {
        RtVal::Arr(a) => RtVal::Arr(Rc::new(RefCell::new(a.borrow().clone()))),
        RtVal::Opt { payload, value } => RtVal::Opt {
            payload: *payload,
            value: value.as_deref().map(deep_copy).map(Box::new),
        },
        RtVal::Obj { class, fields } => RtVal::Obj {
            class: *class,
            fields: Rc::new(RefCell::new(
                fields
                    .borrow()
                    .iter()
                    .map(|(k, v)| (k.clone(), deep_copy(v)))
                    .collect(),
            )),
        },
        RtVal::Record { record, fields } => RtVal::Record {
            record: *record,
            fields: fields
                .iter()
                .map(|(name, value)| (name.clone(), deep_copy(value)))
                .collect(),
        },
        other => other.clone(),
    }
}

fn spec_of(v: &RtVal) -> Option<SpecVal> {
    Some(match v {
        RtVal::Int(n) => SpecVal::Int(*n),
        RtVal::Bool(b) => SpecVal::Bool(*b),
        RtVal::Arr(a) => SpecVal::Arr(a.borrow().to_spec()),
        RtVal::Opt { payload, value } => SpecVal::Opt {
            payload: Some(*payload),
            value: match value {
                Some(value) => Some(Box::new(spec_of(value)?)),
                None => None,
            },
        },
        RtVal::PtrOpt(_) => return None,
        RtVal::Obj { fields, .. } => SpecVal::Obj(
            fields
                .borrow()
                .iter()
                .filter_map(|(k, v)| spec_of(v).map(|sv| (k.clone(), sv)))
                .collect(),
        ),
        RtVal::Record { fields, .. } => {
            let mut out = HashMap::new();
            for (name, value) in fields {
                out.insert(name.clone(), spec_of(value)?);
            }
            SpecVal::Obj(out)
        }
        // A pointer has no specification value: contracts speak about
        // views, and a view is not something the monitor can see.
        RtVal::Ptr(..) => return None,
        RtVal::ResMap(..) => return None,
        RtVal::Unit => return None,
    })
}

fn stmt_span(stmt: &Stmt) -> crate::span::Span {
    match stmt {
        Stmt::Unsafe { kw_span, .. }
        | Stmt::StaticAlloc { kw_span, .. }
        | Stmt::SystemAlloc { kw_span, .. }
        | Stmt::SystemDealloc { kw_span, .. }
        | Stmt::Expose { kw_span, .. } => *kw_span,
        Stmt::Decl { name_span, .. } | Stmt::Assign { name_span, .. } => *name_span,
        Stmt::Assert(c) => c.line_span,
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

#[cfg(test)]
mod g1_payload_guard_tests {
    use super::*;
    use crate::span::Span;

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

    fn function(name: &str, ret: Ty, body: Vec<Stmt>) -> Fn {
        Fn {
            is_pub: false,
            extern_info: None,
            name: name.into(),
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

    fn expr(kind: ExprKind, ty: Option<Ty>) -> Expr {
        Expr {
            kind,
            span: Span::new(0, 0),
            ty,
        }
    }

    fn int_lit(value: i128) -> Expr {
        expr(ExprKind::IntLit(value), Some(Ty::Int(IntTy::U64)))
    }

    fn affine_bool_option() -> Ty {
        Ty::AffineOption(AffineOptionTy::Array(ValueTy::Bool))
    }

    fn public_interp_error(program: &Program) -> String {
        let modules = crate::modules::ModuleSet::single("synthetic".into(), String::new());
        run_fn(program, &modules, "subject")
            .expect_err("synthetic affine-option program reached interpreter execution")
    }

    #[test]
    fn affine_options_fail_closed_at_the_public_interpreter_boundary() {
        let mut return_program = empty_program();
        return_program
            .fns
            .push(function("subject", affine_bool_option(), Vec::new()));
        assert!(
            public_interp_error(&return_program).starts_with("interp.affine_option_unsupported:")
        );

        let mut local_program = empty_program();
        local_program.fns.push(function(
            "subject",
            Ty::Unit,
            vec![Stmt::Decl {
                ty: affine_bool_option(),
                name: "maybe_flags".into(),
                name_span: Span::new(0, 0),
                init: None,
                mutable: false,
            }],
        ));
        assert!(
            public_interp_error(&local_program).starts_with("interp.affine_option_unsupported:")
        );

        let mut expression_program = empty_program();
        expression_program.fns.push(function(
            "subject",
            Ty::Unit,
            vec![Stmt::ExprStmt(expr(
                ExprKind::IsSome {
                    operand: Box::new(expr(ExprKind::NoneE, Some(affine_bool_option()))),
                },
                Some(Ty::Bool),
            ))],
        ));
        assert!(
            public_interp_error(&expression_program)
                .starts_with("interp.affine_option_unsupported:")
        );
    }

    fn with_empty_interpreter<R>(run: impl FnOnce(&mut Interp<'_>) -> R) -> R {
        let fns: HashMap<&str, &Fn> = HashMap::new();
        let classes: Vec<ClassDecl> = Vec::new();
        let records: Vec<RecordDecl> = Vec::new();
        let ghosts = GhostDefs::from_items(&[]);
        let mut interpreter = Interp {
            fns: &fns,
            classes: &classes,
            records: &records,
            ghosts: &ghosts,
            source: "",
            fuel: FUEL,
            skipped: Vec::new(),
            raw: RawHeap::default(),
            world: None,
            uart: None,
        };
        run(&mut interpreter)
    }

    fn frame_with(vars: HashMap<String, RtVal>) -> Frame {
        Frame {
            vars,
            entry_scalars: HashMap::new(),
            olds: HashMap::new(),
            self_ctx: None,
        }
    }

    fn bool_array_decl(name: &str) -> Stmt {
        let ty = Ty::Array(ValueTy::Bool, Mutability::Owned);
        Stmt::Decl {
            ty,
            name: name.into(),
            name_span: Span::new(0, 0),
            init: Some(expr(
                ExprKind::ArrayLit(vec![expr(ExprKind::BoolLit(true), Some(Ty::Bool))]),
                Some(ty),
            )),
            mutable: false,
        }
    }

    fn eval_with_frame(expression: &Expr, vars: HashMap<String, RtVal>) -> Result<RtVal, String> {
        with_empty_interpreter(|interpreter| {
            interpreter
                .eval(expression, &mut frame_with(vars))
                .map_err(|trap| trap.message)
        })
    }

    fn eval_with_empty_runtime(expression: &Expr) -> Result<RtVal, String> {
        eval_with_frame(expression, HashMap::new())
    }

    #[test]
    fn dropping_an_array_place_removes_its_binding_and_releases_its_rc() {
        let storage = Rc::new(RefCell::new(RtArray::Bool(vec![true])));
        let mut frame = frame_with(HashMap::from([(
            "flags".into(),
            RtVal::Arr(storage.clone()),
        )]));
        assert_eq!(Rc::strong_count(&storage), 2);

        with_empty_interpreter(|interpreter| {
            interpreter
                .drop_place(&RtPlace::Local("flags".into()), &mut frame)
                .unwrap_or_else(|trap| panic!("unexpected array-drop trap: {}", trap.message));
        });

        assert!(!frame.vars.contains_key("flags"));
        assert_eq!(Rc::strong_count(&storage), 1);
    }

    #[test]
    fn eval_moved_takes_an_owned_integer_array_place() {
        let storage = Rc::new(RefCell::new(RtArray::Int {
            payload: IntTy::U64,
            values: vec![7],
        }));
        let mut frame = frame_with(HashMap::from([(
            "values".into(),
            RtVal::Arr(storage.clone()),
        )]));
        let read = expr(
            ExprKind::Var("values".into()),
            Some(Ty::Array(ValueTy::Int(IntTy::U64), Mutability::Owned)),
        );

        let value = with_empty_interpreter(|interpreter| {
            interpreter
                .eval_moved(&read, &mut frame)
                .unwrap_or_else(|trap| panic!("unexpected array-move trap: {}", trap.message))
        });

        assert!(!frame.vars.contains_key("values"));
        assert!(matches!(&value, RtVal::Arr(_)));
        assert_eq!(Rc::strong_count(&storage), 2);
    }

    #[test]
    fn successful_branch_and_loop_blocks_remove_array_locals() {
        let mut frame = frame_with(HashMap::from([("again".into(), RtVal::Bool(true))]));
        let branch = Stmt::If {
            cond: expr(ExprKind::BoolLit(true), Some(Ty::Bool)),
            then_block: vec![bool_array_decl("branch_flags")],
            else_block: None,
        };
        let loop_stmt = Stmt::While {
            cond: expr(ExprKind::Var("again".into()), Some(Ty::Bool)),
            invariants: Vec::new(),
            variant: None,
            kw_span: Span::new(0, 0),
            body: vec![
                bool_array_decl("loop_flags"),
                Stmt::Assign {
                    name: "again".into(),
                    name_span: Span::new(0, 0),
                    value: expr(ExprKind::BoolLit(false), Some(Ty::Bool)),
                },
            ],
        };

        with_empty_interpreter(|interpreter| {
            let mut outer_locals = Vec::new();
            assert!(matches!(
                interpreter.exec_stmt(&branch, &mut frame, &mut outer_locals),
                Ok(Flow::Normal)
            ));
            assert!(!frame.vars.contains_key("branch_flags"));
            assert!(matches!(
                interpreter.exec_stmt(&loop_stmt, &mut frame, &mut outer_locals),
                Ok(Flow::Normal)
            ));
        });

        assert!(!frame.vars.contains_key("loop_flags"));
    }

    #[test]
    fn trapped_blocks_retain_array_places_without_running_cleanup() {
        let mut frame = frame_with(HashMap::new());
        let body = vec![
            bool_array_decl("trapped_flags"),
            Stmt::ExprStmt(expr(
                ExprKind::Index {
                    array: "trapped_flags".into(),
                    array_span: Span::new(0, 0),
                    index: Box::new(int_lit(1)),
                },
                Some(Ty::Bool),
            )),
        ];

        let trapped =
            with_empty_interpreter(
                |interpreter| match interpreter.exec_block(&body, &mut frame) {
                    Err(trap) => trap,
                    Ok(_) => panic!("out-of-bounds index should trap"),
                },
            );

        assert_eq!(trapped.message, "index out of bounds: index 1, length 1");
        assert!(frame.vars.contains_key("trapped_flags"));
    }

    #[test]
    fn unsafe_marker_keeps_array_local_in_the_enclosing_scope() {
        let mut frame = frame_with(HashMap::new());
        let unsafe_block = Stmt::Unsafe {
            kw_span: Span::new(0, 0),
            body: vec![bool_array_decl("open_flags")],
        };
        let mut enclosing_locals = Vec::new();

        with_empty_interpreter(|interpreter| {
            assert!(matches!(
                interpreter.exec_stmt(&unsafe_block, &mut frame, &mut enclosing_locals),
                Ok(Flow::Normal)
            ));
        });

        assert!(frame.vars.contains_key("open_flags"));
        assert_eq!(enclosing_locals, vec!["open_flags".to_string()]);
    }

    #[test]
    fn rejects_option_payloads_without_g1_runtime_semantics() {
        let unsupported = [
            ValueTy::Record(0),
            ValueTy::Param(TypeParamId::from_legacy(0)),
            ValueTy::Int(IntTy::TParam(0)),
        ];

        for payload in unsupported {
            let mut program = empty_program();
            program
                .fns
                .push(function("subject", Ty::Option(payload), Vec::new()));
            let error = validate_interp_program(&program)
                .expect_err("an unsupported option payload must fail closed");
            assert!(
                error.starts_with("interp.aggregate_payload_unsupported:"),
                "{payload:?}: {error}"
            );
        }
    }

    #[test]
    fn permits_owned_local_boolean_arrays_but_not_nonlocal_positions() {
        let mut program = empty_program();
        program.fns.push(function(
            "subject",
            Ty::Unit,
            vec![Stmt::Decl {
                ty: Ty::Array(ValueTy::Bool, Mutability::Owned),
                name: "flags".into(),
                name_span: Span::new(0, 0),
                init: Some(expr(
                    ExprKind::AllocArray {
                        elem: ValueTy::Bool,
                        len: Box::new(int_lit(0)),
                        init: Box::new(expr(ExprKind::BoolLit(false), Some(Ty::Bool))),
                    },
                    Some(Ty::Array(ValueTy::Bool, Mutability::Owned)),
                )),
                mutable: true,
            }],
        ));

        validate_interp_program(&program).expect("owned local Boolean arrays have G1.4b semantics");
        for ty in [
            Ty::Array(ValueTy::Bool, Mutability::Shared),
            Ty::Array(ValueTy::Bool, Mutability::Mut),
        ] {
            assert!(
                validate_interp_ty(ty, "Boolean array borrow")
                    .unwrap_err()
                    .starts_with("interp.array_position_unsupported:")
            );
        }
        assert!(
            validate_interp_nonlocal_option_position(
                Ty::Array(ValueTy::Bool, Mutability::Owned),
                "parameter `flags`",
            )
            .unwrap_err()
            .starts_with("interp.array_position_unsupported:")
        );
    }

    #[test]
    fn option_parameters_and_stored_fields_remain_outside_g1_1() {
        for context in ["parameter `value`", "field `Box.value`"] {
            let error =
                validate_interp_nonlocal_option_position(Ty::Option(ValueTy::Bool), context)
                    .expect_err("G1.1 must not introduce an option parameter/field ABI");
            assert!(error.starts_with("interp.option_position_unsupported:"));
        }
    }

    #[test]
    fn boolean_option_construction_access_and_empty_trap_are_typed() {
        let some_false = expr(
            ExprKind::SomeE(Box::new(expr(ExprKind::BoolLit(false), Some(Ty::Bool)))),
            Some(Ty::Option(ValueTy::Bool)),
        );
        let is_some = expr(
            ExprKind::IsSome {
                operand: Box::new(some_false.clone()),
            },
            Some(Ty::Bool),
        );
        let value = expr(
            ExprKind::OptValue {
                operand: Box::new(some_false),
            },
            Some(Ty::Bool),
        );

        assert!(matches!(
            eval_with_empty_runtime(&is_some),
            Ok(RtVal::Bool(true))
        ));
        assert!(matches!(
            eval_with_empty_runtime(&value),
            Ok(RtVal::Bool(false))
        ));

        let none = expr(ExprKind::NoneE, Some(Ty::Option(ValueTy::Bool)));
        let runtime_none = eval_with_empty_runtime(&none).unwrap();
        assert_eq!(
            spec_of(&runtime_none),
            Some(SpecVal::Opt {
                payload: Some(ValueTy::Bool),
                value: None,
            })
        );
        let empty_value = expr(
            ExprKind::OptValue {
                operand: Box::new(none),
            },
            Some(Ty::Bool),
        );
        assert_eq!(
            eval_with_empty_runtime(&empty_value).unwrap_err(),
            "`.value` of an empty option"
        );
    }

    #[test]
    fn deep_copy_recurses_through_present_options() {
        let original = RtVal::Opt {
            payload: ValueTy::Bool,
            value: Some(Box::new(RtVal::Bool(false))),
        };
        let copied = deep_copy(&original);
        assert!(matches!(
            copied,
            RtVal::Opt {
                payload: ValueTy::Bool,
                value: Some(value),
            } if matches!(*value, RtVal::Bool(false))
        ));
    }

    #[test]
    fn recursively_accepts_boolean_alloc_array_element_metadata() {
        let allocation = expr(
            ExprKind::AllocArray {
                elem: ValueTy::Bool,
                len: Box::new(int_lit(1)),
                init: Box::new(expr(ExprKind::BoolLit(false), Some(Ty::Bool))),
            },
            Some(Ty::Array(ValueTy::Bool, Mutability::Owned)),
        );
        let mut program = empty_program();
        program.fns.push(function(
            "subject",
            Ty::Unit,
            vec![Stmt::Decl {
                ty: Ty::Array(ValueTy::Bool, Mutability::Owned),
                name: "values".into(),
                name_span: Span::new(0, 0),
                init: Some(allocation),
                mutable: false,
            }],
        ));

        validate_interp_program(&program).expect("Boolean allocation metadata is executable");
    }

    #[test]
    fn index_accepts_boolean_or_concrete_integer_result_annotations() {
        let load = expr(
            ExprKind::Index {
                array: "values".into(),
                array_span: Span::new(0, 0),
                index: Box::new(int_lit(0)),
            },
            Some(Ty::Bool),
        );
        let mut program = empty_program();
        program.fns.push(function(
            "subject",
            Ty::Unit,
            vec![
                Stmt::Decl {
                    ty: Ty::Array(ValueTy::Bool, Mutability::Owned),
                    name: "values".into(),
                    name_span: Span::new(0, 0),
                    init: Some(expr(
                        ExprKind::ArrayLit(vec![expr(ExprKind::BoolLit(true), Some(Ty::Bool))]),
                        Some(Ty::Array(ValueTy::Bool, Mutability::Owned)),
                    )),
                    mutable: false,
                },
                Stmt::ExprStmt(load),
            ],
        ));

        validate_interp_program(&program).expect("Boolean array indices produce Boolean values");
    }

    #[test]
    fn boolean_array_literal_allocation_index_store_and_snapshots_are_typed() {
        let bool_ty = Ty::Array(ValueTy::Bool, Mutability::Owned);
        let literal = expr(
            ExprKind::ArrayLit(vec![
                expr(ExprKind::BoolLit(true), Some(Ty::Bool)),
                expr(ExprKind::BoolLit(false), Some(Ty::Bool)),
            ]),
            Some(bool_ty),
        );
        let RtVal::Arr(values) = eval_with_empty_runtime(&literal).unwrap() else {
            panic!("expected an array")
        };
        assert!(matches!(
            &*values.borrow(),
            RtArray::Bool(values) if values == &[true, false]
        ));

        let allocated = expr(
            ExprKind::AllocArray {
                elem: ValueTy::Bool,
                len: Box::new(int_lit(2)),
                init: Box::new(expr(ExprKind::BoolLit(true), Some(Ty::Bool))),
            },
            Some(bool_ty),
        );
        let RtVal::Arr(values) = eval_with_empty_runtime(&allocated).unwrap() else {
            panic!("expected an array")
        };
        values.borrow_mut().set(1, RtVal::Bool(false));
        let index = expr(
            ExprKind::Index {
                array: "flags".into(),
                array_span: Span::new(0, 0),
                index: Box::new(int_lit(1)),
            },
            Some(Ty::Bool),
        );
        assert!(matches!(
            eval_with_frame(
                &index,
                HashMap::from([("flags".into(), RtVal::Arr(values.clone()))])
            ),
            Ok(RtVal::Bool(false))
        ));

        let empty = RtVal::Arr(Rc::new(RefCell::new(RtArray::Bool(Vec::new()))));
        assert_eq!(
            spec_of(&empty),
            Some(SpecVal::Arr(SpecArray::Bool(Vec::new())))
        );
        let RtVal::Arr(copied) = deep_copy(&empty) else {
            panic!("expected copied array")
        };
        assert!(matches!(&*copied.borrow(), RtArray::Bool(values) if values.is_empty()));
    }

    #[test]
    fn boolean_array_guard_rejects_forged_payloads_indices_stores_and_transports() {
        let bool_array = Ty::Array(ValueTy::Bool, Mutability::Owned);
        let bad_alloc = expr(
            ExprKind::AllocArray {
                elem: ValueTy::Bool,
                len: Box::new(expr(ExprKind::BoolLit(true), Some(Ty::Int(IntTy::U64)))),
                init: Box::new(expr(ExprKind::IntLit(1), Some(Ty::Bool))),
            },
            Some(bool_array),
        );
        assert!(validate_interp_expr(&bad_alloc, &HashMap::new()).is_err());

        let bad_outer = expr(
            ExprKind::AllocArray {
                elem: ValueTy::Bool,
                len: Box::new(int_lit(1)),
                init: Box::new(expr(ExprKind::BoolLit(false), Some(Ty::Bool))),
            },
            Some(Ty::Array(ValueTy::Int(IntTy::U8), Mutability::Owned)),
        );
        assert!(validate_interp_expr(&bad_outer, &HashMap::new()).is_err());

        let mut program = empty_program();
        program.fns.push(function(
            "subject",
            Ty::Unit,
            vec![
                Stmt::Decl {
                    ty: bool_array,
                    name: "flags".into(),
                    name_span: Span::new(0, 0),
                    init: Some(expr(ExprKind::ArrayLit(vec![]), Some(bool_array))),
                    mutable: true,
                },
                Stmt::Store {
                    array: "flags".into(),
                    array_span: Span::new(0, 0),
                    index: expr(ExprKind::BoolLit(false), Some(Ty::Int(IntTy::U64))),
                    value: expr(ExprKind::IntLit(0), Some(Ty::Bool)),
                },
            ],
        ));
        assert!(validate_interp_program(&program).is_err());

        let forged_call = expr(
            ExprKind::Call {
                callee: "make".into(),
                callee_span: Span::new(0, 0),
                type_args: vec![],
                args: vec![],
            },
            Some(bool_array),
        );
        assert!(
            validate_interp_expr(&forged_call, &HashMap::new())
                .unwrap_err()
                .starts_with("interp.array_position_unsupported:")
        );
    }

    #[test]
    fn boolean_array_guard_rejects_object_option_and_scalar_operator_laundering() {
        let bool_array = Ty::Array(ValueTy::Bool, Mutability::Owned);
        let locals = HashMap::from([("flags".into(), bool_array)]);
        let span = Span::new(0, 0);
        let receiver_uses = [
            expr(
                ExprKind::MethodCall {
                    recv: "flags".into(),
                    recv_span: span,
                    method: "read".into(),
                    method_span: span,
                    args: vec![],
                },
                Some(Ty::Unit),
            ),
            expr(
                ExprKind::ClassField {
                    obj: "flags".into(),
                    obj_span: span,
                    field: "value".into(),
                },
                Some(Ty::Bool),
            ),
            expr(
                ExprKind::RecordField {
                    obj: "flags".into(),
                    obj_span: span,
                    field: "value".into(),
                },
                Some(Ty::Bool),
            ),
            expr(
                ExprKind::ClassFieldLen {
                    obj: "flags".into(),
                    field: "values".into(),
                },
                Some(Ty::Int(IntTy::U64)),
            ),
            expr(
                ExprKind::ClassFieldIndex {
                    obj: "flags".into(),
                    obj_span: span,
                    field: "values".into(),
                    index: Box::new(int_lit(0)),
                },
                Some(Ty::Bool),
            ),
        ];
        for receiver_use in receiver_uses {
            assert!(
                validate_interp_expr(&receiver_use, &locals)
                    .unwrap_err()
                    .starts_with("interp.array_position_unsupported:"),
                "{receiver_use:?}"
            );
        }

        for accessor in [
            expr(
                ExprKind::IsSome {
                    operand: Box::new(expr(ExprKind::Var("flags".into()), Some(bool_array))),
                },
                Some(Ty::Bool),
            ),
            expr(
                ExprKind::OptValue {
                    operand: Box::new(expr(ExprKind::Var("flags".into()), Some(bool_array))),
                },
                Some(Ty::Bool),
            ),
        ] {
            assert!(
                validate_interp_expr(&accessor, &locals)
                    .unwrap_err()
                    .starts_with("interp.option_operand:"),
                "{accessor:?}"
            );
        }

        for conversion in [
            expr(
                ExprKind::Widen {
                    target: IntTy::U64,
                    arg: Box::new(expr(ExprKind::Var("flags".into()), Some(bool_array))),
                },
                Some(Ty::Int(IntTy::U64)),
            ),
            expr(
                ExprKind::Narrow {
                    target: IntTy::U8,
                    arg: Box::new(expr(ExprKind::Var("flags".into()), Some(bool_array))),
                },
                Some(Ty::Int(IntTy::U8)),
            ),
        ] {
            assert!(
                validate_interp_expr(&conversion, &locals)
                    .unwrap_err()
                    .contains("integer conversion operand"),
                "{conversion:?}"
            );
        }

        let forged_boolean = expr(
            ExprKind::Unary {
                op: UnOp::Not,
                operand: Box::new(expr(ExprKind::Var("flags".into()), Some(bool_array))),
            },
            Some(Ty::Bool),
        );
        assert!(validate_interp_expr(&forged_boolean, &locals).is_err());

        let resource_locals = HashMap::from([("authority".into(), Ty::Res(ResKind::RawSpan))]);
        let erased_place = expr(ExprKind::Var("authority".into()), None);
        reject_bool_array_transport(&erased_place, &resource_locals, "sealed operand")
            .expect("an intentionally unannotated resource place is not a Boolean array");
    }

    #[test]
    fn boolean_array_guard_rejects_scalar_statement_sinks() {
        let span = Span::new(0, 0);
        let bool_array = Ty::Array(ValueTy::Bool, Mutability::Owned);
        let int_array = Ty::Array(ValueTy::Int(IntTy::U8), Mutability::Owned);
        let bool_var = || expr(ExprKind::Var("bits".into()), Some(bool_array));
        let byte = || expr(ExprKind::IntLit(1), Some(Ty::Int(IntTy::U8)));
        let base = HashMap::from([
            ("bits".into(), bool_array),
            ("ints".into(), int_array),
            ("raw".into(), Ty::Res(ResKind::RawSpan)),
            ("release".into(), Ty::Res(ResKind::SystemDealloc)),
        ]);

        let forged_sinks = vec![
            Stmt::Store {
                array: "ints".into(),
                array_span: span,
                index: bool_var(),
                value: byte(),
            },
            Stmt::Store {
                array: "ints".into(),
                array_span: span,
                index: int_lit(0),
                value: bool_var(),
            },
            Stmt::FieldStore {
                field: "bytes".into(),
                field_span: span,
                index: bool_var(),
                value: byte(),
            },
            Stmt::If {
                cond: bool_var(),
                then_block: vec![],
                else_block: None,
            },
            Stmt::While {
                cond: bool_var(),
                invariants: vec![],
                variant: None,
                kw_span: span,
                body: vec![],
            },
            Stmt::StaticAlloc {
                kw_span: span,
                size: bool_var(),
                ptr: "p".into(),
                ptr_span: span,
                res: "memory".into(),
                res_span: span,
            },
            Stmt::SystemAlloc {
                kw_span: span,
                size: bool_var(),
                ptr: "p".into(),
                ptr_span: span,
                res: "memory".into(),
                res_span: span,
                release: "free".into(),
                release_span: span,
            },
            Stmt::SystemDealloc {
                kw_span: span,
                ptr: bool_var(),
                res: expr(ExprKind::Var("raw".into()), None),
                release: expr(ExprKind::Var("release".into()), None),
            },
        ];

        for statement in forged_sinks {
            let error = validate_interp_stmts(&[statement], &mut base.clone())
                .expect_err("a Boolean array must not reach a scalar statement sink");
            assert!(
                error.starts_with("interp.expression_type:")
                    || error.starts_with("interp.array_position_unsupported:"),
                "{error}"
            );
        }
    }

    #[test]
    fn permits_integer_execution_and_ignores_retained_templates() {
        let mut program = empty_program();
        program.fns.push(function(
            "subject",
            Ty::Option(ValueTy::Int(IntTy::U64)),
            vec![Stmt::Return {
                value: Some(expr(
                    ExprKind::NoneE,
                    Some(Ty::Option(ValueTy::Int(IntTy::U64))),
                )),
                span: Span::new(0, 0),
            }],
        ));
        program.fn_templates.push(function(
            "template",
            Ty::Option(ValueTy::Param(TypeParamId::from_legacy(0))),
            Vec::new(),
        ));

        validate_interp_program(&program)
            .expect("the executable integer domain should remain unchanged");
    }
}
