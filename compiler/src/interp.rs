//! `sable test`: the tree-walking interpreter with trap semantics
//! (design §9). Every partial operation is checked exactly where the
//! verifier would emit a VC — overflow, bounds, division — and every
//! monitorable contract (pre, post, invariant, variant) is evaluated
//! dynamically via `speceval`. Unmonitorable clauses are reported as
//! skipped, never guessed.
//!
//! This is a dev tool in the sanitizer category: its results are not a
//! verification claim, and test functions are never verified.

use crate::ast;
use crate::ast::*;
use crate::control::{
    AssignmentStaging, BlockId, BodyPlan, ClassDropPhase, ClassDropPlan, ControlProgram, DropId,
    ExitRoute, PlanError, ScopeId, StatementPlanKind, TrapSite, ValueDropAction, ValueDropRecipe,
};
use crate::place::Place;
use crate::span::Span;
use crate::speceval::{self, GhostDefs, SpecArray, SpecEnv, SpecVal};
use crate::transition::CallOwner;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

#[derive(Debug)]
pub enum RtVal {
    Int(i128),
    Bool(bool),
    Arr(Rc<RefCell<RtArray>>),
    /// An ordinary option. The checked payload type is retained even for
    /// `none`, because the dynamic proof monitor must implement the typed
    /// `Option.value = getD default` model (`0` for integers, `false` for
    /// booleans) after a function returns.
    Opt {
        payload: Ty,
        value: Option<Box<RtVal>>,
    },
    /// The ownership-bearing option.  Its payload slot
    /// lives directly in the named runtime place so `.take` can clear that
    /// place atomically.  The contained array is never cloned or deep-copied.
    AffineOptBoolArray(Option<Rc<RefCell<RtArray>>>),
    /// The ownership-bearing option over a class: the payload slot lives
    /// directly in the named runtime place, and a present payload carries
    /// the class's destructor with it.
    AffineOptClass {
        class: usize,
        value: Option<Rc<RefCell<HashMap<String, RtVal>>>>,
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

impl Clone for RtVal {
    fn clone(&self) -> Self {
        match self {
            RtVal::Int(value) => RtVal::Int(*value),
            RtVal::Bool(value) => RtVal::Bool(*value),
            RtVal::Arr(array) => RtVal::Arr(array.clone()),
            RtVal::Opt { payload, value } => RtVal::Opt {
                payload: payload.clone(),
                value: value.clone(),
            },
            RtVal::AffineOptBoolArray(_) | RtVal::AffineOptClass { .. } => {
                panic!("affine option runtime values cannot be cloned")
            }
            RtVal::PtrOpt(value) => RtVal::PtrOpt(*value),
            RtVal::Record { record, fields } => RtVal::Record {
                record: *record,
                fields: fields.clone(),
            },
            RtVal::Obj { class, fields } => RtVal::Obj {
                class: *class,
                fields: fields.clone(),
            },
            RtVal::Ptr(allocation, offset) => RtVal::Ptr(*allocation, *offset),
            RtVal::ResMap(entries) => RtVal::ResMap(entries.clone()),
            RtVal::Unit => RtVal::Unit,
        }
    }
}

impl RtVal {
    /// Whether this value is a member of `payload`'s domain.
    ///
    /// An allow-list: a payload with no runtime value is inhabited by
    /// nothing, so a container that would hold one is refused at the point it
    /// is built rather than answering confidently from a mismatched element.
    fn inhabits(&self, payload: &Ty) -> bool {
        match (self, payload) {
            (RtVal::Int(_), Ty::Int(integer)) => !matches!(integer, IntTy::TParam(_)),
            (RtVal::Bool(_), Ty::Bool) => true,
            (RtVal::Record { record, .. }, Ty::Record(declared)) => record == declared,
            _ => false,
        }
    }
}

/// Runtime arrays retain their checked payload even when empty, so an empty
/// integer array and an empty Boolean array remain distinguishable and accept
/// different stores. The tag sits beside the elements rather than inside their
/// representation: an array holds whatever a runtime value can hold, which
/// makes admitting a new payload a checker question rather than a runtime one.
///
/// Elements are cloned in and out with `RtVal`'s ordinary semantics, which
/// share an inner array's storage rather than copying it. Nested owned arrays
/// therefore need an explicit copy rule before they are admitted; the checker
/// rejects them today.
#[derive(Debug, Clone)]
pub struct RtArray {
    payload: Ty,
    values: Vec<RtVal>,
}

impl RtArray {
    pub fn len(&self) -> usize {
        self.values.len()
    }

    pub fn payload(&self) -> Ty {
        self.payload.clone()
    }

    pub fn iter(&self) -> std::slice::Iter<'_, RtVal> {
        self.values.iter()
    }

    /// A payload mismatch is a real check, not a debug assertion. The tag
    /// beside the elements is what every later read, store, and comparison
    /// trusts, so building an array whose values do not inhabit it would make
    /// the interpreter answer confidently and wrongly. It is reported as
    /// undefined behavior rather than a trap: no program the checker admits
    /// can produce it.
    fn payload_mismatch(payload: &Ty, value: &RtVal, role: &str, span: Span) -> Trap {
        Trap {
            undef: true,
            message: format!(
                "interp.array_payload_mismatch: {role} {value:?} does not inhabit the array \
                 payload `{}`",
                payload.name()
            ),
            span,
        }
    }

    fn from_values(payload: Ty, values: Vec<RtVal>, span: Span) -> IResult<RtArray> {
        for value in &values {
            if !value.inhabits(&payload) {
                return Err(RtArray::payload_mismatch(&payload, value, "element", span));
            }
        }
        Ok(RtArray { payload, values })
    }

    fn repeat(payload: Ty, value: RtVal, len: usize, span: Span) -> IResult<RtArray> {
        if !value.inhabits(&payload) {
            return Err(RtArray::payload_mismatch(
                &payload,
                &value,
                "initializer",
                span,
            ));
        }
        Ok(RtArray {
            payload,
            values: vec![value; len],
        })
    }

    fn get(&self, index: usize) -> RtVal {
        self.values[index].clone()
    }

    fn set(&mut self, index: usize, value: RtVal, span: Span) -> IResult<()> {
        if !value.inhabits(&self.payload) {
            return Err(RtArray::payload_mismatch(
                &self.payload,
                &value,
                "store value",
                span,
            ));
        }
        self.values[index] = value;
        Ok(())
    }

    /// Byte exposure is defined over integer payloads only (ADR 0026).
    fn int_values(&self) -> Option<Vec<i128>> {
        matches!(self.payload, Ty::Int(_)).then(|| {
            self.values
                .iter()
                .map(|value| match value {
                    RtVal::Int(value) => *value,
                    _ => unreachable!("checked: integer array element"),
                })
                .collect()
        })
    }

    fn set_int(&mut self, index: usize, value: i128) {
        debug_assert!(
            matches!(self.payload, Ty::Int(_)),
            "interpreter guard rejects non-integer exposure"
        );
        self.values[index] = RtVal::Int(value);
    }

    /// The monitor's snapshot of this array. `None` when an element has no
    /// specification value at all, which keeps a clause unmonitorable rather
    /// than silently guessing one.
    fn to_spec(&self) -> Option<SpecArray> {
        let values = self
            .values
            .iter()
            .map(spec_of)
            .collect::<Option<Vec<_>>>()?;
        Some(SpecArray::new(self.payload.clone(), values))
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

#[derive(Debug)]
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

#[derive(Clone)]
struct InterpLocal {
    ty: Ty,
    mutable: bool,
}

type InterpLocals = HashMap<String, InterpLocal>;

fn interp_local_ty(locals: &InterpLocals, name: &str) -> Option<Ty> {
    locals.get(name).map(|local| local.ty.clone())
}

fn require_fresh_interp_bindings(names: &[&str], locals: &InterpLocals) -> Result<(), String> {
    let mut fresh = HashSet::new();
    for name in names {
        if locals.contains_key(*name) || !fresh.insert(*name) {
            return Err(format!(
                "interp.duplicate_local: generated binding `{name}` would replace an active or sibling local"
            ));
        }
    }
    Ok(())
}

/// Raw `Program` callers need the same explicit domain boundary as normal
/// checked callers: newly executable Boolean arrays are owned locals only.
/// Integer arrays retain their established positions; Boolean arrays do not
/// acquire a parameter, return, field, borrow, or exposure ABI.
fn validate_interp_program(program: &Program) -> Result<(), String> {
    // Retained generic templates are proof artifacts and are never executed by
    // the interpreter.  They intentionally contain `Ty::Param`; validate
    // only the executable, monomorphized portion of the program.
    for function in &program.fns {
        validate_interp_fn(function)?;
    }

    for class in &program.classes {
        for field in &class.fields {
            validate_interp_class_field_ty(
                field.ty.clone(),
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
            validate_interp_field_ty(
                field.ty.clone(),
                &format!("field `{}.{}`", record.name, field.name),
            )?;
        }
    }

    Ok(())
}

fn validate_interp_fn(function: &Fn) -> Result<(), String> {
    let mut locals = HashMap::new();
    for param in &function.params {
        validate_interp_param_ty(param.ty.clone(), &format!("parameter `{}`", param.name))?;
        locals.insert(
            param.name.clone(),
            InterpLocal {
                ty: param.ty.clone(),
                mutable: false,
            },
        );
    }
    validate_interp_return_ty(
        function.ret.clone(),
        &format!("return type of `{}`", function.name),
    )?;
    validate_interp_stmts(&function.body, &mut locals)
}

/// What a result may be. A return is the other half of the call boundary
/// `validate_interp_param_ty` states, and it is a named function for the same
/// reason that one is: `docs/shape-admission.md` asks each stage gate directly,
/// and a rule spelled inline in a signature walk is a rule the table cannot see.
pub(crate) fn validate_interp_return_ty(ty: Ty, context: &str) -> Result<(), String> {
    // A *borrowed* array is what a return may not be: the callee's frame
    // stops keeping the storage it names. An owned one is precisely what a
    // return hands over (ADR 0085), payload included — `RtVal::Arr` is one
    // `Rc` whichever domain its tag names.
    if ty.as_borrow().is_some() {
        return Err(format!(
            "interp.borrow_return_unsupported: {context} is a borrow; a returned borrow would name storage the callee's frame stops keeping"
        ));
    }
    if ty.is_affine_option() {
        return Err(format!(
            "interp.affine_option_position_unsupported: {context} is ownership-bearing; affine options are supported only as explicit locals"
        ));
    }
    validate_interp_ty(ty, context)
}

/// A parameter is a value binding, so a copyable option crosses a call the
/// way it lives in a local: by value, its payload gated below. What has no
/// parameter ABI is ownership at the boundary — an affine option and an
/// owned Boolean array are refused here independently of the checker, so a
/// raw `Program` caller meets the same fence a checked program does.
fn validate_interp_param_ty(ty: Ty, context: &str) -> Result<(), String> {
    if ty.is_affine_option() {
        return Err(format!(
            "interp.affine_option_position_unsupported: {context} is ownership-bearing; `option<[bool]>` is supported only as an explicit local"
        ));
    }
    // An owner crossing here is what a move is (ADR 0085): the caller's place
    // dies at the argument, the BodyPlan frame candidate destroys what the
    // callee received after postcondition monitoring, and a borrow stays a
    // second name for storage its caller keeps.
    validate_interp_ty(ty, context)
}

/// A class field stores what a parameter binds: the value families the
/// interpreter executes, copyable options included — a stored option is an
/// `RtVal::Opt` in the object's field map like any other field value.
pub(crate) fn validate_interp_class_field_ty(ty: Ty, context: &str) -> Result<(), String> {
    // A class field stores owners a parameter cannot bind: an owned
    // Boolean array is field state exactly as an integer array is, tagged
    // in the payload-generic runtime array.
    if ty.is_owned_array_of(&Ty::Bool) {
        return Ok(());
    }
    validate_interp_param_ty(ty, context)
}

/// A stored record field is a position boundary: a record is explicit
/// layout, and an ordinary option is a value — a parameter, a return, a
/// local — that must not acquire a byte-layout ABI merely because the
/// interpreter knows how to execute it. This gate is independent of the
/// checker's record-field rules on purpose: it serves raw `Program` callers
/// as defense in depth.
pub(crate) fn validate_interp_field_ty(ty: Ty, context: &str) -> Result<(), String> {
    if matches!(ty, Ty::Option(_)) && !ty.is_affine_option() {
        return Err(format!(
            "interp.option_position_unsupported: {context} is option-valued; \
             ordinary options are supported as parameters, returns, locals, \
             and class fields, not record fields"
        ));
    }
    validate_interp_param_ty(ty, context)
}

/// Check every container payload inside a type the interpreter will execute.
///
/// A traversal: exhaustive with no wildcard, so a new constructor is a
/// compile error rather than a silently executed shape. Its leaves are the
/// payload gates below, which are allow-lists and never recurse.
pub(crate) fn validate_interp_ty(ty: Ty, context: &str) -> Result<(), String> {
    // An option whose present case owns is answered before the copyable
    // dispatch below: its payload gate is a different allow-list, and the
    // copyable one would name the wrong rule.
    if let Some(payload) = ty.as_affine_option_payload() {
        if payload.is_owned_array_of(&Ty::Bool) || matches!(payload, Ty::Class(_)) {
            return Ok(());
        }
        return Err(format!(
            "interp.affine_option_payload_unsupported: {context} has type `{}`; the supported affine options are `option<[bool]>` and `option<class>`",
            ty.name()
        ));
    }
    // A Boolean array has no clause of its own here, in either binding mode:
    // the runtime array carries its payload tag beside its elements, so
    // `.len`, an index read, and an element store are one implementation over
    // the tag, and `Ty::Bool` is an ordinary array payload below. Which
    // positions may *hold* one is decided above and by the checker.
    //
    // A borrow carries no payload of its own, so what is gated is the
    // referent's.
    validate_interp_container_payloads(ty.referent().clone(), context)
}

/// The payload rules for one type's own containers, exhaustive with no
/// wildcard so a new constructor is a compile error rather than a silently
/// executed shape.
fn validate_interp_container_payloads(ty: Ty, context: &str) -> Result<(), String> {
    match ty {
        Ty::Array(payload) => validate_interp_array_payload(&payload, context),
        Ty::Slots(_) => Err(format!(
            "interp.slots_unsupported: {context} uses owner slots, which have no interpreter value or lifecycle semantics yet"
        )),
        Ty::Option(payload) => validate_interp_option_payload(&payload, context),
        Ty::Param(_) | Ty::Int(IntTy::TParam(_)) | Ty::Raw(IntTy::TParam(_)) => Err(format!(
            "interp.type_parameter_unsupported: {context} contains an unresolved type parameter"
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

/// May the interpreter execute an array with this payload. A gate: an
/// allow-list ending in a named refusal, which never recurses.
pub(crate) fn validate_interp_array_payload(payload: &Ty, context: &str) -> Result<(), String> {
    match payload.payload_family() {
        // Record elements are RtVal::Record entries in the payload-generic
        // runtime array, honest copies in and out.
        PayloadFamily::Value | PayloadFamily::Record => Ok(()),
        // A type parameter is a proof artifact; the interpreter executes
        // only the monomorphized program, so it answers alongside the
        // unsupported families rather than the admitted one. Option
        // elements answer with them: arrays of options stay closed.
        PayloadFamily::OptionOfValue
        | PayloadFamily::Param
        | PayloadFamily::Noncanonical
        | PayloadFamily::Unsupported => Err(format!(
            "interp.aggregate_payload_unsupported: {context} has array payload `{}`; \
                 the interpreter currently executes only concrete integer and Boolean payloads",
            payload.name()
        )),
    }
}

/// May the interpreter execute a copyable option with this payload. A gate,
/// on the same terms as `validate_interp_array_payload`.
pub(crate) fn validate_interp_option_payload(payload: &Ty, context: &str) -> Result<(), String> {
    match payload.payload_family() {
        // `RtVal::Opt` is recursive and stores its payload type, so a
        // nested option executes exactly as a flat one.
        PayloadFamily::Value | PayloadFamily::OptionOfValue => Ok(()),
        PayloadFamily::Record
        | PayloadFamily::Param
        | PayloadFamily::Noncanonical
        | PayloadFamily::Unsupported => Err(format!(
            "interp.aggregate_payload_unsupported: {context} has option payload `{}`; \
                 the interpreter currently executes only concrete integer and Boolean option \
                 payloads",
            payload.name()
        )),
    }
}

fn validate_interp_stmts(stmts: &[Stmt], locals: &mut InterpLocals) -> Result<(), String> {
    for stmt in stmts {
        match stmt {
            Stmt::Decl {
                ty,
                init,
                name,
                mutable,
                ..
            } => {
                if locals.contains_key(name) {
                    return Err(format!(
                        "interp.duplicate_local: declaration `{name}` would replace an active local"
                    ));
                }
                validate_interp_ty(ty.clone(), &format!("declaration `{name}`"))?;
                if ty.is_affine_option() {
                    if !mutable {
                        return Err(format!(
                            "interp.affine_option_immutable: affine option local `{name}` must be declared `mut`"
                        ));
                    }
                    let Some(init) = init else {
                        return Err(format!(
                            "interp.affine_option_initializer: affine option local `{name}` must be initialized with `none` or `some(alloc_array<bool>(...))`"
                        ));
                    };
                    validate_affine_option_initializer(init, ty, locals, name)?;
                } else if let Some(init) = init {
                    validate_interp_expr(init, locals)?;
                    validate_interp_sink(
                        ty.clone(),
                        init,
                        locals,
                        &format!("declaration `{name}`"),
                    )?;
                } else if ty.is_array_of(&Ty::Bool) {
                    return Err(format!(
                        "interp.array_position_unsupported: Boolean array local `{name}` must be initialized by an owned literal or allocation"
                    ));
                }
                locals.insert(
                    name.clone(),
                    InterpLocal {
                        ty: ty.clone(),
                        mutable: *mutable,
                    },
                );
            }
            Stmt::Assign { name, value, .. } => {
                let destination = interp_local_ty(locals, name).ok_or_else(|| {
                    format!("interp.unknown_local: assignment to unknown local `{name}`")
                })?;
                if destination.is_affine_option() {
                    return Err(format!(
                        "interp.affine_option_assignment_unsupported: affine option `{name}` cannot be rebound"
                    ));
                }
                if destination.is_array_of(&Ty::Bool) {
                    return Err(format!(
                        "interp.array_position_unsupported: Boolean array `{name}` cannot be rebound; use an element store"
                    ));
                }
                validate_interp_sink(destination, value, locals, &format!("assignment `{name}`"))?;
            }
            Stmt::ExprStmt(value) => {
                validate_interp_expr(value, locals)?;
                reject_owned_bool_array_transport(value, locals, "expression statement")?;
            }
            Stmt::FieldAssign { value, .. } => {
                validate_interp_expr(value, locals)?;
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
                    // A return is the one boundary an owner may cross by
                    // moving (ADR 0085): `eval_moved` clears the source
                    // place, so the value leaves with the caller and the
                    // scopes unwinding behind it find nothing to destroy.
                    validate_interp_expr(value, locals)?;
                }
            }
            Stmt::Assert(_) => {}
            Stmt::VarDecl { name, init, ty, .. } => {
                if locals.contains_key(name) {
                    return Err(format!(
                        "interp.duplicate_local: declaration `{name}` would replace an active local"
                    ));
                }
                // `var t = o.take;` extracts a class payload into a fresh
                // owner; the array family keeps its typed-declaration
                // route.
                if matches!(init.kind, ExprKind::OptTake { .. })
                    && !matches!(ty, Some(Ty::Class(_)))
                {
                    return Err(
                        "interp.affine_option_take_position: `.take` must directly initialize a fresh owned local"
                            .into(),
                    );
                }
                if let Some(ty) = ty {
                    validate_interp_ty(ty.clone(), &format!("inferred declaration `{name}`"))?;
                }
                validate_interp_expr(init, locals)?;
                let inferred = ty.clone().or(init.ty.clone()).ok_or_else(|| {
                    format!("interp.missing_type: inferred declaration `{name}` has no type")
                })?;
                validate_interp_sink(
                    inferred.clone(),
                    init,
                    locals,
                    &format!("declaration `{name}`"),
                )?;
                if inferred.is_affine_option() {
                    return Err(format!(
                        "interp.affine_option_position_unsupported: inferred declaration `{name}` cannot own an affine option; write an explicit `option<[bool]>` declaration"
                    ));
                }
                locals.insert(
                    name.clone(),
                    InterpLocal {
                        ty: inferred,
                        mutable: true,
                    },
                );
            }
            Stmt::FieldStore { index, value, .. } => {
                validate_interp_sink(
                    Ty::Int(IntTy::U64),
                    index,
                    locals,
                    "array field store index",
                )?;
                validate_interp_expr(value, locals)?;
                reject_owned_bool_array_transport(value, locals, "array field store")?;
            }
            Stmt::Store {
                array,
                index,
                value,
                ..
            } => {
                let array_ty = interp_local_ty(locals, array).ok_or_else(|| {
                    format!("interp.unknown_local: store names unknown array `{array}`")
                })?;
                let Some((payload, _)) = array_ty.as_array() else {
                    return Err(format!(
                        "interp.not_array: store target `{array}` is not an array"
                    ));
                };
                let payload = payload.clone();
                validate_interp_array_payload(&payload, &format!("store target `{array}`"))?;
                validate_interp_sink(Ty::Int(IntTy::U64), index, locals, "array store index")?;
                validate_interp_sink(payload, value, locals, "array store value")?;
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
                match interp_local_ty(locals, array) {
                    Some(ref owning) if owning.is_affine_option() => {
                        return Err(format!(
                            "interp.affine_option_position_unsupported: affine option `{array}` cannot be an exposure source"
                        ));
                    }
                    Some(ref found) if found.is_array_of(&Ty::Bool) => {
                        return Err(format!(
                            "interp.array_position_unsupported: exposure of Boolean array `{array}`; Boolean arrays are safe owned locals only"
                        ));
                    }
                    Some(ref found) if matches!(found.as_array(), Some((Ty::Int(integer), _)) if !matches!(integer, IntTy::TParam(_))) =>
                        {}
                    _ => {
                        return Err(format!(
                            "interp.not_array: exposure source `{array}` is not an executable integer array"
                        ));
                    }
                }
                require_fresh_interp_bindings(&[ptr, res], locals)?;
                let mut body_locals = locals.clone();
                body_locals.insert(
                    ptr.clone(),
                    InterpLocal {
                        ty: Ty::Raw(IntTy::U8),
                        mutable: false,
                    },
                );
                body_locals.insert(
                    res.clone(),
                    InterpLocal {
                        ty: Ty::Res(ResKind::RawSpan),
                        mutable: false,
                    },
                );
                validate_interp_stmts(body, &mut body_locals)?;
            }
            Stmt::StaticAlloc { size, ptr, res, .. } => {
                validate_interp_sink(Ty::Int(IntTy::U64), size, locals, "static allocation size")?;
                require_fresh_interp_bindings(&[ptr, res], locals)?;
                locals.insert(
                    ptr.clone(),
                    InterpLocal {
                        ty: Ty::Raw(IntTy::U8),
                        mutable: false,
                    },
                );
                locals.insert(
                    res.clone(),
                    InterpLocal {
                        ty: Ty::Res(ResKind::RawSpan),
                        mutable: false,
                    },
                );
            }
            Stmt::SystemAlloc {
                size,
                ptr,
                res,
                release,
                ..
            } => {
                validate_interp_sink(Ty::Int(IntTy::U64), size, locals, "system allocation size")?;
                require_fresh_interp_bindings(&[ptr, res, release], locals)?;
                locals.insert(
                    ptr.clone(),
                    InterpLocal {
                        ty: Ty::Raw(IntTy::U8),
                        mutable: false,
                    },
                );
                locals.insert(
                    res.clone(),
                    InterpLocal {
                        ty: Ty::Res(ResKind::RawSpan),
                        mutable: false,
                    },
                );
                locals.insert(
                    release.clone(),
                    InterpLocal {
                        ty: Ty::Res(ResKind::SystemDealloc),
                        mutable: false,
                    },
                );
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

fn validate_affine_option_initializer(
    init: &Expr,
    declared: &Ty,
    locals: &InterpLocals,
    name: &str,
) -> Result<(), String> {
    require_cached_type(init, declared.clone(), "affine option initializer")?;
    let payload = declared
        .as_affine_option_payload()
        .cloned()
        .expect("checked: affine option declaration");
    match &init.kind {
        ExprKind::NoneE => Ok(()),
        ExprKind::SomeE(inner)
            if matches!(inner.kind, ExprKind::AllocArray { elem: Ty::Bool, .. }) =>
        {
            validate_interp_expr(inner, locals)?;
            require_cached_type(inner, Ty::array(Ty::Bool), "affine option payload")
        }
        ExprKind::SomeE(inner)
            if matches!(payload, Ty::Class(_))
                && matches!(inner.kind, ExprKind::CtorCall { .. } | ExprKind::Var(_)) =>
        {
            validate_interp_expr(inner, locals)?;
            require_cached_type(inner, payload, "affine option payload")
        }
        _ => Err(format!(
            "interp.affine_option_initializer: affine option local `{name}` must be initialized with `none`, `some(alloc_array<bool>(...))`, or `some(<class value>)`"
        )),
    }
}

fn validate_interp_expr(expr: &Expr, locals: &InterpLocals) -> Result<(), String> {
    if let ExprKind::SlotOp { op, .. } = &expr.kind {
        return Err(format!(
            "interp.slots_unsupported: `{}` has no interpreter semantics yet",
            op.name()
        ));
    }
    if let Some(ty) = &expr.ty {
        validate_interp_ty(ty.clone(), "expression annotation")?;
    }
    // The producers of an *owner* are enumerated, because an owner has to
    // come from somewhere the destruction rules know about. A borrowed
    // Boolean array is not produced at all — it names storage that already
    // exists — so it is no more restricted here than `&[T]` is.
    if expr
        .ty
        .as_ref()
        .is_some_and(|ty| ty.is_owned_array_of(&Ty::Bool))
        && !matches!(
            expr.kind,
            ExprKind::ArrayLit(_)
                | ExprKind::AllocArray { .. }
                | ExprKind::OptTake { .. }
                | ExprKind::Var(_)
                // A verified callee hands its owner over (ADR 0085), so a
                // call result is storage the destruction rules already know
                // about: the callee's frame stopped owning it at the return.
                | ExprKind::Call { .. }
        )
    {
        return Err(
            "interp.array_position_unsupported: only owned Boolean array literals, allocations, and their local places are executable"
                .into(),
        );
    }

    match &expr.kind {
        ExprKind::SlotOp { .. } => {
            unreachable!("slot operations are refused before cached annotation validation")
        }
        ExprKind::Index { array, index, .. } => {
            let array_ty = interp_local_ty(locals, array).ok_or_else(|| {
                format!("interp.unknown_local: index names unknown array `{array}`")
            })?;
            let Some((payload, _)) = array_ty.as_array() else {
                return Err(format!(
                    "interp.not_array: indexed local `{array}` is not an array"
                ));
            };
            let payload = payload.clone();
            validate_interp_sink(Ty::Int(IntTy::U64), index, locals, "array index")?;
            validate_interp_array_payload(&payload, &format!("indexed array `{array}`"))?;
            require_cached_type(expr, payload, "array index result")?;
        }
        ExprKind::AllocArray { elem, len, init } => {
            validate_interp_array_payload(elem, "alloc_array")?;
            let expected = Ty::Array(Box::new(elem.clone()));
            require_cached_type(expr, expected, "alloc_array result")?;
            validate_interp_sink(Ty::Int(IntTy::U64), len, locals, "alloc_array length")?;
            validate_interp_sink(elem.clone(), init, locals, "alloc_array initializer")?;
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
            // An ordinary call is where an owner is handed over (ADR 0085);
            // a constructor argument keeps the refusal, and the checker
            // closes that boundary in its own name (`type.member_param`).
            let hands_over = matches!(expr.kind, ExprKind::Call { .. });
            for arg in args {
                validate_interp_expr(arg, locals)?;
                if !hands_over {
                    reject_owned_bool_array_transport(arg, locals, "call argument")?;
                }
            }
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
            let operand_ty = semantic_interp_ty(operand, locals)?;
            if operand_ty.is_affine_option() {
                let ExprKind::Var(name) = &operand.kind else {
                    return Err(
                        "interp.affine_option_temporary: `.is_some` on an affine option requires a named local"
                            .into(),
                    );
                };
                if !interp_local_ty(locals, name).is_some_and(|ty| ty.is_affine_option()) {
                    return Err(format!(
                        "interp.affine_option_payload_unsupported: `{name}` is not an executable owning-option local"
                    ));
                }
            } else {
                validate_interp_expr(operand, locals)?;
            }
            if !matches!(operand_ty, Ty::Option(_) | Ty::OptionRaw(_)) {
                return Err(format!(
                    "interp.option_operand: `.is_some` needs an option, found `{}`",
                    operand_ty.name()
                ));
            }
            require_cached_type(expr, Ty::Bool, "`.is_some` result")?;
        }
        ExprKind::OptValue { operand } => {
            let operand_ty = semantic_interp_ty(operand, locals)?;
            if operand_ty.is_affine_option() {
                return Err(
                    "interp.affine_option_value_unsupported: an owning option has no copying `.value`; use `.take`"
                        .into(),
                );
            }
            validate_interp_expr(operand, locals)?;
            let result_ty = option_value_ty(operand_ty.clone()).ok_or_else(|| {
                format!(
                    "interp.option_operand: `.value` needs an option, found `{}`",
                    operand_ty.name()
                )
            })?;
            require_cached_type(expr, result_ty, "`.value` result")?;
        }
        ExprKind::SomeE(operand) => {
            if expr.ty.as_ref().is_some_and(Ty::is_affine_option) {
                return Err(
                    "interp.affine_option_temporary: affine `some(...)` is valid only as an explicit local initializer"
                        .into(),
                );
            }
            validate_interp_expr(operand, locals)?;
            reject_owned_bool_array_transport(operand, locals, "option payload")?;
        }
        ExprKind::OptTake {
            option,
            option_span: _,
        } => {
            let local = locals.get(option).ok_or_else(|| {
                format!("interp.unknown_local: `.take` names unknown local `{option}`")
            })?;
            if !local.ty.is_affine_option() {
                return Err(format!(
                    "interp.option_operand: `.take` needs an owning option, found `{}`",
                    local.ty.clone().name()
                ));
            }
            if !local.mutable {
                return Err(format!(
                    "interp.affine_option_immutable: `.take` needs mutable local `{option}`"
                ));
            }
            let payload = local
                .ty
                .as_affine_option_payload()
                .cloned()
                .expect("checked: owning-option local");
            require_cached_type(expr, payload, "affine option take result")?;
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
                reject_owned_bool_array_transport(arg, locals, "operation argument")?;
            }
            reject_bool_array_result(expr, "operation result")?;
        }
        ExprKind::MethodCall { recv, args, .. } => {
            reject_bool_array_named_receiver(recv, locals, "method receiver")?;
            for arg in args {
                validate_interp_expr(arg, locals)?;
                reject_owned_bool_array_transport(arg, locals, "method argument")?;
            }
            reject_bool_array_result(expr, "method result")?;
        }
        ExprKind::ArrayLit(elements) => {
            let Some(Ty::Array(ref payload)) = expr.ty else {
                return Err(
                    "interp.array_literal_type: array literal must have an owned array annotation"
                        .into(),
                );
            };
            validate_interp_array_payload(payload, "array literal")?;
            for element in elements {
                validate_interp_sink(
                    (**payload).clone(),
                    element,
                    locals,
                    "array literal element",
                )?;
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
            let ty = interp_local_ty(locals, name).ok_or_else(|| {
                format!("interp.unknown_local: expression names unknown local `{name}`")
            })?;
            if ty.is_affine_option() {
                return Err(format!(
                    "interp.affine_option_transport_unsupported: affine option local `{name}` cannot be copied or moved as an expression"
                ));
            }
            if let Some(cached) = &expr.ty {
                if *cached != ty && !ty.clone().is_resource() {
                    return Err(format!(
                        "interp.expression_type: local `{name}` has type `{}` but its expression is annotated `{}`",
                        ty.name(),
                        cached.name()
                    ));
                }
            }
        }
        ExprKind::Len { array } => {
            if interp_local_ty(locals, array).is_none_or(|ty| ty.as_array().is_none()) {
                return Err(format!(
                    "interp.unknown_local: length names unknown or non-array local `{array}`"
                ));
            }
            require_cached_type(expr, Ty::Int(IntTy::U64), "array length")?;
        }
        ExprKind::NoneE => {
            if expr.ty.as_ref().is_some_and(Ty::is_affine_option) {
                return Err(
                    "interp.affine_option_temporary: affine `none` is valid only as an explicit local initializer"
                        .into(),
                );
            }
        }
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
            if interp_local_ty(locals, array).is_some_and(|ty| ty.is_affine_option()) {
                return Err(format!(
                    "interp.affine_option_position_unsupported: affine option `{array}` cannot be borrowed"
                ));
            }
        }
    }
    Ok(())
}

/// The type of the value an option's present case holds.
///
/// This one genuinely lowers: a `raw<Record>` option is a nullable pointer,
/// so its present case has type `raw<Record>` and not the option's own type.
/// An ordinary option's present case is its payload, admitted by the same
/// gate that admits the option itself.
pub(crate) fn option_value_ty(option: Ty) -> Option<Ty> {
    match option {
        Ty::Option(payload) => validate_interp_option_payload(&payload, "option value")
            .ok()
            .map(|()| *payload),
        Ty::OptionRaw(record) => Some(Ty::RawRecord(record)),
        _ => None,
    }
}

fn reject_bool_array_named_receiver(
    name: &str,
    locals: &InterpLocals,
    context: &str,
) -> Result<(), String> {
    if interp_local_ty(locals, name).is_some_and(|ty| ty.is_affine_option()) {
        return Err(format!(
            "interp.affine_option_position_unsupported: {context} `{name}` is an affine option, not an object"
        ));
    }
    if interp_local_ty(locals, name).is_some_and(|ty| ty.is_array_of(&Ty::Bool)) {
        return Err(format!(
            "interp.array_position_unsupported: {context} `{name}` is a Boolean array, not an object"
        ));
    }
    Ok(())
}

fn require_cached_type(expr: &Expr, expected: Ty, context: &str) -> Result<(), String> {
    if expr.ty == Some(expected.clone()) {
        Ok(())
    } else {
        Err(format!(
            "interp.expression_type: {context} must have type `{}`, found `{}`",
            expected.name(),
            expr.ty
                .clone()
                .map_or_else(|| "<missing>".into(), |arg0: ast::Ty| Ty::name(&arg0))
        ))
    }
}

fn semantic_interp_ty(expr: &Expr, locals: &InterpLocals) -> Result<Ty, String> {
    match &expr.kind {
        ExprKind::BoolLit(_) => Ok(Ty::Bool),
        ExprKind::IntLit(_) => match &expr.ty {
            Some(ty @ Ty::Int(integer)) if !matches!(integer, IntTy::TParam(_)) => Ok(ty.clone()),
            _ => Err("interp.literal_type: integer literal lacks a concrete integer type".into()),
        },
        ExprKind::Var(name) => interp_local_ty(locals, name).ok_or_else(|| {
            format!("interp.unknown_local: expression names unknown local `{name}`")
        }),
        ExprKind::Index { array, .. } => match interp_local_ty(locals, array) {
            Some(ref found) if found.as_array().is_some() => {
                let payload = found
                    .as_array()
                    .expect("the arm's guard already matched this shape")
                    .0
                    .clone();
                validate_interp_array_payload(&payload, &format!("indexed local `{array}`"))?;
                Ok(payload)
            }
            _ => Err(format!(
                "interp.not_array: indexed local `{array}` is not an array"
            )),
        },
        ExprKind::Len { .. } => Ok(Ty::Int(IntTy::U64)),
        ExprKind::AllocArray { elem, .. } => Ok(Ty::Array(Box::new(elem.clone()))),
        ExprKind::ArrayLit(_) => expr
            .ty
            .clone()
            .ok_or_else(|| "interp.array_literal_type: missing array literal type".into()),
        ExprKind::Unary { op, .. } => match op {
            UnOp::Not => Ok(Ty::Bool),
            UnOp::Neg => expr
                .ty
                .clone()
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
            .clone()
            .ok_or_else(|| "interp.expression_type: expression has no cached type".into()),
    }
}

fn validate_interp_sink(
    expected: Ty,
    expr: &Expr,
    locals: &InterpLocals,
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
    if expected.is_owned_array_of(&Ty::Bool)
        && !matches!(
            expr.kind,
            ExprKind::ArrayLit(_)
                | ExprKind::AllocArray { .. }
                | ExprKind::OptTake { .. }
                // A call hands its owner over at the return (ADR 0085), so
                // the value this declaration receives is storage nothing
                // else still names.
                | ExprKind::Call { .. }
        )
    {
        return Err(format!(
            "interp.array_position_unsupported: {context} receives an owned Boolean array through an unsupported transport; only owned literals, allocations, and handed-over call results are executable"
        ));
    }
    Ok(())
}

/// Reject an *owned* Boolean array crossing a boundary that would give a
/// second place a claim on the same storage. Lending one is not that: a
/// borrow hands over a name, and only an owning type receives a BodyPlan frame
/// cleanup candidate, so `&[bool]` crosses a call boundary exactly as `&[T]`
/// does.
fn reject_owned_bool_array_transport(
    expr: &Expr,
    locals: &InterpLocals,
    context: &str,
) -> Result<(), String> {
    // Checked affine-resource places deliberately may have no cached `Expr.ty`:
    // their sealed operand position is the typing authority.  This guard only
    // needs to recognize Boolean-array transport, so do not demand unrelated
    // scalar/resource metadata here.  Named locals are resolved from the
    // active environment to prevent a forged cache from hiding an array.
    let transports_owned_bool_array = match &expr.kind {
        ExprKind::Var(name) => {
            interp_local_ty(locals, name).is_some_and(|ty| ty.is_owned_array_of(&Ty::Bool))
        }
        _ => expr
            .ty
            .as_ref()
            .is_some_and(|ty| ty.is_owned_array_of(&Ty::Bool)),
    };
    if transports_owned_bool_array {
        return Err(format!(
            "interp.array_position_unsupported: {context} transports an owned Boolean array; an owned Boolean array is a local value"
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
    locals: &InterpLocals,
    context: &str,
) -> Result<(), String> {
    let is_bool_array = expr.ty.as_ref().is_some_and(|ty| ty.is_array_of(&Ty::Bool))
        || matches!(
            &expr.kind,
            ExprKind::Var(name)
                if interp_local_ty(locals, name).is_some_and(|ty| ty.is_array_of(&Ty::Bool))
        );
    if is_bool_array {
        return Err(format!(
            "interp.array_position_unsupported: {context} cannot receive a Boolean array"
        ));
    }
    Ok(())
}

fn reject_bool_array_result(expr: &Expr, context: &str) -> Result<(), String> {
    if expr.ty.as_ref().is_some_and(|ty| ty.is_array_of(&Ty::Bool)) {
        return Err(format!(
            "interp.array_position_unsupported: {context} is a Boolean array; only owned literal/allocation results are permitted"
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
        ty.res_kind(),
        Some(ResKind::ResourceMapPointsToU64) | Some(ResKind::ResourceMapPointsToRecord(_))
    )
}

#[cfg(test)]
pub fn run_tests(program: &Program, mods: &crate::modules::ModuleSet) -> Vec<TestReport> {
    let control = match ControlProgram::build(program) {
        Ok(control) => control,
        Err(error) => return control_failure_reports(program, control_plan_message(error)),
    };
    run_tests_with_control(program, mods, &control)
}

pub(crate) fn run_checked_tests(
    checked: &crate::CheckedProgram,
    mods: &crate::modules::ModuleSet,
) -> Vec<TestReport> {
    run_tests_with_control(checked.program(), mods, checked.control())
}

fn control_failure_reports(program: &Program, error: String) -> Vec<TestReport> {
    program
        .fns
        .iter()
        .filter(|function| function.name.starts_with("test_"))
        .map(|function| TestReport {
            name: function.name.clone(),
            outcome: Err(error.clone()),
            skipped: Vec::new(),
        })
        .collect()
}

fn run_tests_with_control(
    program: &Program,
    mods: &crate::modules::ModuleSet,
    control: &ControlProgram,
) -> Vec<TestReport> {
    if let Err(error) = validate_interp_program(program) {
        return control_failure_reports(program, error);
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
                control,
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

/// Execute a deliberately unsealed AST for focused interpreter unit probes.
///
/// This is compiled only with the library's own unit tests. Integration and
/// production callers must enter through a [`crate::CheckedProgram`] or
/// [`crate::VerifiedProgram`], so they cannot rebuild structural control from
/// a raw AST.
#[cfg(test)]
fn run_unchecked_fn(
    program: &Program,
    mods: &crate::modules::ModuleSet,
    name: &str,
) -> Result<RtVal, String> {
    run_unchecked_fn_observed(program, mods, name).outcome
}

/// Execute a function using the exact control plan sealed by the checker.
pub fn run_checked_fn(
    checked: &crate::CheckedProgram,
    mods: &crate::modules::ModuleSet,
    name: &str,
) -> Result<RtVal, String> {
    run_fn_observed_with_control(checked.program(), mods, name, checked.control()).outcome
}

/// Execute a function using the control plan that travelled through Lean
/// verification with the exact typed AST.
pub fn run_verified_fn(
    verified: &crate::VerifiedProgram,
    mods: &crate::modules::ModuleSet,
    name: &str,
) -> Result<RtVal, String> {
    run_fn_observed_with_control(verified.program(), mods, name, verified.control()).outcome
}

#[cfg(test)]
fn run_unchecked_fn_observed(
    program: &Program,
    mods: &crate::modules::ModuleSet,
    name: &str,
) -> ObservedRun {
    let control = match ControlProgram::build(program) {
        Ok(control) => control,
        Err(error) => {
            return ObservedRun {
                outcome: Err(control_plan_message(error)),
                mmio: Vec::new(),
                uart_profile: None,
                uart_cursor: 0,
            };
        }
    };
    run_fn_observed_with_control(program, mods, name, &control)
}

pub fn run_checked_fn_observed(
    checked: &crate::CheckedProgram,
    mods: &crate::modules::ModuleSet,
    name: &str,
) -> ObservedRun {
    run_fn_observed_with_control(checked.program(), mods, name, checked.control())
}

fn run_fn_observed_with_control(
    program: &Program,
    mods: &crate::modules::ModuleSet,
    name: &str,
    control: &ControlProgram,
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
        control,
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
    control: &'a ControlProgram,
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
    #[cfg(test)]
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

/// Dynamic activation state for one shared lexical control plan.
///
/// The plan owns candidate identity and exit ordering. The interpreter still
/// owns the dynamic question: a declaration is reached on this run, and a
/// moved place may be empty by the time its candidate is visited.
struct ExecutionControl<'a> {
    plan: &'a BodyPlan,
    reached: HashSet<DropId>,
}

#[derive(Clone, Copy)]
struct TrapContext<'a> {
    plan: &'a BodyPlan,
    scope: ScopeId,
}

impl<'a> TrapContext<'a> {
    const fn new(plan: &'a BodyPlan, scope: ScopeId) -> Self {
        Self { plan, scope }
    }

    fn consume_expression(self, expression: &Expr) -> IResult<()> {
        let sites = self
            .plan
            .expression_trap_sites(self.scope, expression)
            .map_err(control_plan_trap)?;
        consume_trap_sites(&sites, Some(self.scope))
    }

    fn consume_statement(self, statement: &Stmt) -> IResult<()> {
        let sites = self
            .plan
            .statement_trap_sites(self.scope, statement)
            .map_err(control_plan_trap)?;
        consume_trap_sites(&sites, None)
    }
}

fn consume_trap_sites(sites: &[&TrapSite], expected_scope: Option<ScopeId>) -> IResult<()> {
    for site in sites {
        let route = site.route();
        if expected_scope.is_some_and(|scope| site.scope() != scope)
            || route.kind() != crate::control::ExitKind::Trap
            || !route.scopes().is_empty()
            || !route.clears().is_empty()
            || !route.drops().is_empty()
        {
            return Err(Trap {
                undef: true,
                message: "internal trap site does not abort through the empty no-unwind route"
                    .into(),
                span: site.span(),
            });
        }
    }
    Ok(())
}

impl<'a> ExecutionControl<'a> {
    fn new(plan: &'a BodyPlan) -> Self {
        Self {
            plan,
            reached: HashSet::new(),
        }
    }

    fn arm(&mut self, name: &str, scope: ScopeId, span: Span) -> IResult<()> {
        let place = Place::local(name);
        let Some(candidate) = self.plan.candidate_for_place(&place) else {
            return Ok(());
        };
        if candidate.scope() != scope {
            return Err(Trap {
                undef: true,
                message: format!(
                    "internal control plan assigned `{name}` to a different lexical scope"
                ),
                span,
            });
        }
        self.reached.insert(candidate.id());
        Ok(())
    }
}

fn control_plan_trap(error: PlanError) -> Trap {
    Trap {
        undef: true,
        message: control_plan_message(error.clone()),
        span: error.span,
    }
}

fn control_plan_message(error: PlanError) -> String {
    format!(
        "internal control plan rejected the checked body: {}",
        error.message
    )
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
        let owner = CallOwner::Function(f.name.clone());
        let control_body = self
            .control
            .body(&owner, f.span)
            .map_err(control_plan_trap)?;
        control_body
            .validate_callable(f.span, &f.params, &f.body)
            .map_err(control_plan_trap)?;
        let plan = control_body.plan();
        let mut control = ExecutionControl::new(plan);
        let mut frame = Frame {
            vars: HashMap::new(),
            entry_scalars: HashMap::new(),
            olds: HashMap::new(),
            self_ctx: None,
        };
        for (p, v) in f
            .params
            .iter()
            .filter(|p| !p.ty.clone().is_resource() || has_resource_shadow(p.ty.clone()))
            .zip(args)
        {
            match (&v, p.ty.clone()) {
                (RtVal::Arr(a), ty) if ty.is_unique_borrow() => {
                    if let Some(snapshot) = a.borrow().to_spec() {
                        frame.olds.insert(p.name.clone(), SpecVal::Arr(snapshot));
                    }
                }
                // `&mut C`: the borrow shares storage with the caller, so
                // the bare name reads the current state and `old p` needs
                // the value it had at entry. `spec_of` copies.
                (obj @ RtVal::Obj { .. }, ty) if ty.is_unique_borrow() => {
                    if let Some(sv) = spec_of(obj) {
                        frame.olds.insert(p.name.clone(), sv);
                    }
                }
                // An *owned* array parameter was handed over, so the callee
                // may hand it on again and leave its place empty — and a
                // contract still speaks about a moved-from parameter (ADR
                // 0030). The entry copy is deep rather than the `Rc`,
                // because an entry value is what it was at entry whatever
                // becomes of the storage. A borrowed array keeps the
                // established convention: clauses read current contents, and
                // `old p` is the snapshot taken above.
                (array @ RtVal::Arr(_), ty) if matches!(ty, Ty::Array(_)) => {
                    frame.entry_scalars.insert(p.name.clone(), deep_copy(array));
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
            if p.ty.clone().is_resource() && !has_resource_shadow(p.ty.clone()) {
                frame.vars.insert(p.name.clone(), RtVal::Unit);
            }
            control.arm(&p.name, plan.frame_scope(), p.span)?;
        }

        for pre in &f.pres {
            self.check_clause(&frame, pre, None, &format!("pre of `{}`", f.name))?;
        }

        let flow = self.exec_body(&f.body, &mut frame, &mut control)?;
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
        let frame_exit = plan.implicit_return().frame().clone();
        self.cleanup_route(&frame_exit, &mut frame, &mut control)?;
        Ok(result)
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

    /// Run one lexical scope using the shared plan's candidate order.
    ///
    /// A normal close consumes the scope's fallthrough/backedge route. An
    /// explicit return already consumed its complete lexical route at the
    /// return site. Rust error propagation intentionally consumes neither:
    /// Sable traps abort without unwinding.
    fn exec_body(
        &mut self,
        stmts: &[Stmt],
        frame: &mut Frame,
        control: &mut ExecutionControl<'_>,
    ) -> IResult<Flow> {
        let block = control.plan.body_block().id();
        let normal_exit = control
            .plan
            .body_block()
            .flow()
            .can_fall_through()
            .then(|| control.plan.implicit_return().lexical().clone());
        self.exec_block(stmts, frame, control, block, normal_exit)
    }

    fn exec_block(
        &mut self,
        stmts: &[Stmt],
        frame: &mut Frame,
        control: &mut ExecutionControl<'_>,
        block: BlockId,
        normal_exit: Option<ExitRoute>,
    ) -> IResult<Flow> {
        let (can_fall_through, anchor) = {
            let planned = control.plan.block(block);
            (planned.flow().can_fall_through(), planned.anchor())
        };
        if can_fall_through != normal_exit.is_some() {
            return Err(control_plan_trap(PlanError {
                span: anchor,
                message: "retained block fallthrough disagrees with its normal exit route".into(),
            }));
        }
        let out = self.exec_stmts(stmts, frame, control, block)?;
        if let Flow::Normal = out {
            let Some(route) = normal_exit.as_ref() else {
                return Err(control_plan_trap(PlanError {
                    span: anchor,
                    message: "non-fallthrough retained block completed normally".into(),
                }));
            };
            self.cleanup_route(route, frame, control)?;
        }
        Ok(out)
    }

    /// Run a block whose declarations belong to the *enclosing* scope.
    ///
    /// `unsafe { ... }` is a marker, not a scope: the checker keeps its locals
    /// in the enclosing lifetime (ADR 0026), so they must not be destroyed at
    /// this closing brace. An exposure body is the opposite case and runs
    /// through `exec_block`, because closing the loan is a lexical lifetime.
    fn exec_open_block(
        &mut self,
        stmts: &[Stmt],
        frame: &mut Frame,
        control: &mut ExecutionControl<'_>,
        block: BlockId,
    ) -> IResult<Flow> {
        self.exec_stmts(stmts, frame, control, block)
    }

    fn exec_stmts(
        &mut self,
        stmts: &[Stmt],
        frame: &mut Frame,
        control: &mut ExecutionControl<'_>,
        block: BlockId,
    ) -> IResult<Flow> {
        let (scope, anchor, planned) = {
            let block = control.plan.block(block);
            (block.scope(), block.anchor(), block.statements().to_vec())
        };
        if planned.len() != stmts.len() {
            return Err(control_plan_trap(PlanError {
                span: anchor,
                message: "runtime block length disagrees with its retained block plan".into(),
            }));
        }
        let mut out = Flow::Normal;
        for (stmt, statement) in stmts.iter().zip(planned) {
            if !statement.entry_reachable() {
                return Err(control_plan_trap(PlanError {
                    span: stmt_span(stmt),
                    message: "runtime reached a statement sealed as structurally unreachable"
                        .into(),
                }));
            }
            let flow = self.exec_stmt(stmt, statement.kind(), frame, control, scope)?;
            if let Stmt::VarDecl {
                name, name_span, ..
            }
            | Stmt::Decl {
                name, name_span, ..
            } = stmt
            {
                // A declaration that completed on this dynamic path arms its
                // candidate. Uninitialized owning places are still armed: a
                // later assignment may install a value, while `drop_place`
                // remains the authority for whether one is present.
                control.arm(name, scope, *name_span)?;
            }
            match flow {
                Flow::Normal => {}
                ret => {
                    out = ret;
                    break;
                }
            }
        }
        Ok(out)
    }

    fn cleanup_route(
        &mut self,
        route: &ExitRoute,
        frame: &mut Frame,
        control: &mut ExecutionControl<'_>,
    ) -> IResult<()> {
        // Resolve the complete route before mutating the frame. This both
        // keeps an invalid shared plan from performing a partial cleanup and
        // lets recursive destructor execution mutably borrow the interpreter
        // without retaining a borrow into the plan.
        let drops = route
            .drops()
            .iter()
            .filter(|drop| control.reached.contains(drop))
            .map(|drop| {
                let candidate = control.plan.candidate(*drop);
                if !candidate.place().is_root() {
                    return Err(Trap {
                        undef: true,
                        message: format!(
                            "internal lexical cleanup candidate `{}` is not a local",
                            candidate.place().render()
                        ),
                        span: candidate.span(),
                    });
                }
                Ok((
                    *drop,
                    candidate.place().root().to_owned(),
                    candidate.drop_action().clone(),
                    candidate.span(),
                ))
            })
            .collect::<IResult<Vec<_>>>()?;
        let clears = route
            .clears()
            .iter()
            .map(|place| {
                if !place.is_root() {
                    return Err(Trap {
                        undef: true,
                        message: format!(
                            "internal lexical clear `{}` is not a local",
                            place.render()
                        ),
                        span: Span::new(0, 0),
                    });
                }
                Ok(place.root().to_owned())
            })
            .collect::<IResult<Vec<_>>>()?;

        // A drop consumes an owning value before the binding itself dies.
        // Non-owning locals, moved-from owners, and erased proof bindings are
        // then cleared by the same normalized route rather than by
        // statement-specific cleanup code.
        for (drop, name, action, span) in drops {
            if let Some(held) = self.take_place(&RtPlace::Local(name.clone()), frame) {
                self.drop_runtime_value_with_action(held, &action, &name, span)?;
            }
            control.reached.remove(&drop);
        }
        for name in clears {
            frame.vars.remove(name.as_str());
        }
        Ok(())
    }

    #[cfg(test)]
    fn exec_test_block(&mut self, stmts: &[Stmt], frame: &mut Frame) -> IResult<Flow> {
        let owner_span = Span::new(usize::MAX - 1, usize::MAX);
        let plan = BodyPlan::build(
            CallOwner::Function("__interpreter_block_probe".into()),
            owner_span,
            &[],
            stmts,
        )
        .map_err(control_plan_trap)?;
        let mut control = ExecutionControl::new(&plan);
        self.exec_body(stmts, frame, &mut control)
    }

    #[cfg(test)]
    fn exec_test_stmt(&mut self, stmt: &Stmt, frame: &mut Frame) -> IResult<Flow> {
        let owner_span = Span::new(usize::MAX - 1, usize::MAX);
        let body = std::slice::from_ref(stmt);
        let plan = BodyPlan::build(
            CallOwner::Function("__interpreter_statement_probe".into()),
            owner_span,
            &[],
            body,
        )
        .map_err(control_plan_trap)?;
        let mut control = ExecutionControl::new(&plan);
        let statement = plan.body_block().statements()[0].kind();
        self.exec_stmt(stmt, statement, frame, &mut control, plan.body_scope())
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
    #[cfg(test)]
    fn drop_place(&mut self, place: &RtPlace, frame: &mut Frame) -> IResult<()> {
        enum OwnedDrop {
            Object(usize, Rc<RefCell<HashMap<String, RtVal>>>),
            Plain,
            None,
        }

        let owned = match place {
            RtPlace::Local(name) => match frame.vars.get(name.as_str()) {
                Some(RtVal::Obj { class, fields }) => OwnedDrop::Object(*class, fields.clone()),
                // A present class payload dies with its option, through the
                // class's own destructor path — exactly once, because the
                // whole option leaves the place before the deinit runs.
                Some(RtVal::AffineOptClass {
                    class,
                    value: Some(fields),
                }) => OwnedDrop::Object(*class, fields.clone()),
                Some(
                    RtVal::Arr(_)
                    | RtVal::AffineOptBoolArray(_)
                    | RtVal::AffineOptClass { value: None, .. },
                ) => OwnedDrop::Plain,
                _ => OwnedDrop::None,
            },
            RtPlace::SelfField(field) => match frame.self_ctx.as_ref().and_then(|(_, fields)| {
                let fields = fields.borrow();
                match fields.get(field.as_str()) {
                    Some(RtVal::Obj { class, fields }) => {
                        Some(OwnedDrop::Object(*class, fields.clone()))
                    }
                    Some(RtVal::AffineOptClass {
                        class,
                        value: Some(fields),
                    }) => Some(OwnedDrop::Object(*class, fields.clone())),
                    Some(
                        RtVal::Arr(_)
                        | RtVal::AffineOptBoolArray(_)
                        | RtVal::AffineOptClass { value: None, .. },
                    ) => Some(OwnedDrop::Plain),
                    _ => None,
                }
            }) {
                Some(owned) => owned,
                None => OwnedDrop::None,
            },
        };
        match owned {
            OwnedDrop::Object(class, fields) => {
                // Out of its place *before* the destructor runs: a `deinit`
                // that reached the dying value through its own name would
                // see a value that no longer belongs to anyone.
                self.take_place(place, frame);
                self.drop_value(class, &fields, &place.name())
            }
            OwnedDrop::Plain => {
                // Arrays, array-payload affine options, and absent options
                // have no destructor to run, but an owned local still dies
                // at its lexical boundary. A class-payload option that is
                // present routes Object-style above instead: its payload
                // carries a destructor. This is a drop, not a move; a value
                // transferred through `eval_moved` or `.take` has already
                // left its source place.
                self.take_place(place, frame);
                Ok(())
            }
            OwnedDrop::None => Ok(()),
        }
    }

    /// The source place of an expression, if it names one. A call or a
    /// constructor is already a temporary: it has no source to clear.
    ///
    /// The two roots here are the two the program language can name as an
    /// ownership source, and they are the roots of the checker's `Place`.
    fn source_place(e: &Expr) -> Option<RtPlace> {
        match &e.kind {
            ExprKind::SlotOp { .. } => None,
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
    fn eval_moved(
        &mut self,
        e: &Expr,
        frame: &mut Frame,
        traps: TrapContext<'_>,
    ) -> IResult<RtVal> {
        let v = self.eval(e, frame, traps)?;
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
    fn eval_erased_resource_arg(
        &mut self,
        e: &Expr,
        frame: &mut Frame,
        traps: TrapContext<'_>,
    ) -> IResult<()> {
        // The checked formal parameter or sealed primitive operand is the
        // authority for erasedness here. Resource variables and borrows may
        // have no cached `Expr::ty`: their checker arms return as soon as the
        // expected resource type has been validated. A present annotation
        // must still agree with the caller's contract.
        debug_assert!(
            e.ty.clone()
                .map_or(true, |arg0: ast::Ty| Ty::is_resource(&arg0))
        );
        match &e.kind {
            ExprKind::Var(_) | ExprKind::Borrow { .. } | ExprKind::SelfField { .. } => Ok(()),
            _ => {
                self.eval_moved(e, frame, traps)?;
                Ok(())
            }
        }
    }

    /// Operand evaluation for a resource transformation whose result is
    /// erased. Nested resource expressions recurse through the same effect
    /// boundary; ordinary operands use their normal runtime evaluator.
    fn eval_erased_resource_operand(
        &mut self,
        e: &Expr,
        frame: &mut Frame,
        traps: TrapContext<'_>,
    ) -> IResult<()> {
        if e.ty
            .clone()
            .is_some_and(|arg0: ast::Ty| Ty::is_resource(&arg0))
        {
            self.eval_erased_resource_arg(e, frame, traps)
        } else {
            self.eval_moved(e, frame, traps)?;
            Ok(())
        }
    }

    /// Consume the checker-retained destruction recipe for one class value.
    /// A field the body moved out is *not* dropped again — dynamic presence
    /// stays in the runtime map — but invariant/deinitializer/field order and
    /// the terminal no-unwind policy come only from `ClassDropPlan`.
    #[cfg(test)]
    fn drop_value(
        &mut self,
        class: usize,
        fields: &Rc<RefCell<HashMap<String, RtVal>>>,
        what: &str,
    ) -> IResult<()> {
        let Some(cd) = self.classes.get(class).cloned() else {
            return Err(control_plan_trap(PlanError {
                span: Span::new(0, 0),
                message: format!("runtime class index {class} has no concrete declaration"),
            }));
        };
        let drop_plan = self
            .control
            .class_drop(class, &cd)
            .map_err(control_plan_trap)?
            .clone();
        self.drop_value_with_plan(class, fields, what, &drop_plan, cd.span)
    }

    /// Execute an already-resolved class action. Statement cleanup sites use
    /// this entry so their retained `ClassDropAction`, rather than the runtime
    /// payload tag, selects the destruction recipe.
    fn drop_value_with_plan(
        &mut self,
        class: usize,
        fields: &Rc<RefCell<HashMap<String, RtVal>>>,
        what: &str,
        drop_plan: &ClassDropPlan,
        use_span: Span,
    ) -> IResult<()> {
        let Some(cd) = self.classes.get(class).cloned() else {
            return Err(control_plan_trap(PlanError {
                span: use_span,
                message: format!("runtime class index {class} has no concrete declaration"),
            }));
        };
        drop_plan.validate(class, &cd).map_err(control_plan_trap)?;
        // All three potentially failing phase kinds share this one empty
        // route. The `?` on each operation below is therefore deliberate: a
        // failure returns immediately and never executes the phase suffix.
        drop_plan
            .validate_terminal_trap_route()
            .map_err(control_plan_trap)?;
        debug_assert_eq!(drop_plan.class(), class);
        let terminal = drop_plan.terminal_trap_route();
        debug_assert_eq!(terminal.kind(), crate::control::ExitKind::Trap);
        debug_assert!(
            terminal.scopes().is_empty()
                && terminal.clears().is_empty()
                && terminal.drops().is_empty()
        );

        for phase in drop_plan.phases() {
            match phase {
                ClassDropPhase::CheckInvariant => {
                    self.check_invariants_at(&cd, fields, what)?;
                }
                ClassDropPhase::RunDeinitializer(owner) => {
                    let Some(body) = cd.deinit.clone() else {
                        return Err(control_plan_trap(PlanError {
                            span: cd.span,
                            message: format!(
                                "class-drop plan for `{}` retained a missing deinitializer",
                                cd.name
                            ),
                        }));
                    };
                    let control_body = self
                        .control
                        .body(owner, cd.span)
                        .map_err(control_plan_trap)?;
                    control_body
                        .validate_callable(cd.span, &[], &body)
                        .map_err(control_plan_trap)?;
                    let plan = control_body.plan();
                    let mut control = ExecutionControl::new(plan);
                    let mut frame = Frame {
                        vars: HashMap::new(),
                        entry_scalars: HashMap::new(),
                        olds: HashMap::new(),
                        self_ctx: Some((class, fields.clone())),
                    };
                    match self.exec_body(&body, &mut frame, &mut control)? {
                        Flow::Normal => {}
                        Flow::Return(_) => {
                            return Err(control_plan_trap(PlanError {
                                span: cd.span,
                                message: format!(
                                    "deinitializer for `{}` returned instead of completing its class-drop phase",
                                    cd.name
                                ),
                            }));
                        }
                    }
                }
                ClassDropPhase::DropField(field) => {
                    // Remove before recursively destroying: the field is no
                    // longer live in its owner while its own deinitializer
                    // runs. An absent entry is the representation-specific
                    // record that the parent deinitializer moved it out.
                    let held = fields.borrow_mut().remove(field.name());
                    let Some(held) = held else {
                        continue;
                    };
                    if field.must_consume() {
                        return Err(control_plan_trap(PlanError {
                            span: field.span(),
                            message: format!(
                                "must-consume field `{}` remained live at class destruction",
                                field.name()
                            ),
                        }));
                    }
                    if let Some(action) = field.drop_action() {
                        self.drop_runtime_value_with_action(
                            held,
                            action,
                            &format!("{what}.{}", field.name()),
                            field.span(),
                        )?;
                    } else if matches!(
                        held,
                        RtVal::Obj { .. }
                            | RtVal::Arr(_)
                            | RtVal::AffineOptBoolArray(_)
                            | RtVal::AffineOptClass { .. }
                    ) {
                        return Err(control_plan_trap(PlanError {
                            span: field.span(),
                            message: format!(
                                "runtime field `{}` holds an owner without a retained drop action",
                                field.name()
                            ),
                        }));
                    }
                }
            }
        }
        Ok(())
    }

    fn drop_runtime_value_with_action(
        &mut self,
        held: RtVal,
        action: &ValueDropAction,
        what: &str,
        use_span: Span,
    ) -> IResult<()> {
        self.control
            .validate_value_drop_action(action, self.classes, use_span)
            .map_err(control_plan_trap)?;
        match (action.recipe(), held) {
            (ValueDropRecipe::ReleaseSlots { .. }, _) => Err(control_plan_trap(PlanError {
                span: use_span,
                message: format!(
                    "internal.interp.slots_cleanup_unsupported: runtime cleanup for owner-slot value `{what}` is not admitted"
                ),
            })),
            (ValueDropRecipe::DropClass(class_action), RtVal::Obj { class, fields })
                if class == class_action.class() =>
            {
                let drop_plan = self
                    .control
                    .class_drop_for_action(class_action, self.classes, use_span)
                    .map_err(control_plan_trap)?
                    .clone();
                self.drop_value_with_plan(class, &fields, what, &drop_plan, use_span)
            }
            (ValueDropRecipe::DropClass(class_action), _) => Err(control_plan_trap(PlanError {
                span: use_span,
                message: format!(
                    "runtime value `{what}` does not hold retained class index {}",
                    class_action.class()
                ),
            })),
            (ValueDropRecipe::ReleaseArray { element }, RtVal::Arr(array)) => {
                let actual = array.borrow().payload();
                if &actual != element {
                    return Err(control_plan_trap(PlanError {
                        span: use_span,
                        message: format!(
                            "runtime array `{what}` has payload `{}`, not retained payload `{}`",
                            actual.name(),
                            element.name()
                        ),
                    }));
                }
                Ok(())
            }
            (ValueDropRecipe::ReleaseArray { .. }, _) => Err(control_plan_trap(PlanError {
                span: use_span,
                message: format!("runtime value `{what}` does not hold its retained array"),
            })),
            (ValueDropRecipe::DropPresent(_), RtVal::AffineOptBoolArray(None))
            | (ValueDropRecipe::DropPresent(_), RtVal::AffineOptClass { value: None, .. }) => {
                Ok(())
            }
            (ValueDropRecipe::DropPresent(payload), RtVal::AffineOptBoolArray(Some(array))) => self
                .drop_runtime_value_with_action(
                    RtVal::Arr(array),
                    payload,
                    &format!("{what}.value"),
                    use_span,
                ),
            (
                ValueDropRecipe::DropPresent(payload),
                RtVal::AffineOptClass {
                    class,
                    value: Some(fields),
                },
            ) => self.drop_runtime_value_with_action(
                RtVal::Obj { class, fields },
                payload,
                &format!("{what}.value"),
                use_span,
            ),
            (ValueDropRecipe::DropPresent(_), _) => Err(control_plan_trap(PlanError {
                span: use_span,
                message: format!("runtime value `{what}` does not hold its retained owning option"),
            })),
        }
    }

    fn validate_runtime_value_for_action(
        &self,
        held: &RtVal,
        action: &ValueDropAction,
        what: &str,
        use_span: Span,
    ) -> IResult<()> {
        self.control
            .validate_value_drop_action(action, self.classes, use_span)
            .map_err(control_plan_trap)?;
        if let (ValueDropRecipe::ReleaseArray { element }, RtVal::Arr(array)) =
            (action.recipe(), held)
        {
            let actual = array.borrow().payload();
            if &actual != element {
                return Err(control_plan_trap(PlanError {
                    span: use_span,
                    message: format!(
                        "runtime array `{what}` has payload `{}`, not retained payload `{}`",
                        actual.name(),
                        element.name()
                    ),
                }));
            }
        }
        let valid = match (action.recipe(), held) {
            (ValueDropRecipe::ReleaseSlots { .. }, _) => {
                return Err(control_plan_trap(PlanError {
                    span: use_span,
                    message: format!(
                        "internal.interp.slots_cleanup_unsupported: runtime validation for owner-slot value `{what}` is not admitted"
                    ),
                }));
            }
            (ValueDropRecipe::DropClass(expected), RtVal::Obj { class, .. }) => {
                *class == expected.class()
            }
            (ValueDropRecipe::ReleaseArray { element }, RtVal::Arr(array)) => {
                array.borrow().payload() == *element
            }
            (ValueDropRecipe::DropPresent(payload), RtVal::AffineOptBoolArray(value)) => {
                matches!(
                    payload.recipe(),
                    ValueDropRecipe::ReleaseArray { element } if element == &Ty::Bool
                ) && value.as_ref().is_none_or(|array| {
                    self.validate_runtime_value_for_action(
                        &RtVal::Arr(array.clone()),
                        payload,
                        what,
                        use_span,
                    )
                    .is_ok()
                })
            }
            (ValueDropRecipe::DropPresent(payload), RtVal::AffineOptClass { class, value }) => {
                matches!(
                    payload.recipe(),
                    ValueDropRecipe::DropClass(expected) if expected.class() == *class
                ) && value.as_ref().is_none_or(|fields| {
                    self.validate_runtime_value_for_action(
                        &RtVal::Obj {
                            class: *class,
                            fields: fields.clone(),
                        },
                        payload,
                        what,
                        use_span,
                    )
                    .is_ok()
                })
            }
            (ValueDropRecipe::DropClass(_), _)
            | (ValueDropRecipe::ReleaseArray { .. }, _)
            | (ValueDropRecipe::DropPresent(_), _) => false,
        };
        if valid {
            Ok(())
        } else {
            Err(control_plan_trap(PlanError {
                span: use_span,
                message: format!(
                    "runtime value `{what}` does not match retained cleanup type `{}`",
                    action.ty().name()
                ),
            }))
        }
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
        statement: StatementPlanKind,
        frame: &mut Frame,
        control: &mut ExecutionControl<'_>,
        scope: ScopeId,
    ) -> IResult<Flow> {
        let structurally_matches = match stmt {
            Stmt::Return { .. } => matches!(statement, StatementPlanKind::Return),
            Stmt::If { .. } => matches!(statement, StatementPlanKind::Branch(_)),
            Stmt::While { .. } => matches!(statement, StatementPlanKind::Loop(_)),
            Stmt::Unsafe { .. } => matches!(statement, StatementPlanKind::Unsafe(_)),
            Stmt::Expose { .. } => matches!(statement, StatementPlanKind::Exposure(_)),
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
                matches!(statement, StatementPlanKind::Linear(_))
            }
        };
        if !structurally_matches {
            return Err(control_plan_trap(PlanError {
                span: stmt_span(stmt),
                message: "runtime statement disagrees with its retained structural role".into(),
            }));
        }
        // Exposure opens a raw loan, so authenticate every source identity
        // against the retained epilogue before even consuming dynamic fuel or
        // trap sites. In particular, a post-check AST cannot redirect the
        // planned copyback to another array or rename the body capabilities.
        let planned_exposure = match stmt {
            Stmt::Expose {
                kw_span,
                array,
                mutable,
                ptr,
                res,
                ..
            } => {
                let exposure = control
                    .plan
                    .exposure_plan(scope, *kw_span)
                    .map_err(control_plan_trap)?
                    .clone();
                let body_plan = control.plan.block(exposure.body());
                let Some(normal) = exposure.normal().cloned() else {
                    return Err(control_plan_trap(PlanError {
                        span: *kw_span,
                        message: "interpreter exposure has no admitted normal close plan".into(),
                    }));
                };
                if exposure.parent_scope() != scope
                    || exposure.keyword_span() != *kw_span
                    || body_plan.kind() != crate::control::BlockKind::Exposure
                    || body_plan.anchor() != *kw_span
                    || body_plan.scope() != exposure.body_scope()
                    || body_plan.flow() != exposure.body_flow()
                    || exposure.flow() != exposure.body_flow()
                    || exposure.body_flow().contains_return()
                    || normal.parent_scope() != scope
                    || normal.body_exit().kind() != crate::control::ExitKind::Fallthrough
                    || normal.body_exit().scopes() != [exposure.body_scope()]
                    || normal.close().kind() != crate::control::ExitKind::ExposureClose
                    || !normal.close().scopes().is_empty()
                    || !normal.close().clears().contains(normal.release_loan())
                    || normal.capture() != normal.rebuild().resource()
                    || normal.release_loan() == normal.rebuild().pointer()
                    || &exposure.effect_key().owner != control.plan.owner()
                    || exposure.effect_key().span != *kw_span
                {
                    return Err(control_plan_trap(PlanError {
                        span: *kw_span,
                        message:
                            "exposure plan is detached from its retained body or normal epilogue"
                                .into(),
                    }));
                }
                let rebuild = normal.rebuild();
                let expected_mutability = if *mutable {
                    Mutability::Mut
                } else {
                    Mutability::Shared
                };
                if rebuild.owner() != &Place::local(array)
                    || rebuild.pointer() != &Place::local(ptr)
                    || rebuild.resource() != &Place::local(res)
                    || rebuild.mutability() != expected_mutability
                    || rebuild.keyword_span() != *kw_span
                    || !matches!(rebuild.owner_ty().as_array(), Some((Ty::Int(IntTy::U8), _)))
                {
                    return Err(control_plan_trap(PlanError {
                        span: *kw_span,
                        message: "exposure source bindings, owner type, or mutability disagree with the retained rebuild action"
                            .into(),
                    }));
                }
                Some((exposure, normal))
            }
            _ => None,
        };
        // Replacement/drop actions are authenticated before fuel or runtime
        // state changes. The interpreter may decide only whether a retained
        // destination is dynamically present, never which cleanup recipe or
        // staging identity belongs to this source site.
        let planned_field_assignment = match stmt {
            Stmt::FieldAssign {
                field,
                field_span,
                value,
            } => {
                let destination = Place::field("self", field);
                let action = control
                    .plan
                    .field_assignment(scope, *field_span, &destination, value)
                    .map_err(control_plan_trap)?
                    .clone();
                if action.scope() != scope
                    || action.span() != *field_span
                    || action.destination() != &destination
                {
                    return Err(control_plan_trap(PlanError {
                        span: *field_span,
                        message: "field assignment is detached from its retained action".into(),
                    }));
                }
                match (action.drop_if_present(), action.staging()) {
                    (true, AssignmentStaging::Temporary(temp)) if temp.is_root() => {}
                    (false, AssignmentStaging::Direct) => {}
                    _ => {
                        return Err(control_plan_trap(PlanError {
                            span: *field_span,
                            message: "field assignment has inconsistent retained staging".into(),
                        }));
                    }
                }
                if let Some(drop_action) = action.drop_action() {
                    self.control
                        .validate_value_drop_action(drop_action, self.classes, *field_span)
                        .map_err(control_plan_trap)?;
                }
                Some(action)
            }
            _ => None,
        };
        let planned_temporary_drop = match stmt {
            Stmt::ExprStmt(expression) if matches!(expression.ty, Some(Ty::Class(_))) => {
                let action = control
                    .plan
                    .temporary_drop(scope, expression)
                    .map_err(control_plan_trap)?
                    .clone();
                if action.scope() != scope
                    || action.span() != expression.span
                    || !action.temporary().is_root()
                {
                    return Err(control_plan_trap(PlanError {
                        span: expression.span,
                        message:
                            "discarded class result is detached from its retained temporary action"
                                .into(),
                    }));
                }
                self.control
                    .validate_value_drop_action(action.drop_action(), self.classes, expression.span)
                    .map_err(control_plan_trap)?;
                Some(action)
            }
            _ => None,
        };
        self.burn(stmt_span(stmt))?;
        let traps = TrapContext::new(control.plan, scope);
        traps.consume_statement(stmt)?;
        match stmt {
            Stmt::Decl { name, init, .. } => {
                if let Some(e) = init {
                    let v = self.eval_moved(e, frame, traps)?;
                    frame.vars.insert(name.clone(), v);
                }
                Ok(Flow::Normal)
            }
            Stmt::Assign {
                name,
                name_span,
                value,
            } => {
                let destination = Place::local(name);
                let action = control
                    .plan
                    .assignment(scope, *name_span, &destination)
                    .map_err(control_plan_trap)?
                    .clone();
                if action.scope() != scope {
                    return Err(Trap {
                        undef: true,
                        message: "internal control assignment has a mismatched lexical scope"
                            .into(),
                        span: action.span(),
                    });
                }
                match (action.previous(), action.staging()) {
                    (Some(_), AssignmentStaging::Temporary(temp)) if temp.is_root() => {}
                    (None, AssignmentStaging::Direct) => {}
                    _ => {
                        return Err(Trap {
                            undef: true,
                            message: "internal control assignment has inconsistent staging".into(),
                            span: action.span(),
                        });
                    }
                }
                let v = self.eval_moved(value, frame, traps)?;
                // The action, rather than the runtime value's shape, decides
                // whether replacement has an old cleanup candidate. Runtime
                // liveness still decides whether a moved-out place contains
                // anything for that planned drop to destroy.
                if let Some(drop) = action.previous() {
                    if !control.reached.contains(&drop) {
                        return Err(Trap {
                            undef: true,
                            message: format!(
                                "internal control assignment reached `{}` before its binding",
                                action.destination().render()
                            ),
                            span: action.span(),
                        });
                    }
                    let candidate = control.plan.candidate(drop);
                    if candidate.place() != action.destination() || candidate.ty() != action.ty() {
                        return Err(Trap {
                            undef: true,
                            message:
                                "internal control assignment names a mismatched drop candidate"
                                    .into(),
                            span: action.span(),
                        });
                    }
                    let destination = RtPlace::Local(action.destination().root().to_owned());
                    if let Some(held) = self.take_place(&destination, frame) {
                        self.drop_runtime_value_with_action(
                            held,
                            candidate.drop_action(),
                            &action.destination().render(),
                            action.span(),
                        )?;
                    }
                }
                frame.vars.insert(action.destination().root().to_owned(), v);
                Ok(Flow::Normal)
            }
            // `unsafe { ... }` is a marker: its retained block shares the
            // active lexical scope and therefore has no close at this brace.
            Stmt::Unsafe { body, .. } => {
                let StatementPlanKind::Unsafe(block) = statement else {
                    unreachable!("the structural guard above matched `unsafe`")
                };
                self.exec_open_block(body, frame, control, block)
            }
            Stmt::StaticAlloc { size, ptr, res, .. } => {
                let RtVal::Int(n) = self.eval(size, frame, traps)? else {
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
                let RtVal::Int(n) = self.eval(size, frame, traps)? else {
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
                let RtVal::Ptr(alloc, off) = self.eval(ptr, frame, traps)? else {
                    unreachable!("checked: raw pointer")
                };
                self.eval_moved(res, frame, traps)?;
                self.eval_moved(release, frame, traps)?;
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
            Stmt::Expose { kw_span, body, .. } => {
                // The AST supplies the executable body; the preflight above
                // authenticated and selected every retained identity and edge
                // before this arm may create the loan.
                let (exposure, normal) =
                    planned_exposure.expect("the structural guard identified an exposure");
                let root = |place: &Place, role: &str| -> IResult<String> {
                    if !place.is_root() {
                        return Err(control_plan_trap(PlanError {
                            span: *kw_span,
                            message: format!(
                                "interpreter exposure {role} `{}` is not a local",
                                place.render()
                            ),
                        }));
                    }
                    Ok(place.root().to_owned())
                };
                let rebuild = normal.rebuild();
                let owner = root(rebuild.owner(), "owner")?;
                let pointer = root(rebuild.pointer(), "pointer")?;
                let resource = root(rebuild.resource(), "resource")?;
                let capture = root(normal.capture(), "capture")?;
                let release = root(normal.release_loan(), "release")?;
                if capture != resource || rebuild.keyword_span() != *kw_span {
                    return Err(control_plan_trap(PlanError {
                        span: *kw_span,
                        message:
                            "exposure capture/rebuild identities disagree with the retained site"
                                .into(),
                    }));
                }
                let Some(RtVal::Arr(a)) = frame.vars.get(owner.as_str()).cloned() else {
                    return Err(control_plan_trap(PlanError {
                        span: *kw_span,
                        message: format!(
                            "interpreter exposure owner `{owner}` is absent or not an array"
                        ),
                    }));
                };
                let (owner_payload, _) = rebuild
                    .owner_ty()
                    .as_array()
                    .expect("exposure preflight retained a byte-array owner");
                if a.borrow().payload() != owner_payload.clone() {
                    return Err(control_plan_trap(PlanError {
                        span: *kw_span,
                        message:
                            "exposure runtime owner payload disagrees with its retained owner type"
                                .into(),
                    }));
                }
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
                frame.vars.insert(pointer, RtVal::Ptr(alloc, 0));
                // The resource has no runtime representation (ADR 0024);
                // the binding exists so the body's names resolve.
                frame.vars.insert(resource, RtVal::Unit);
                // This consumer represents the plan's loan-release authority
                // by the allocation identity itself. It survives body_exit
                // and is removed only by the retained close route.
                frame.vars.insert(release.clone(), RtVal::Ptr(alloc, 0));

                let flow = self.exec_open_block(body, frame, control, exposure.body())?;
                if !matches!(flow, Flow::Normal) {
                    // Checked exposures cannot return. Keeping the edge
                    // explicit preserves the plan's rule that only a normal
                    // body edge may run capture/rebuild/release/close.
                    return Ok(flow);
                }

                // ExposureNormalPlan fixes this order: capture final storage,
                // end body bindings, rebuild/copy back, release, close scratch.
                if !frame.vars.contains_key(capture.as_str()) {
                    return Err(control_plan_trap(PlanError {
                        span: *kw_span,
                        message: "exposure capture action reached an absent resource binding"
                            .into(),
                    }));
                }
                let Some(allocation) = self.raw.allocs.get(&alloc) else {
                    return Err(control_plan_trap(PlanError {
                        span: *kw_span,
                        message: "exposure capture action names an absent raw loan".into(),
                    }));
                };
                if !allocation.live {
                    return Err(control_plan_trap(PlanError {
                        span: *kw_span,
                        message: "exposure capture action names a released raw loan".into(),
                    }));
                }
                let final_bytes = allocation.bytes.clone();
                self.cleanup_route(normal.body_exit(), frame, control)?;
                if rebuild.mutability() == Mutability::Mut {
                    for (i, b) in final_bytes.iter().enumerate().take(n) {
                        match b {
                            Some(v) => a.borrow_mut().set_int(i, *v),
                            None => {
                                return Err(Trap {
                                    undef: false,
                                    message: format!(
                                        "exposure of `{owner}` ends with byte {i} \
                                         uninitialized"
                                    ),
                                    span: *kw_span,
                                });
                            }
                        }
                    }
                }
                let Some(RtVal::Ptr(release_alloc, 0)) = frame.vars.get(release.as_str()) else {
                    return Err(control_plan_trap(PlanError {
                        span: *kw_span,
                        message: "exposure release action has no live retained loan".into(),
                    }));
                };
                if *release_alloc != alloc {
                    return Err(control_plan_trap(PlanError {
                        span: *kw_span,
                        message: "exposure release action names a different raw loan".into(),
                    }));
                }
                let Some(allocation) = self.raw.allocs.get_mut(&alloc) else {
                    return Err(control_plan_trap(PlanError {
                        span: *kw_span,
                        message: "exposure release action names an absent raw loan".into(),
                    }));
                };
                allocation.live = false;
                self.cleanup_route(normal.close(), frame, control)?;
                Ok(Flow::Normal)
            }
            Stmt::ExprStmt(e) => {
                let v = self.eval(e, frame, traps)?;
                if let Some(action) = planned_temporary_drop {
                    self.drop_runtime_value_with_action(
                        v,
                        action.drop_action(),
                        &action.temporary().render(),
                        action.span(),
                    )?;
                }
                Ok(Flow::Normal)
            }
            Stmt::Assert(clause) => {
                self.check_clause(frame, clause, None, "inline assert")?;
                Ok(Flow::Normal)
            }
            Stmt::VarDecl { name, init, .. } => {
                let v = self.eval_moved(init, frame, traps)?;
                frame.vars.insert(name.clone(), v);
                Ok(Flow::Normal)
            }
            Stmt::FieldAssign { field, value, .. } => {
                let action = planned_field_assignment
                    .expect("field-assignment preflight selected its retained action");
                let v = self.eval_moved(value, frame, traps)?;
                if let Some(drop_action) = action.drop_action() {
                    self.validate_runtime_value_for_action(
                        &v,
                        drop_action,
                        "field-assignment RHS",
                        action.span(),
                    )?;
                }
                if action.drop_if_present() {
                    let drop_action = action.drop_action().expect("drop-if-present has an action");
                    let (_, fields) = frame.self_ctx.clone().ok_or_else(|| {
                        control_plan_trap(PlanError {
                            span: action.span(),
                            message: "field-assignment action has no active self object".into(),
                        })
                    })?;
                    let previous = fields.borrow_mut().remove(field.as_str());
                    if let Some(previous) = previous {
                        self.drop_runtime_value_with_action(
                            previous,
                            drop_action,
                            &action.destination().render(),
                            action.span(),
                        )?;
                    }
                }
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
                let idx = self.eval_int(index, frame, traps)?;
                let val = self.eval(value, frame, traps)?;
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
                arr.borrow_mut().set(idx as usize, val, *field_span)?;
                Ok(Flow::Normal)
            }
            Stmt::Store {
                array,
                array_span,
                index,
                value,
            } => {
                let idx = self.eval_int(index, frame, traps)?;
                let val = self.eval(value, frame, traps)?;
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
                a.borrow_mut().set(idx as usize, val, *array_span)?;
                Ok(Flow::Normal)
            }
            Stmt::Return { value, span } => {
                // Returning a place is a move: the value leaves with the
                // caller, so the scopes unwinding behind it must not find
                // it still sitting in its source and destroy it.
                let v = match value {
                    Some(e) => self.eval_moved(e, frame, traps)?,
                    None => RtVal::Unit,
                };
                let route = control
                    .plan
                    .explicit_return(*span, scope)
                    .map_err(control_plan_trap)?
                    .lexical()
                    .clone();
                self.cleanup_route(&route, frame, control)?;
                Ok(Flow::Return(v))
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                let branch = control
                    .plan
                    .branch(scope, cond.span, else_block.is_some())
                    .map_err(control_plan_trap)?
                    .clone();
                if self.eval_bool(cond, frame, traps)? {
                    let arm = branch.then_arm();
                    self.exec_block(
                        then_block,
                        frame,
                        control,
                        arm.block(),
                        arm.normal_exit().cloned(),
                    )
                } else if let Some(eb) = else_block {
                    let Some(arm) = branch.else_arm() else {
                        return Err(control_plan_trap(PlanError {
                            span: cond.span,
                            message: "retained branch lost its source else arm".into(),
                        }));
                    };
                    self.exec_block(eb, frame, control, arm.block(), arm.normal_exit().cloned())
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
                let loop_plan = control
                    .plan
                    .loop_plan(scope, *kw_span, cond.span)
                    .map_err(control_plan_trap)?
                    .clone();
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
                    if !self.eval_bool(cond, frame, traps)? {
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

                    match self.exec_block(
                        body,
                        frame,
                        control,
                        loop_plan.body(),
                        loop_plan.backedge().cloned(),
                    )? {
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
        let owner = CallOwner::Constructor {
            class: class.name.clone(),
            init: ifn.name.clone(),
        };
        let control_body = self
            .control
            .body(&owner, ifn.span)
            .map_err(control_plan_trap)?;
        control_body
            .validate_callable(ifn.span, &ifn.params, &ifn.body)
            .map_err(control_plan_trap)?;
        let plan = control_body.plan();
        let mut control = ExecutionControl::new(plan);
        let fields = Rc::new(RefCell::new(HashMap::new()));
        let mut frame = Frame {
            vars: HashMap::new(),
            entry_scalars: HashMap::new(),
            olds: HashMap::new(),
            self_ctx: Some((ci, fields.clone())),
        };
        for (p, v) in ifn.params.iter().zip(args) {
            match (&v, p.ty.clone()) {
                (obj @ RtVal::Obj { .. }, ty) if ty.is_unique_borrow() => {
                    if let Some(sv) = spec_of(obj) {
                        frame.olds.insert(p.name.clone(), sv);
                    }
                }
                _ => {
                    frame.entry_scalars.insert(p.name.clone(), v.clone());
                }
            }
            frame.vars.insert(p.name.clone(), v);
            control.arm(&p.name, plan.frame_scope(), p.span)?;
        }
        for pre in &ifn.pres {
            self.check_clause(
                &frame,
                pre,
                None,
                &format!("pre of `{}::{}`", class.name, ifn.name),
            )?;
        }
        self.exec_body(&ifn.body, &mut frame, &mut control)?;
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
        let frame_exit = plan.implicit_return().frame().clone();
        self.cleanup_route(&frame_exit, &mut frame, &mut control)?;
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
        let owner = CallOwner::Method {
            class: class.name.clone(),
            method: m.f.name.clone(),
        };
        let control_body = self
            .control
            .body(&owner, m.f.span)
            .map_err(control_plan_trap)?;
        control_body
            .validate_callable(m.f.span, &m.f.params, &m.f.body)
            .map_err(control_plan_trap)?;
        let plan = control_body.plan();
        let mut control = ExecutionControl::new(plan);
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
            match (&v, p.ty.clone()) {
                // `&mut C`: the borrow shares storage with the caller, so
                // `old p` needs the value it had at entry. `spec_of` copies.
                (obj @ RtVal::Obj { .. }, ty) if ty.is_unique_borrow() => {
                    if let Some(sv) = spec_of(obj) {
                        frame.olds.insert(p.name.clone(), sv);
                    }
                }
                _ => {
                    frame.entry_scalars.insert(p.name.clone(), v.clone());
                }
            }
            frame.vars.insert(p.name.clone(), v);
            control.arm(&p.name, plan.frame_scope(), p.span)?;
        }
        for pre in &m.f.pres {
            self.check_clause(
                &frame,
                pre,
                None,
                &format!("pre of `{}::{method}`", class.name),
            )?;
        }
        let flow = self.exec_body(&m.f.body, &mut frame, &mut control)?;
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
        let frame_exit = plan.implicit_return().frame().clone();
        self.cleanup_route(&frame_exit, &mut frame, &mut control)?;
        Ok(result)
    }

    fn eval_int(&mut self, e: &Expr, frame: &mut Frame, traps: TrapContext<'_>) -> IResult<i128> {
        match self.eval(e, frame, traps)? {
            RtVal::Int(n) => Ok(n),
            _ => unreachable!("checked: int expression"),
        }
    }

    fn eval_bool(&mut self, e: &Expr, frame: &mut Frame, traps: TrapContext<'_>) -> IResult<bool> {
        match self.eval(e, frame, traps)? {
            RtVal::Bool(b) => Ok(b),
            _ => unreachable!("checked: bool expression"),
        }
    }

    fn eval(&mut self, e: &Expr, frame: &mut Frame, traps: TrapContext<'_>) -> IResult<RtVal> {
        self.burn(e.span)?;
        traps.consume_expression(e)?;
        match &e.kind {
            ExprKind::SlotOp { op, .. } => Err(Trap {
                undef: true,
                message: format!(
                    "interp.slots_unsupported: `{}` has no interpreter semantics yet",
                    op.name()
                ),
                span: e.span,
            }),
            ExprKind::IntLit(n) => Ok(RtVal::Int(*n)),
            ExprKind::BoolLit(b) => Ok(RtVal::Bool(*b)),
            ExprKind::Var(name) => match frame.vars.get(name.as_str()) {
                Some(RtVal::AffineOptBoolArray(_)) => {
                    unreachable!("checked: affine option places are observed or taken directly")
                }
                Some(value) => Ok(value.clone()),
                None => unreachable!("checked: initialized local"),
            },
            // Resource transformations redistribute authority, which is
            // a static notion: at runtime there is nothing to move and
            // nothing to return (ADR 0024). `posix_world` is the
            // exception: the *script* it selects is real runtime state,
            // and a test controlling it is what "scripted world" means.
            ExprKind::ResOp { op, args, .. } => {
                match op {
                    ResOp::TestWorld => {
                        let script = self.eval_int(&args[0], frame, traps)?;
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
                        let script = self.eval_int(&args[0], frame, traps)?;
                        self.uart = Some(ScriptedUart::new(script));
                    }
                    // Adoption spends the world's claim on a descriptor.
                    // The VC is what makes a second adoption unreachable;
                    // this is the monitor saying so independently, the
                    // same two layers the raw operations have.
                    ResOp::OpenFileOf => {
                        self.eval_erased_resource_arg(&args[0], frame, traps)?;
                        let fd = self.eval_int(&args[1], frame, traps)?;
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
                        let RtVal::ResMap(entries) = self.eval(&args[0], frame, traps)? else {
                            unreachable!("checked: resource map borrow")
                        };
                        let key = self.eval_int(&args[1], frame, traps)?;
                        if !entries.borrow_mut().remove(&key) {
                            return Err(Trap {
                                undef: false,
                                message: format!("resource_map_take: key {key} is absent"),
                                span: e.span,
                            });
                        }
                    }
                    ResOp::ResourceMapPut => {
                        let RtVal::ResMap(entries) = self.eval(&args[0], frame, traps)? else {
                            unreachable!("checked: resource map borrow")
                        };
                        let key = self.eval_int(&args[1], frame, traps)?;
                        self.eval_erased_resource_arg(&args[2], frame, traps)?;
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
                            self.eval_erased_resource_operand(arg, frame, traps)?;
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
                    let byte = self.eval_int(&args[0], frame, traps)?;
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
                        vs.push(self.eval(a, frame, traps)?);
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
                let idx = self.eval_int(index, frame, traps)?;
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
            ExprKind::IsSome { operand } => {
                // Affine presence tests inspect the named place itself.  They
                // do not even transiently copy an owner-bearing runtime
                // value; the only observation is the slot's tag.
                if let ExprKind::Var(name) = &operand.kind {
                    if let Some(RtVal::AffineOptBoolArray(value)) = frame.vars.get(name.as_str()) {
                        return Ok(RtVal::Bool(value.is_some()));
                    }
                    if let Some(RtVal::AffineOptClass { value, .. }) = frame.vars.get(name.as_str())
                    {
                        return Ok(RtVal::Bool(value.is_some()));
                    }
                }
                match self.eval(operand, frame, traps)? {
                    RtVal::Opt { value, .. } => Ok(RtVal::Bool(value.is_some())),
                    RtVal::PtrOpt(o) => Ok(RtVal::Bool(o.is_some())),
                    _ => unreachable!("checked: option operand"),
                }
            }
            ExprKind::OptValue { operand } => match self.eval(operand, frame, traps)? {
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
            ExprKind::OptTake {
                option,
                option_span,
            } => match frame.vars.get_mut(option.as_str()) {
                Some(RtVal::AffineOptBoolArray(value)) => match value.take() {
                    Some(array) => Ok(RtVal::Arr(array)),
                    None => Err(Trap {
                        undef: false,
                        message: "`.take` of an empty affine option".into(),
                        span: *option_span,
                    }),
                },
                Some(RtVal::AffineOptClass { class, value }) => {
                    let class = *class;
                    match value.take() {
                        Some(fields) => Ok(RtVal::Obj { class, fields }),
                        None => Err(Trap {
                            undef: false,
                            message: "`.take` of an empty affine option".into(),
                            span: *option_span,
                        }),
                    }
                }
                _ => unreachable!("checked: affine option local"),
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
                let idx = self.eval_int(index, frame, traps)?;
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
            ExprKind::Widen { arg, .. } => self.eval(arg, frame, traps),
            ExprKind::Narrow { target, arg } => {
                let v = self.eval_int(arg, frame, traps)?;
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
            // The option's runtime representation is chosen by its payload,
            // and the owning case is matched first: the copyable arm builds
            // its payload with `eval`, which duplicates the value. For an
            // owned array that would leave two owners of one allocation,
            // and `drop_place` — which looks at the value's own constructor
            // — would see neither of them.
            ExprKind::SomeE(inner) => match &e.ty {
                Some(option) if option.is_affine_option() => {
                    match self.eval_moved(inner, frame, traps)? {
                        RtVal::Arr(array) => {
                            debug_assert_eq!(array.borrow().payload(), Ty::Bool);
                            Ok(RtVal::AffineOptBoolArray(Some(array)))
                        }
                        // The wrap consumes the class value: `eval_moved`
                        // cleared its source, so the option is the sole
                        // owner from here.
                        RtVal::Obj { class, fields } => Ok(RtVal::AffineOptClass {
                            class,
                            value: Some(fields),
                        }),
                        _ => unreachable!("checked: affine option payload"),
                    }
                }
                Some(Ty::Option(payload)) => {
                    let value = self.eval(inner, frame, traps)?;
                    Ok(RtVal::Opt {
                        payload: *payload.clone(),
                        value: Some(Box::new(value)),
                    })
                }
                Some(Ty::OptionRaw(_)) => {
                    let RtVal::Ptr(a, o) = self.eval(inner, frame, traps)? else {
                        unreachable!("checked: raw pointer option")
                    };
                    Ok(RtVal::PtrOpt(Some((a, o))))
                }
                _ => unreachable!("checked: option construction"),
            },
            ExprKind::NoneE => match &e.ty {
                Some(option) if option.is_affine_option() => {
                    match option.as_affine_option_payload() {
                        Some(Ty::Class(class)) => Ok(RtVal::AffineOptClass {
                            class: *class,
                            value: None,
                        }),
                        _ => Ok(RtVal::AffineOptBoolArray(None)),
                    }
                }
                Some(Ty::Option(payload)) => Ok(RtVal::Opt {
                    payload: *payload.clone(),
                    value: None,
                }),
                Some(Ty::OptionRaw(_)) => Ok(RtVal::PtrOpt(None)),
                _ => unreachable!("checked: option construction"),
            },
            ExprKind::ArrayLit(elems) => {
                let Some(Ty::Array(ref payload)) = e.ty else {
                    unreachable!("checked: owned array literal type")
                };
                let mut values = Vec::with_capacity(elems.len());
                for el in elems {
                    values.push(self.eval(el, frame, traps)?);
                }
                Ok(RtVal::Arr(Rc::new(RefCell::new(RtArray::from_values(
                    *payload.clone(),
                    values,
                    e.span,
                )?))))
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
                let n = self.eval_int(len, frame, traps)?;
                let initial = self.eval(init, frame, traps)?;
                // Defined allocation-failure behavior: the named OOM trap.
                if n < 0 || n > 50_000_000 {
                    return Err(Trap {
                        undef: false,
                        message: format!("OOM trap: alloc_array of length {n}"),
                        span: e.span,
                    });
                }
                Ok(RtVal::Arr(Rc::new(RefCell::new(RtArray::repeat(
                    elem.clone(),
                    initial,
                    n as usize,
                    e.span,
                )?))))
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
                let idx = self.eval_int(index, frame, traps)?;
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
                    vals.push(self.eval_moved(a, frame, traps)?);
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
                    fields.insert(name, self.eval(arg, frame, traps)?);
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
                    vals.push(self.eval_moved(a, frame, traps)?);
                }
                self.invoke(class, method, fields, vals)
            }
            ExprKind::Unary { op, operand } => match op {
                UnOp::Not => {
                    let b = self.eval_bool(operand, frame, traps)?;
                    Ok(RtVal::Bool(!b))
                }
                UnOp::Neg => {
                    let v = self.eval_int(operand, frame, traps)?;
                    let Ty::Int(it) = e.ty.clone().unwrap() else {
                        unreachable!()
                    };
                    self.check_range(-v, it, e, "negation")?;
                    Ok(RtVal::Int(-v))
                }
            },
            ExprKind::Binary { op, lhs, rhs, .. } => {
                if matches!(op, BinOp::And | BinOp::Or) {
                    let l = self.eval_bool(lhs, frame, traps)?;
                    // Short-circuit, matching the VC semantics.
                    return Ok(RtVal::Bool(match op {
                        BinOp::And => l && self.eval_bool(rhs, frame, traps)?,
                        BinOp::Or => l || self.eval_bool(rhs, frame, traps)?,
                        _ => unreachable!(),
                    }));
                }
                let a = self.eval_int(lhs, frame, traps)?;
                let b = self.eval_int(rhs, frame, traps)?;
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
                let Ty::Int(it) = e.ty.clone().unwrap() else {
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
                    if p.ty.clone().is_resource()
                        && (f.extern_info.is_some() || !has_resource_shadow(p.ty.clone()))
                    {
                        self.eval_erased_resource_arg(a, frame, traps)?;
                        continue;
                    }
                    vals.push(self.eval_moved(a, frame, traps)?);
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
        RtVal::AffineOptBoolArray(_) => {
            unreachable!("affine options are never copied into snapshots or borrowed values")
        }
        RtVal::Opt { payload, value } => RtVal::Opt {
            payload: payload.clone(),
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
        RtVal::Arr(a) => SpecVal::Arr(a.borrow().to_spec()?),
        RtVal::Opt { payload, value } => SpecVal::Opt {
            payload: Some(payload.clone()),
            value: match value {
                Some(value) => Some(Box::new(spec_of(value)?)),
                None => None,
            },
        },
        RtVal::AffineOptBoolArray(value) => SpecVal::AffineOpt {
            value: match value {
                Some(array) => Some(Box::new(SpecVal::Arr(array.borrow().to_spec()?))),
                None => None,
            },
        },
        RtVal::AffineOptClass { value, .. } => SpecVal::AffineOpt {
            value: match value {
                Some(fields) => Some(Box::new(SpecVal::Obj(
                    fields
                        .borrow()
                        .iter()
                        .filter_map(|(k, v)| spec_of(v).map(|sv| (k.clone(), sv)))
                        .collect(),
                ))),
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

/// Payload-tagged constructors for tests, mirroring the spec-side helpers:
/// a probe states the payload it means instead of relying on an element
/// representation to imply one.
#[cfg(test)]
pub(crate) fn rt_bools(values: &[bool]) -> RtArray {
    RtArray::from_values(
        Ty::Bool,
        values.iter().copied().map(RtVal::Bool).collect(),
        Span::new(0, 0),
    )
    .expect("Boolean values inhabit a Boolean payload")
}

#[cfg(test)]
pub(crate) fn rt_ints(payload: IntTy, values: &[i128]) -> RtArray {
    RtArray::from_values(
        Ty::Int(payload),
        values.iter().copied().map(RtVal::Int).collect(),
        Span::new(0, 0),
    )
    .expect("integer values inhabit an integer payload")
}

/// The Boolean elements of an array, for assertions about contents rather
/// than representation.
#[cfg(test)]
pub(crate) fn rt_bools_of(array: &RtArray) -> Vec<bool> {
    array
        .iter()
        .map(|value| match value {
            RtVal::Bool(value) => *value,
            other => panic!("expected a Boolean element, found {other:?}"),
        })
        .collect()
}

#[cfg(test)]
mod payload_guard_tests {
    use super::*;
    use crate::scan::{Clause, ClauseKind};
    use crate::span::Span;

    #[test]
    fn owner_slots_have_neither_an_interpreter_type_nor_operation_semantics() {
        let error = validate_interp_ty(Ty::slots(Ty::Int(IntTy::U64)), "forged slot local")
            .expect_err("owner slots have no runtime representation yet");
        assert!(error.starts_with("interp.slots_unsupported:"), "{error}");

        let operation = expr(
            ExprKind::SlotOp {
                op: SlotOp::Put,
                op_span: Span::new(1, 2),
                args: vec![expr(
                    ExprKind::Var("hostile_operand".into()),
                    Some(Ty::Param(TypeParamId::from_legacy(0))),
                )],
            },
            Some(Ty::Param(TypeParamId::from_legacy(0))),
        );
        let error = validate_interp_expr(&operation, &HashMap::new())
            .expect_err("the slot refusal wins over hostile cached types and operands");
        assert!(error.starts_with("interp.slots_unsupported:"), "{error}");
    }

    /// The tag beside the elements is what every later read, store, and
    /// comparison trusts, so building an array whose values do not inhabit it
    /// is a real check rather than a debug assertion. It is reported as
    /// undefined behavior: no program the checker admits can produce it.
    #[test]
    fn an_array_never_holds_a_value_outside_its_payload() {
        let span = Span::new(0, 0);
        let mismatch = RtArray::from_values(Ty::Bool, vec![RtVal::Int(1)], span)
            .expect_err("an integer does not inhabit a Boolean payload");
        assert!(mismatch.undef);
        assert!(
            mismatch
                .message
                .starts_with("interp.array_payload_mismatch:"),
            "{}",
            mismatch.message
        );

        assert!(
            RtArray::repeat(Ty::Record(0), RtVal::Int(0), 1, span).is_err(),
            "a payload with no runtime value is inhabited by nothing"
        );

        let mut array = RtArray::from_values(Ty::Bool, vec![RtVal::Bool(true)], span)
            .expect("Boolean values inhabit a Boolean payload");
        assert!(array.set(0, RtVal::Int(0), span).is_err());
        assert!(array.set(0, RtVal::Bool(false), span).is_ok());
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

    fn drop_clause(kind: ClauseKind, text: &str, start: usize) -> Clause {
        Clause {
            kind,
            label: None,
            fact: false,
            unfold: false,
            text: text.into(),
            span: Span::new(start, start + 1),
            line_span: Span::new(start, start + 1),
        }
    }

    fn trapping_deinitializer(text: &str, start: usize) -> Vec<Stmt> {
        vec![Stmt::Assert(drop_clause(ClauseKind::Assert, text, start))]
    }

    fn drop_class(
        name: &str,
        start: usize,
        fields: Vec<Field>,
        invariants: Vec<Clause>,
        deinit: Option<Vec<Stmt>>,
    ) -> ClassDecl {
        ClassDecl {
            is_pub: false,
            name: name.into(),
            name_span: Span::new(start, start + 1),
            type_params: Vec::new(),
            type_bounds: Vec::new(),
            proof_reuse: ProofReuse::None,
            fields,
            invariants,
            inits: Vec::new(),
            methods: Vec::new(),
            deinit,
            span: Span::new(start, start + 10),
        }
    }

    fn class_field(name: &str, class: usize, start: usize) -> Field {
        Field {
            name: name.into(),
            ty: Ty::Class(class),
            span: Span::new(start, start + 1),
            must_consume: false,
        }
    }

    fn runtime_object(class: usize) -> RtVal {
        RtVal::Obj {
            class,
            fields: Rc::new(RefCell::new(HashMap::new())),
        }
    }

    fn drop_runtime_object(
        classes: Vec<ClassDecl>,
        class: usize,
        fields: &Rc<RefCell<HashMap<String, RtVal>>>,
    ) -> IResult<()> {
        let mut program = empty_program();
        program.classes = classes;
        let control = ControlProgram::build(&program).expect("class-drop probe has exact plans");
        let functions: HashMap<&str, &Fn> = HashMap::new();
        let ghosts = GhostDefs::from_items(&[]);
        let mut interpreter = Interp {
            control: &control,
            fns: &functions,
            classes: &program.classes,
            records: &program.records,
            ghosts: &ghosts,
            source: "",
            fuel: FUEL,
            skipped: Vec::new(),
            raw: RawHeap::default(),
            world: None,
            uart: None,
        };
        interpreter.drop_value(class, fields, "probe")
    }

    #[test]
    fn class_invariant_failure_aborts_the_deinitializer_and_field_suffix() {
        let child = drop_class(
            "Child",
            10,
            Vec::new(),
            Vec::new(),
            Some(trapping_deinitializer("2 = 3", 12)),
        );
        let parent = drop_class(
            "Parent",
            30,
            vec![class_field("child", 0, 31)],
            vec![drop_clause(ClauseKind::Invariant, "1 = 2", 32)],
            Some(trapping_deinitializer("3 = 4", 33)),
        );
        let fields = Rc::new(RefCell::new(HashMap::from([(
            "child".into(),
            runtime_object(0),
        )])));

        let trap = drop_runtime_object(vec![child, parent], 1, &fields)
            .expect_err("the parent invariant must trap");
        assert!(trap.message.contains("class invariant of `Parent`"));
        assert!(trap.message.contains("1 = 2"));
        assert!(
            fields.borrow().contains_key("child"),
            "an invariant trap must not run any later destruction phase"
        );
    }

    #[test]
    fn deinitializer_failure_aborts_the_field_suffix_without_unwind() {
        let child = drop_class(
            "Child",
            10,
            Vec::new(),
            Vec::new(),
            Some(trapping_deinitializer("2 = 3", 12)),
        );
        let parent = drop_class(
            "Parent",
            30,
            vec![class_field("child", 0, 31)],
            Vec::new(),
            Some(trapping_deinitializer("3 = 4", 33)),
        );
        let fields = Rc::new(RefCell::new(HashMap::from([(
            "child".into(),
            runtime_object(0),
        )])));

        let trap = drop_runtime_object(vec![child, parent], 1, &fields)
            .expect_err("the parent deinitializer must trap");
        assert_eq!(trap.message, "inline assert violated: 3 = 4");
        assert!(
            fields.borrow().contains_key("child"),
            "a deinitializer trap must not unwind into field destruction"
        );
    }

    #[test]
    fn recursive_field_failure_uses_reverse_order_and_aborts_the_suffix() {
        let first = drop_class(
            "First",
            10,
            Vec::new(),
            Vec::new(),
            Some(trapping_deinitializer("1 = 2", 12)),
        );
        let second = drop_class(
            "Second",
            30,
            Vec::new(),
            Vec::new(),
            Some(trapping_deinitializer("2 = 3", 32)),
        );
        let parent = drop_class(
            "Parent",
            50,
            vec![class_field("first", 0, 51), class_field("second", 1, 52)],
            Vec::new(),
            None,
        );
        let fields = Rc::new(RefCell::new(HashMap::from([
            ("first".into(), runtime_object(0)),
            ("second".into(), runtime_object(1)),
        ])));

        let trap = drop_runtime_object(vec![first, second, parent], 2, &fields)
            .expect_err("the last-declared child must trap first");
        assert_eq!(trap.message, "inline assert violated: 2 = 3");
        let remaining = fields.borrow();
        assert!(
            !remaining.contains_key("second"),
            "the active child leaves its parent place before recursive destruction"
        );
        assert!(
            remaining.contains_key("first"),
            "a recursive trap must not unwind into the remaining field suffix"
        );
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
        Ty::affine_array_option(Ty::Bool)
    }

    fn public_interp_error(program: &Program) -> String {
        let modules = crate::modules::ModuleSet::single("synthetic".into(), String::new());
        run_unchecked_fn(program, &modules, "subject")
            .expect_err("synthetic affine-option program reached interpreter execution")
    }

    #[test]
    fn affine_options_keep_nonlocal_and_temporary_crossings_closed() {
        let mut return_program = empty_program();
        return_program
            .fns
            .push(function("subject", affine_bool_option(), Vec::new()));
        assert!(
            public_interp_error(&return_program)
                .starts_with("interp.affine_option_position_unsupported:")
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
                mutable: true,
            }],
        ));
        assert!(
            public_interp_error(&local_program).starts_with("interp.affine_option_initializer:")
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
            public_interp_error(&expression_program).starts_with("interp.affine_option_temporary:")
        );
    }

    #[test]
    fn affine_option_take_cannot_replace_its_source_place_in_forged_ast() {
        let span = Span::new(0, 0);
        let mut program = empty_program();
        program.fns.push(function(
            "subject",
            Ty::Unit,
            vec![
                Stmt::Decl {
                    ty: affine_bool_option(),
                    name: "pending".into(),
                    name_span: span,
                    init: Some(expr(ExprKind::NoneE, Some(affine_bool_option()))),
                    mutable: true,
                },
                Stmt::Decl {
                    ty: Ty::array(Ty::Bool),
                    name: "pending".into(),
                    name_span: span,
                    init: Some(affine_take("pending")),
                    mutable: false,
                },
            ],
        ));
        let error = public_interp_error(&program);
        assert!(
            error.starts_with("internal control plan rejected the checked body:"),
            "the shared control identity gate must reject the duplicate before execution: {error}"
        );
        assert!(error.contains("duplicate local `pending`"), "{error}");
    }

    #[test]
    fn affine_option_cannot_launder_through_named_receivers_or_generated_bindings() {
        let span = Span::new(0, 0);
        let scalar = || int_lit(0);
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
            let expression = expr(kind, Some(Ty::Int(IntTy::U64)));
            let locals = HashMap::from([("pending".into(), local(affine_bool_option()))]);
            let error = validate_interp_expr(&expression, &locals)
                .expect_err("affine named receiver must fail closed");
            assert!(
                error.starts_with("interp.affine_option_position_unsupported:")
                    || error.contains("unknown or non-array local"),
                "{error}"
            );
        }

        let mut locals = HashMap::from([("pending".into(), local(affine_bool_option()))]);
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
            validate_interp_stmts(&[expose], &mut locals)
                .unwrap_err()
                .starts_with("interp.affine_option_position_unsupported:")
        );

        let mut locals = HashMap::from([("pending".into(), local(affine_bool_option()))]);
        let allocation = Stmt::StaticAlloc {
            kw_span: span,
            size: scalar(),
            ptr: "pending".into(),
            ptr_span: span,
            res: "pending".into(),
            res_span: span,
        };
        assert!(
            validate_interp_stmts(&[allocation], &mut locals)
                .unwrap_err()
                .starts_with("interp.duplicate_local:")
        );
    }

    fn with_empty_interpreter<R>(run: impl FnOnce(&mut Interp<'_>) -> R) -> R {
        let fns: HashMap<&str, &Fn> = HashMap::new();
        let classes: Vec<ClassDecl> = Vec::new();
        let records: Vec<RecordDecl> = Vec::new();
        let ghosts = GhostDefs::from_items(&[]);
        let control = ControlProgram::default();
        let mut interpreter = Interp {
            control: &control,
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

    fn with_program_interpreter<R>(
        program: &Program,
        run: impl FnOnce(&mut Interp<'_>, &ControlProgram) -> R,
    ) -> R {
        let control = ControlProgram::build(program).expect("test program has exact control");
        let functions: HashMap<&str, &Fn> = program
            .fns
            .iter()
            .map(|function| (function.name.as_str(), function))
            .collect();
        let ghosts = GhostDefs::from_items(&program.ghosts);
        let mut interpreter = Interp {
            control: &control,
            fns: &functions,
            classes: &program.classes,
            records: &program.records,
            ghosts: &ghosts,
            source: "",
            fuel: FUEL,
            skipped: Vec::new(),
            raw: RawHeap::default(),
            world: None,
            uart: None,
        };
        run(&mut interpreter, &control)
    }

    fn fresh_child(span: Span) -> Expr {
        Expr {
            kind: ExprKind::CtorCall {
                class: "Child".into(),
                class_span: span,
                type_args: Vec::new(),
                init: "new".into(),
                args: Vec::new(),
            },
            span,
            ty: Some(Ty::Class(0)),
        }
    }

    fn child_with_deinit(deinit: Option<Vec<Stmt>>) -> ClassDecl {
        let mut child = drop_class("Child", 100, Vec::new(), Vec::new(), deinit);
        let mut initializer = function("new", Ty::Unit, Vec::new());
        initializer.span = Span::new(110, 111);
        initializer.name_span = initializer.span;
        child.inits.push(initializer);
        child
    }

    fn cleanup_statement_program(statement: Stmt, deinit: Option<Vec<Stmt>>) -> Program {
        let mut program = empty_program();
        program.classes.push(child_with_deinit(deinit));
        let mut subject = function("cleanup_subject", Ty::Unit, vec![statement]);
        subject.span = Span::new(200, 240);
        subject.name_span = Span::new(200, 201);
        program.fns.push(subject);
        program
    }

    fn frame_with(vars: HashMap<String, RtVal>) -> Frame {
        Frame {
            vars,
            entry_scalars: HashMap::new(),
            olds: HashMap::new(),
            self_ctx: None,
        }
    }

    fn local(ty: Ty) -> InterpLocal {
        InterpLocal { ty, mutable: true }
    }

    fn bool_array_decl(name: &str) -> Stmt {
        let ty = Ty::array(Ty::Bool);
        Stmt::Decl {
            ty: ty.clone(),
            name: name.into(),
            name_span: Span::new(0, 0),
            init: Some(expr(
                ExprKind::ArrayLit(vec![expr(ExprKind::BoolLit(true), Some(Ty::Bool))]),
                Some(ty),
            )),
            mutable: false,
        }
    }

    fn bool_decl(name: &str, value: bool) -> Stmt {
        Stmt::Decl {
            ty: Ty::Bool,
            name: name.into(),
            name_span: Span::new(0, 0),
            init: Some(expr(ExprKind::BoolLit(value), Some(Ty::Bool))),
            mutable: false,
        }
    }

    fn eval_with_frame(expression: &Expr, vars: HashMap<String, RtVal>) -> Result<RtVal, String> {
        with_empty_interpreter(|interpreter| {
            eval_test_expression(interpreter, expression, &mut frame_with(vars))
                .map_err(|trap| trap.message)
        })
    }

    fn eval_test_expression(
        interpreter: &mut Interp<'_>,
        expression: &Expr,
        frame: &mut Frame,
    ) -> IResult<RtVal> {
        let owner_span = Span::new(usize::MAX - 2, usize::MAX - 1);
        let body = [Stmt::ExprStmt(expression.clone())];
        let plan = BodyPlan::build(
            CallOwner::Function("__interpreter_expression_probe".into()),
            owner_span,
            &[],
            &body,
        )
        .map_err(control_plan_trap)?;
        interpreter.eval(
            expression,
            frame,
            TrapContext::new(&plan, plan.body_scope()),
        )
    }

    fn eval_test_moved(
        interpreter: &mut Interp<'_>,
        expression: &Expr,
        frame: &mut Frame,
    ) -> IResult<RtVal> {
        let owner_span = Span::new(usize::MAX - 2, usize::MAX - 1);
        let body = [Stmt::ExprStmt(expression.clone())];
        let plan = BodyPlan::build(
            CallOwner::Function("__interpreter_move_probe".into()),
            owner_span,
            &[],
            &body,
        )
        .map_err(control_plan_trap)?;
        interpreter.eval_moved(
            expression,
            frame,
            TrapContext::new(&plan, plan.body_scope()),
        )
    }

    #[test]
    fn interpreter_operations_reject_mismatched_and_moved_retained_trap_sites() {
        let trap_span = Span::new(20, 21);
        let integer = |value| Expr {
            kind: ExprKind::IntLit(value),
            span: Span::new(30 + value as usize, 31 + value as usize),
            ty: Some(Ty::Int(IntTy::I32)),
        };
        let arithmetic = |op| Expr {
            kind: ExprKind::Binary {
                op,
                op_span: trap_span,
                lhs: Box::new(integer(4)),
                rhs: Box::new(integer(2)),
            },
            span: trap_span,
            ty: Some(Ty::Int(IntTy::I32)),
        };
        let original = arithmetic(BinOp::Add);
        let body = [Stmt::ExprStmt(original.clone())];
        let plan = BodyPlan::build(
            CallOwner::Function("__retained_trap_probe".into()),
            Span::new(100, 101),
            &[],
            &body,
        )
        .unwrap();

        with_empty_interpreter(|interpreter| {
            let mut frame = frame_with(HashMap::new());
            let error = interpreter
                .eval(
                    &arithmetic(BinOp::Sub),
                    &mut frame,
                    TrapContext::new(&plan, plan.body_scope()),
                )
                .expect_err("the operation must exact-lookup its sealed semantic kind");
            assert!(error.undef);
            assert!(error.message.contains("SubOverflow"), "{}", error.message);
        });

        let branch_anchor = Span::new(110, 111);
        let scoped_body = [Stmt::If {
            cond: Expr {
                kind: ExprKind::BoolLit(true),
                span: branch_anchor,
                ty: Some(Ty::Bool),
            },
            then_block: vec![Stmt::ExprStmt(original.clone())],
            else_block: Some(Vec::new()),
        }];
        let scoped = BodyPlan::build(
            CallOwner::Function("__moved_trap_probe".into()),
            Span::new(120, 121),
            &[],
            &scoped_body,
        )
        .unwrap();
        let else_scope = scoped
            .branch(scoped.body_scope(), branch_anchor, true)
            .unwrap()
            .else_arm()
            .unwrap()
            .scope();
        with_empty_interpreter(|interpreter| {
            let mut frame = frame_with(HashMap::new());
            let error = interpreter
                .eval(&original, &mut frame, TrapContext::new(&scoped, else_scope))
                .expect_err("moving the same operation to a sibling scope must fail");
            assert!(error.undef);
            assert!(error.message.contains("active lexical scope"));
        });
    }

    fn eval_with_empty_runtime(expression: &Expr) -> Result<RtVal, String> {
        eval_with_frame(expression, HashMap::new())
    }

    fn affine_option(value: Option<Rc<RefCell<RtArray>>>) -> RtVal {
        RtVal::AffineOptBoolArray(value)
    }

    fn affine_is_some(name: &str) -> Expr {
        expr(
            ExprKind::IsSome {
                operand: Box::new(expr(ExprKind::Var(name.into()), Some(affine_bool_option()))),
            },
            Some(Ty::Bool),
        )
    }

    fn affine_take(name: &str) -> Expr {
        expr(
            ExprKind::OptTake {
                option: name.into(),
                option_span: Span::new(0, 0),
            },
            Some(Ty::array(Ty::Bool)),
        )
    }

    fn affine_some_decl(name: &str) -> Stmt {
        let array_ty = Ty::array(Ty::Bool);
        Stmt::Decl {
            ty: affine_bool_option(),
            name: name.into(),
            name_span: Span::new(0, 0),
            init: Some(expr(
                ExprKind::SomeE(Box::new(expr(
                    ExprKind::AllocArray {
                        elem: Ty::Bool,
                        len: Box::new(int_lit(1)),
                        init: Box::new(expr(ExprKind::BoolLit(true), Some(Ty::Bool))),
                    },
                    Some(array_ty),
                ))),
                Some(affine_bool_option()),
            )),
            mutable: true,
        }
    }

    #[test]
    fn affine_presence_is_nonconsuming_and_take_clears_the_slot_atomically() {
        let array = Rc::new(RefCell::new(rt_bools(&[true, false])));
        let option = affine_option(Some(array.clone()));
        let mut frame = frame_with(HashMap::from([("pending".into(), option)]));

        let presence = with_empty_interpreter(|interpreter| {
            eval_test_expression(interpreter, &affine_is_some("pending"), &mut frame)
                .unwrap_or_else(|trap| panic!("presence test trapped: {}", trap.message))
        });
        assert!(matches!(presence, RtVal::Bool(true)));
        assert!(matches!(
            frame.vars.get("pending"),
            Some(RtVal::AffineOptBoolArray(Some(_)))
        ));
        assert_eq!(Rc::strong_count(&array), 2);

        let taken = with_empty_interpreter(|interpreter| {
            eval_test_expression(interpreter, &affine_take("pending"), &mut frame)
                .unwrap_or_else(|trap| panic!("present take trapped: {}", trap.message))
        });
        let RtVal::Arr(taken_array) = taken else {
            panic!("take did not return an array")
        };
        assert!(Rc::ptr_eq(&taken_array, &array));
        assert!(matches!(
            frame.vars.get("pending"),
            Some(RtVal::AffineOptBoolArray(None))
        ));

        let trap = with_empty_interpreter(|interpreter| {
            eval_test_expression(interpreter, &affine_take("pending"), &mut frame)
                .expect_err("second take must trap")
        });
        assert_eq!(trap.message, "`.take` of an empty affine option");
        assert!(matches!(
            frame.vars.get("pending"),
            Some(RtVal::AffineOptBoolArray(None))
        ));
    }

    #[test]
    fn dropping_an_affine_option_releases_a_present_payload_once() {
        let array = Rc::new(RefCell::new(rt_bools(&[true])));
        let mut frame = frame_with(HashMap::from([(
            "pending".into(),
            affine_option(Some(array.clone())),
        )]));
        assert_eq!(Rc::strong_count(&array), 2);

        with_empty_interpreter(|interpreter| {
            interpreter
                .drop_place(&RtPlace::Local("pending".into()), &mut frame)
                .unwrap_or_else(|trap| panic!("affine option drop trapped: {}", trap.message))
        });

        assert!(!frame.vars.contains_key("pending"));
        assert_eq!(Rc::strong_count(&array), 1);
    }

    #[test]
    fn a_trap_does_not_unwind_a_present_affine_option() {
        let mut frame = frame_with(HashMap::new());
        let mut pending = affine_some_decl("pending");
        let Stmt::Decl {
            init:
                Some(Expr {
                    kind: ExprKind::SomeE(payload),
                    ..
                }),
            ..
        } = &mut pending
        else {
            unreachable!("fixture is an affine option containing a fresh array")
        };
        payload.span = Span::new(10, 11);
        let body = vec![
            pending,
            bool_array_decl("trap_source"),
            Stmt::ExprStmt(expr(
                ExprKind::Index {
                    array: "trap_source".into(),
                    array_span: Span::new(0, 0),
                    index: Box::new(int_lit(1)),
                },
                Some(Ty::Bool),
            )),
        ];

        let trap = with_empty_interpreter(|interpreter| {
            match interpreter.exec_test_block(&body, &mut frame) {
                Ok(_) => panic!("out-of-bounds access must trap"),
                Err(trap) => trap,
            }
        });
        assert_eq!(trap.message, "index out of bounds: index 1, length 1");
        let Some(RtVal::AffineOptBoolArray(value)) = frame.vars.get("pending") else {
            panic!("trap unwound the affine option place")
        };
        assert!(value.is_some());
    }

    #[test]
    fn affine_option_snapshots_detach_proof_data_from_runtime_ownership() {
        let array = Rc::new(RefCell::new(rt_bools(&[true, false])));
        let mut option = affine_option(Some(array.clone()));
        let snapshot = spec_of(&option).expect("monitor snapshot");
        let RtVal::AffineOptBoolArray(value) = &mut option else {
            unreachable!()
        };

        let removed = value.take().expect("present payload");
        drop(removed);
        assert_eq!(Rc::strong_count(&array), 1);
        assert_eq!(
            snapshot,
            SpecVal::AffineOpt {
                value: Some(Box::new(SpecVal::Arr(crate::speceval::spec_bools(&[
                    true, false
                ])))),
            }
        );
    }

    #[test]
    fn dropping_an_array_place_removes_its_binding_and_releases_its_rc() {
        let storage = Rc::new(RefCell::new(rt_bools(&[true])));
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
    fn retained_array_drop_action_rejects_a_runtime_payload_mismatch() {
        let declaration = bool_array_decl("flags");
        let plan = BodyPlan::build(
            CallOwner::Function("array_drop_payload_probe".into()),
            Span::new(40, 41),
            &[],
            std::slice::from_ref(&declaration),
        )
        .expect("Boolean owner has one retained drop action");
        let candidate = plan
            .candidate_for_place(&Place::local("flags"))
            .expect("Boolean owner is a cleanup candidate");
        let action = candidate.drop_action().clone();
        let wrong = Rc::new(RefCell::new(rt_ints(IntTy::U8, &[1])));

        with_empty_interpreter(|interpreter| {
            let validation = interpreter
                .validate_runtime_value_for_action(
                    &RtVal::Arr(wrong.clone()),
                    &action,
                    "flags",
                    candidate.span(),
                )
                .expect_err("validation must consume the retained element identity");
            assert!(validation.undef);
            assert!(validation.message.contains("internal control plan"));
            assert!(validation.message.contains("payload `u8`"));
            assert!(validation.message.contains("retained payload `bool`"));

            let drop = interpreter
                .drop_runtime_value_with_action(
                    RtVal::Arr(wrong),
                    &action,
                    "flags",
                    candidate.span(),
                )
                .expect_err("destruction must consume the retained element identity too");
            assert!(drop.undef);
            assert_eq!(drop.message, validation.message);
        });
    }

    #[test]
    fn eval_moved_takes_an_owned_integer_array_place() {
        let storage = Rc::new(RefCell::new(rt_ints(IntTy::U64, &[7])));
        let mut frame = frame_with(HashMap::from([(
            "values".into(),
            RtVal::Arr(storage.clone()),
        )]));
        let read = expr(
            ExprKind::Var("values".into()),
            Some(Ty::array(Ty::Int(IntTy::U64))),
        );

        let value = with_empty_interpreter(|interpreter| {
            eval_test_moved(interpreter, &read, &mut frame)
                .unwrap_or_else(|trap| panic!("unexpected array-move trap: {}", trap.message))
        });

        assert!(!frame.vars.contains_key("values"));
        assert!(matches!(&value, RtVal::Arr(_)));
        assert_eq!(Rc::strong_count(&storage), 2);
    }

    #[test]
    fn planned_assignment_installs_into_a_moved_out_owner_without_dropping_twice() {
        let declaration_span = Span::new(10, 11);
        let assignment_span = Span::new(20, 21);
        let assignment = Stmt::Assign {
            name: "destination".into(),
            name_span: assignment_span,
            value: expr(ExprKind::Var("fresh".into()), Some(Ty::Class(0))),
        };
        let body = vec![
            Stmt::Decl {
                ty: Ty::Class(0),
                name: "destination".into(),
                name_span: declaration_span,
                init: None,
                mutable: true,
            },
            assignment.clone(),
        ];
        let plan = BodyPlan::build(
            CallOwner::Function("moved_out_assignment_probe".into()),
            Span::new(1, 30),
            &[],
            &body,
        )
        .expect("class replacement has a planned action");
        let mut control = ExecutionControl::new(&plan);
        control
            .arm("destination", plan.body_scope(), declaration_span)
            .unwrap();
        let fields = Rc::new(RefCell::new(HashMap::new()));
        let mut frame = frame_with(HashMap::from([(
            "fresh".into(),
            RtVal::Obj {
                class: 0,
                fields: fields.clone(),
            },
        )]));

        with_empty_interpreter(|interpreter| {
            assert!(matches!(
                interpreter.exec_stmt(
                    &assignment,
                    plan.body_block().statements()[1].kind(),
                    &mut frame,
                    &mut control,
                    plan.body_scope(),
                ),
                Ok(Flow::Normal)
            ));
        });

        assert!(!frame.vars.contains_key("fresh"));
        let Some(RtVal::Obj {
            fields: installed, ..
        }) = frame.vars.get("destination")
        else {
            panic!("planned assignment did not install the staged owner")
        };
        assert!(Rc::ptr_eq(installed, &fields));
    }

    #[test]
    fn trapping_assignment_rhs_leaves_the_old_planned_owner_live() {
        let declaration_span = Span::new(10, 11);
        let assignment = Stmt::Assign {
            name: "destination".into(),
            name_span: Span::new(20, 21),
            value: expr(
                ExprKind::Index {
                    array: "trap_source".into(),
                    array_span: Span::new(22, 23),
                    index: Box::new(int_lit(1)),
                },
                Some(Ty::Class(0)),
            ),
        };
        let body = vec![
            Stmt::Decl {
                ty: Ty::Class(0),
                name: "destination".into(),
                name_span: declaration_span,
                init: None,
                mutable: true,
            },
            assignment.clone(),
        ];
        let plan = BodyPlan::build(
            CallOwner::Function("trapping_assignment_probe".into()),
            Span::new(1, 30),
            &[],
            &body,
        )
        .expect("class replacement has a planned action");
        let mut control = ExecutionControl::new(&plan);
        control
            .arm("destination", plan.body_scope(), declaration_span)
            .unwrap();
        let old_fields = Rc::new(RefCell::new(HashMap::new()));
        let trap_source = Rc::new(RefCell::new(rt_bools(&[true])));
        let mut frame = frame_with(HashMap::from([
            (
                "destination".into(),
                RtVal::Obj {
                    class: 0,
                    fields: old_fields.clone(),
                },
            ),
            ("trap_source".into(), RtVal::Arr(trap_source)),
        ]));

        let trap = with_empty_interpreter(|interpreter| {
            match interpreter.exec_stmt(
                &assignment,
                plan.body_block().statements()[1].kind(),
                &mut frame,
                &mut control,
                plan.body_scope(),
            ) {
                Err(trap) => trap,
                Ok(_) => panic!("the RHS index must trap before replacement"),
            }
        });

        assert_eq!(trap.message, "index out of bounds: index 1, length 1");
        let Some(RtVal::Obj {
            fields: retained, ..
        }) = frame.vars.get("destination")
        else {
            panic!("trapping RHS destroyed the old destination")
        };
        assert!(Rc::ptr_eq(retained, &old_fields));
    }

    #[test]
    fn retained_field_action_uses_dynamic_presence_for_first_install_moved_absence_and_replacement()
    {
        let field_span = Span::new(210, 211);
        let statement = Stmt::FieldAssign {
            field: "child".into(),
            field_span,
            value: expr(ExprKind::Var("fresh".into()), Some(Ty::Class(0))),
        };
        let program = cleanup_statement_program(statement.clone(), None);

        // `None` is deliberately both a constructor's first install and a
        // method destination whose old owner was moved out: representation
        // liveness makes them the same action state.
        for old in [None, Some(runtime_object(0))] {
            with_program_interpreter(&program, |interpreter, control_program| {
                let body = control_program
                    .body(
                        &CallOwner::Function("cleanup_subject".into()),
                        program.fns[0].span,
                    )
                    .unwrap();
                let plan = body.plan();
                let mut execution = ExecutionControl::new(plan);
                let installed_fields = Rc::new(RefCell::new(HashMap::new()));
                let object_fields = Rc::new(RefCell::new(HashMap::new()));
                if let Some(old) = old {
                    object_fields.borrow_mut().insert("child".into(), old);
                }
                let mut frame = frame_with(HashMap::from([(
                    "fresh".into(),
                    RtVal::Obj {
                        class: 0,
                        fields: installed_fields.clone(),
                    },
                )]));
                frame.self_ctx = Some((0, object_fields.clone()));

                assert!(matches!(
                    interpreter.exec_stmt(
                        &statement,
                        plan.body_block().statements()[0].kind(),
                        &mut frame,
                        &mut execution,
                        plan.body_scope(),
                    ),
                    Ok(Flow::Normal)
                ));
                assert!(!frame.vars.contains_key("fresh"));
                let fields = object_fields.borrow();
                let Some(RtVal::Obj {
                    fields: installed, ..
                }) = fields.get("child")
                else {
                    panic!("retained field action did not install its staged RHS")
                };
                assert!(Rc::ptr_eq(installed, &installed_fields));
            });
        }
    }

    #[test]
    fn trapping_field_rhs_precedes_the_retained_destination_drop() {
        let statement = Stmt::FieldAssign {
            field: "child".into(),
            field_span: Span::new(210, 211),
            value: Expr {
                kind: ExprKind::Index {
                    array: "trap_source".into(),
                    array_span: Span::new(212, 213),
                    index: Box::new(int_lit(1)),
                },
                span: Span::new(212, 214),
                ty: Some(Ty::Class(0)),
            },
        };
        let program = cleanup_statement_program(statement.clone(), None);
        with_program_interpreter(&program, |interpreter, control_program| {
            let body = control_program
                .body(
                    &CallOwner::Function("cleanup_subject".into()),
                    program.fns[0].span,
                )
                .unwrap();
            let plan = body.plan();
            let mut execution = ExecutionControl::new(plan);
            let old_fields = Rc::new(RefCell::new(HashMap::new()));
            let object_fields = Rc::new(RefCell::new(HashMap::from([(
                "child".into(),
                RtVal::Obj {
                    class: 0,
                    fields: old_fields.clone(),
                },
            )])));
            let mut frame = frame_with(HashMap::from([(
                "trap_source".into(),
                RtVal::Arr(Rc::new(RefCell::new(rt_bools(&[true])))),
            )]));
            frame.self_ctx = Some((0, object_fields.clone()));

            let trap = match interpreter.exec_stmt(
                &statement,
                plan.body_block().statements()[0].kind(),
                &mut frame,
                &mut execution,
                plan.body_scope(),
            ) {
                Err(trap) => trap,
                Ok(_) => panic!("RHS must trap before replacement"),
            };
            assert_eq!(trap.message, "index out of bounds: index 1, length 1");
            let fields = object_fields.borrow();
            let Some(RtVal::Obj {
                fields: retained, ..
            }) = fields.get("child")
            else {
                panic!("RHS trap removed the old field destination")
            };
            assert!(Rc::ptr_eq(retained, &old_fields));
        });
    }

    #[test]
    fn discarded_class_temporary_runs_its_retained_drop_and_trap_skips_continuation() {
        let temporary = Stmt::ExprStmt(fresh_child(Span::new(210, 211)));
        let mut program =
            cleanup_statement_program(temporary, Some(trapping_deinitializer("1 = 2", 120)));
        program.fns[0]
            .body
            .push(Stmt::Assert(drop_clause(ClauseKind::Assert, "3 = 4", 220)));

        let modules = crate::modules::ModuleSet::single("synthetic".into(), String::new());
        let trap = run_unchecked_fn(&program, &modules, "cleanup_subject")
            .expect_err("discarded result deinitializer must trap");
        assert!(trap.contains("inline assert violated: 1 = 2"), "{trap}");
    }

    #[test]
    fn successful_branch_and_loop_blocks_clear_all_planned_locals() {
        let mut frame = frame_with(HashMap::new());
        let branch = Stmt::If {
            cond: expr(ExprKind::BoolLit(true), Some(Ty::Bool)),
            then_block: vec![
                bool_array_decl("branch_flags"),
                bool_decl("branch_scalar", true),
            ],
            else_block: None,
        };
        let loop_stmt = Stmt::While {
            cond: expr(ExprKind::Var("again".into()), Some(Ty::Bool)),
            invariants: Vec::new(),
            variant: None,
            kw_span: Span::new(0, 0),
            body: vec![
                bool_array_decl("loop_flags"),
                bool_decl("loop_scalar", true),
                Stmt::Assign {
                    name: "again".into(),
                    name_span: Span::new(0, 0),
                    value: expr(ExprKind::BoolLit(false), Some(Ty::Bool)),
                },
            ],
        };
        let loop_probe = vec![
            Stmt::Decl {
                ty: Ty::Bool,
                name: "again".into(),
                name_span: Span::new(1, 2),
                init: Some(expr(ExprKind::BoolLit(true), Some(Ty::Bool))),
                mutable: true,
            },
            loop_stmt,
        ];

        with_empty_interpreter(|interpreter| {
            assert!(matches!(
                interpreter.exec_test_stmt(&branch, &mut frame),
                Ok(Flow::Normal)
            ));
            assert!(!frame.vars.contains_key("branch_flags"));
            assert!(!frame.vars.contains_key("branch_scalar"));
            assert!(matches!(
                interpreter.exec_test_block(&loop_probe, &mut frame),
                Ok(Flow::Normal)
            ));
        });

        assert!(!frame.vars.contains_key("loop_flags"));
        assert!(!frame.vars.contains_key("loop_scalar"));
        assert!(!frame.vars.contains_key("again"));
    }

    #[test]
    fn early_return_consumes_the_planned_nested_cleanup_route() {
        let mut frame = frame_with(HashMap::new());
        let mut condition = expr(ExprKind::BoolLit(true), Some(Ty::Bool));
        condition.span = Span::new(10, 11);
        let body = vec![
            bool_array_decl("outer_flags"),
            bool_decl("outer_scalar", true),
            Stmt::If {
                cond: condition,
                then_block: vec![
                    bool_array_decl("inner_flags"),
                    bool_decl("inner_scalar", true),
                    Stmt::Return {
                        value: None,
                        span: Span::new(20, 21),
                    },
                ],
                else_block: None,
            },
        ];

        with_empty_interpreter(|interpreter| {
            assert!(matches!(
                interpreter.exec_test_block(&body, &mut frame),
                Ok(Flow::Return(RtVal::Unit))
            ));
        });
        assert!(!frame.vars.contains_key("inner_flags"));
        assert!(!frame.vars.contains_key("inner_scalar"));
        assert!(!frame.vars.contains_key("outer_flags"));
        assert!(!frame.vars.contains_key("outer_scalar"));
    }

    #[test]
    fn exposure_uses_its_planned_clear_route_for_source_and_body_bindings() {
        let span = Span::new(40, 41);
        let bytes = RtArray::from_values(Ty::Int(IntTy::U8), vec![RtVal::Int(7)], span)
            .expect("byte array fixture");
        let mut frame = frame_with(HashMap::from([(
            "bytes".into(),
            RtVal::Arr(Rc::new(RefCell::new(bytes))),
        )]));
        let exposure = Stmt::Expose {
            kw_span: span,
            array: "bytes".into(),
            array_span: Span::new(41, 42),
            mutable: false,
            ptr: "loan_ptr".into(),
            ptr_span: Span::new(42, 43),
            res: "loan_res".into(),
            res_span: Span::new(43, 44),
            body: vec![bool_decl("loan_scalar", true)],
        };
        let parameter = Param {
            name: "bytes".into(),
            ty: Ty::array(Ty::Int(IntTy::U8)),
            span: Span::new(39, 40),
            consumes: false,
        };
        let owner_span = Span::new(38, 39);
        let body = std::slice::from_ref(&exposure);
        let plan = BodyPlan::build(
            CallOwner::Function("__interpreter_exposure_probe".into()),
            owner_span,
            std::slice::from_ref(&parameter),
            body,
        )
        .expect("exposure probe has a typed source binding");
        let release = plan
            .exposure_plan(plan.body_scope(), span)
            .unwrap()
            .normal()
            .unwrap()
            .release_loan()
            .root()
            .to_owned();

        with_empty_interpreter(|interpreter| {
            let mut control = ExecutionControl::new(&plan);
            control
                .arm("bytes", plan.frame_scope(), parameter.span)
                .expect("the owned parameter has its retained cleanup candidate");
            assert!(matches!(
                interpreter.exec_stmt(
                    &exposure,
                    plan.body_block().statements()[0].kind(),
                    &mut frame,
                    &mut control,
                    plan.body_scope(),
                ),
                Ok(Flow::Normal)
            ));
            assert!(!frame.vars.contains_key(release.as_str()));
            assert!(
                interpreter
                    .raw
                    .allocs
                    .values()
                    .all(|allocation| !allocation.live)
            );
        });

        assert!(frame.vars.contains_key("bytes"));
        assert!(!frame.vars.contains_key("loan_ptr"));
        assert!(!frame.vars.contains_key("loan_res"));
        assert!(!frame.vars.contains_key("loan_scalar"));
    }

    #[test]
    fn exposure_rejects_forged_source_mutability_and_pointer_before_opening_loan() {
        let span = Span::new(60, 61);
        let exposure = Stmt::Expose {
            kw_span: span,
            array: "bytes".into(),
            array_span: Span::new(61, 62),
            mutable: false,
            ptr: "loan_ptr".into(),
            ptr_span: Span::new(62, 63),
            res: "loan_res".into(),
            res_span: Span::new(63, 64),
            body: vec![bool_decl("loan_scalar", true)],
        };
        let parameters = [
            Param {
                name: "bytes".into(),
                ty: Ty::array(Ty::Int(IntTy::U8)),
                span: Span::new(58, 59),
                consumes: false,
            },
            Param {
                name: "other".into(),
                ty: Ty::array(Ty::Int(IntTy::U8)),
                span: Span::new(59, 60),
                consumes: false,
            },
        ];
        let body = std::slice::from_ref(&exposure);
        let plan = BodyPlan::build(
            CallOwner::Function("__interpreter_exposure_identity_probe".into()),
            Span::new(57, 58),
            &parameters,
            body,
        )
        .expect("exposure identity probe has two typed byte-array bindings");

        let mut swapped_owner = exposure.clone();
        let Stmt::Expose { array, .. } = &mut swapped_owner else {
            unreachable!()
        };
        *array = "other".into();

        let mut changed_mutability = exposure.clone();
        let Stmt::Expose { mutable, .. } = &mut changed_mutability else {
            unreachable!()
        };
        *mutable = true;

        let mut changed_pointer = exposure.clone();
        let Stmt::Expose { ptr, .. } = &mut changed_pointer else {
            unreachable!()
        };
        *ptr = "forged_ptr".into();

        for forged in [swapped_owner, changed_mutability, changed_pointer] {
            with_empty_interpreter(|interpreter| {
                let array = |value| {
                    RtVal::Arr(Rc::new(RefCell::new(
                        RtArray::from_values(Ty::Int(IntTy::U8), vec![RtVal::Int(value)], span)
                            .expect("byte array fixture"),
                    )))
                };
                let mut frame = frame_with(HashMap::from([
                    ("bytes".into(), array(7)),
                    ("other".into(), array(9)),
                ]));
                let mut control = ExecutionControl::new(&plan);
                let outcome = interpreter.exec_stmt(
                    &forged,
                    plan.body_block().statements()[0].kind(),
                    &mut frame,
                    &mut control,
                    plan.body_scope(),
                );
                let Err(trap) = outcome else {
                    panic!("forged exposure identity reached execution")
                };
                assert!(trap.undef, "{}", trap.message);
                assert!(
                    trap.message.contains("retained rebuild action"),
                    "{}",
                    trap.message
                );
                assert!(
                    interpreter.raw.allocs.is_empty(),
                    "identity rejection must precede loan allocation"
                );
                assert!(!frame.vars.contains_key("loan_ptr"));
                assert!(!frame.vars.contains_key("forged_ptr"));
                assert!(!frame.vars.contains_key("loan_res"));
                assert!(!frame.vars.contains_key("loan_scalar"));
            });
        }
    }

    #[test]
    fn trapped_blocks_retain_scalar_and_owner_places_without_running_cleanup() {
        let mut frame = frame_with(HashMap::new());
        let body = vec![
            bool_decl("trapped_scalar", true),
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

        let trapped = with_empty_interpreter(|interpreter| {
            match interpreter.exec_test_block(&body, &mut frame) {
                Err(trap) => trap,
                Ok(_) => panic!("out-of-bounds index should trap"),
            }
        });

        assert_eq!(trapped.message, "index out of bounds: index 1, length 1");
        assert!(frame.vars.contains_key("trapped_scalar"));
        assert!(frame.vars.contains_key("trapped_flags"));
    }

    #[test]
    fn unsafe_marker_keeps_array_local_in_the_enclosing_scope() {
        let mut frame = frame_with(HashMap::new());
        let unsafe_block = Stmt::Unsafe {
            kw_span: Span::new(0, 0),
            body: vec![bool_array_decl("open_flags")],
        };
        with_empty_interpreter(|interpreter| {
            assert!(matches!(
                interpreter.exec_test_stmt(&unsafe_block, &mut frame),
                Ok(Flow::Normal)
            ));
        });

        assert!(frame.vars.contains_key("open_flags"));
    }

    #[test]
    fn rejects_option_payloads_without_g1_runtime_semantics() {
        let unsupported = [
            Ty::Record(0),
            Ty::Param(TypeParamId::from_legacy(0)),
            Ty::Int(IntTy::TParam(0)),
        ];

        for payload in unsupported {
            let mut program = empty_program();
            program
                .fns
                .push(function("subject", Ty::option(payload.clone()), Vec::new()));
            let error = validate_interp_program(&program)
                .expect_err("an unsupported option payload must fail closed");
            assert!(
                error.starts_with("interp.aggregate_payload_unsupported:"),
                "{payload:?}: {error}"
            );
        }
    }

    /// An owned Boolean array is a local value; a borrowed one is a second
    /// name for a caller's storage and runs wherever `&[T]` runs. The
    /// interpreter's array is payload-tagged and a borrow's value is the
    /// caller's own `Rc`, so length, index, and store are one implementation
    /// over the tag — which is why the mode, not the element type, is what
    /// the position gate reads.
    #[test]
    fn an_owned_bool_array_is_a_local_value_and_a_borrowed_one_is_a_parameter() {
        let mut program = empty_program();
        program.fns.push(function(
            "subject",
            Ty::Unit,
            vec![Stmt::Decl {
                ty: Ty::array(Ty::Bool),
                name: "flags".into(),
                name_span: Span::new(0, 0),
                init: Some(expr(
                    ExprKind::AllocArray {
                        elem: Ty::Bool,
                        len: Box::new(int_lit(0)),
                        init: Box::new(expr(ExprKind::BoolLit(false), Some(Ty::Bool))),
                    },
                    Some(Ty::array(Ty::Bool)),
                )),
                mutable: true,
            }],
        ));

        validate_interp_program(&program)
            .expect("owned local Boolean arrays have interpreter semantics");
        for ty in [
            Ty::array_ref(Ty::Bool, Mutability::Shared),
            Ty::array_ref(Ty::Bool, Mutability::Mut),
        ] {
            validate_interp_ty(ty.clone(), "Boolean array borrow")
                .expect("a borrowed Boolean array is an executable value");
            validate_interp_param_ty(ty, "parameter `m`")
                .expect("a borrowed Boolean array is an ordinary parameter");
        }
        // An owner crosses too, by moving: the caller's place dies at the
        // argument and the shared frame-exit route destroys what the callee
        // received after its posts (ADR 0085). What stays refused is an affine
        // option, which has no call boundary at all.
        validate_interp_param_ty(Ty::array(Ty::Bool), "parameter `flags`")
            .expect("an owned Boolean array is handed over at a call");
        assert!(
            validate_interp_param_ty(Ty::option(Ty::array(Ty::Bool)), "parameter `held`")
                .unwrap_err()
                .starts_with("interp.affine_option_position_unsupported:")
        );
    }

    /// A `&mut [bool]` argument names the caller's storage, so the callee's
    /// store is visible to the caller with no write-back step: the borrow
    /// hands over the same handle, and the owner — not the callee — destroys
    /// the array. Both halves are what makes lending a Boolean array
    /// different from moving one.
    #[test]
    fn a_unique_bool_array_borrow_writes_through_to_its_owner() {
        let bool_array = Ty::array(Ty::Bool);
        let mut program = empty_program();

        let mut writer = function(
            "writer",
            Ty::Unit,
            vec![Stmt::Store {
                array: "m".into(),
                array_span: Span::new(0, 0),
                index: int_lit(1),
                value: expr(ExprKind::BoolLit(true), Some(Ty::Bool)),
            }],
        );
        writer.params.push(Param {
            name: "m".into(),
            ty: Ty::array_ref(Ty::Bool, Mutability::Mut),
            span: Span::new(0, 0),
            consumes: false,
        });
        program.fns.push(writer);

        program.fns.push(function(
            "subject",
            Ty::Bool,
            vec![
                Stmt::Decl {
                    ty: bool_array.clone(),
                    name: "flags".into(),
                    name_span: Span::new(0, 0),
                    init: Some(expr(
                        ExprKind::AllocArray {
                            elem: Ty::Bool,
                            len: Box::new(int_lit(2)),
                            init: Box::new(expr(ExprKind::BoolLit(false), Some(Ty::Bool))),
                        },
                        Some(bool_array.clone()),
                    )),
                    mutable: true,
                },
                Stmt::ExprStmt(expr(
                    ExprKind::Call {
                        callee: "writer".into(),
                        callee_span: Span::new(0, 0),
                        type_args: vec![],
                        args: vec![expr(
                            ExprKind::Borrow {
                                array: "flags".into(),
                                field: None,
                                mutable: true,
                            },
                            Some(Ty::array_ref(Ty::Bool, Mutability::Mut)),
                        )],
                    },
                    Some(Ty::Unit),
                )),
                Stmt::Return {
                    value: Some(expr(
                        ExprKind::Index {
                            array: "flags".into(),
                            array_span: Span::new(0, 0),
                            index: Box::new(int_lit(1)),
                        },
                        Some(Ty::Bool),
                    )),
                    span: Span::new(0, 0),
                },
            ],
        ));

        let modules = crate::modules::ModuleSet::single("synthetic".into(), String::new());
        assert!(
            matches!(
                run_unchecked_fn(&program, &modules, "subject"),
                Ok(RtVal::Bool(true))
            ),
            "a store through a unique borrow must be visible to the owner"
        );
    }

    #[test]
    fn option_parameters_execute_and_stored_option_fields_split_by_container() {
        for payload in [Ty::Bool, Ty::Int(IntTy::U64)] {
            validate_interp_param_ty(Ty::option(payload.clone()), "parameter `value`")
                .expect("a copyable option parameter is an executable value");
            validate_interp_class_field_ty(Ty::option(payload.clone()), "field `Box.value`")
                .expect("a copyable option class field is an executable value");
            let error = validate_interp_field_ty(Ty::option(payload), "field `Pair.value`")
                .expect_err("options must not acquire a record byte-layout ABI");
            assert!(error.starts_with("interp.option_position_unsupported:"));
        }
        let affine = validate_interp_param_ty(Ty::option(Ty::array(Ty::Bool)), "parameter `value`")
            .expect_err("an affine option has no parameter ABI");
        assert!(affine.starts_with("interp.affine_option_position_unsupported:"));
        let generic = validate_interp_param_ty(
            Ty::option(Ty::Param(TypeParamId::from_legacy(0))),
            "parameter `value`",
        )
        .expect_err("an unresolved option payload is not executable");
        assert!(generic.starts_with("interp.aggregate_payload_unsupported:"));
    }

    #[test]
    fn boolean_option_construction_access_and_empty_trap_are_typed() {
        let some_false = expr(
            ExprKind::SomeE(Box::new(expr(ExprKind::BoolLit(false), Some(Ty::Bool)))),
            Some(Ty::option(Ty::Bool)),
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

        let none = expr(ExprKind::NoneE, Some(Ty::option(Ty::Bool)));
        let runtime_none = eval_with_empty_runtime(&none).unwrap();
        assert_eq!(
            spec_of(&runtime_none),
            Some(SpecVal::Opt {
                payload: Some(Ty::Bool),
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
            payload: Ty::Bool,
            value: Some(Box::new(RtVal::Bool(false))),
        };
        let copied = deep_copy(&original);
        assert!(matches!(
            copied,
            RtVal::Opt {
                payload: Ty::Bool,
                value: Some(value),
            } if matches!(*value, RtVal::Bool(false))
        ));
    }

    #[test]
    fn recursively_accepts_boolean_alloc_array_element_metadata() {
        let allocation = expr(
            ExprKind::AllocArray {
                elem: Ty::Bool,
                len: Box::new(int_lit(1)),
                init: Box::new(expr(ExprKind::BoolLit(false), Some(Ty::Bool))),
            },
            Some(Ty::array(Ty::Bool)),
        );
        let mut program = empty_program();
        program.fns.push(function(
            "subject",
            Ty::Unit,
            vec![Stmt::Decl {
                ty: Ty::array(Ty::Bool),
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
                    ty: Ty::array(Ty::Bool),
                    name: "values".into(),
                    name_span: Span::new(0, 0),
                    init: Some(expr(
                        ExprKind::ArrayLit(vec![expr(ExprKind::BoolLit(true), Some(Ty::Bool))]),
                        Some(Ty::array(Ty::Bool)),
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
        let bool_ty = Ty::array(Ty::Bool);
        let literal = expr(
            ExprKind::ArrayLit(vec![
                expr(ExprKind::BoolLit(true), Some(Ty::Bool)),
                expr(ExprKind::BoolLit(false), Some(Ty::Bool)),
            ]),
            Some(bool_ty.clone()),
        );
        let RtVal::Arr(values) = eval_with_empty_runtime(&literal).unwrap() else {
            panic!("expected an array")
        };
        assert_eq!(values.borrow().payload(), Ty::Bool);
        assert_eq!(rt_bools_of(&values.borrow()), vec![true, false]);

        let allocated = expr(
            ExprKind::AllocArray {
                elem: Ty::Bool,
                len: Box::new(int_lit(2)),
                init: Box::new(expr(ExprKind::BoolLit(true), Some(Ty::Bool))),
            },
            Some(bool_ty),
        );
        let RtVal::Arr(values) = eval_with_empty_runtime(&allocated).unwrap() else {
            panic!("expected an array")
        };
        values
            .borrow_mut()
            .set(1, RtVal::Bool(false), Span::new(0, 0))
            .expect("a Boolean value inhabits a Boolean payload");
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

        let empty = RtVal::Arr(Rc::new(RefCell::new(rt_bools(&[]))));
        assert_eq!(
            spec_of(&empty),
            Some(SpecVal::Arr(crate::speceval::spec_bools(&[])))
        );
        let RtVal::Arr(copied) = deep_copy(&empty) else {
            panic!("expected copied array")
        };
        assert_eq!(copied.borrow().payload(), Ty::Bool);
        assert_eq!(copied.borrow().len(), 0);
    }

    #[test]
    fn boolean_array_guard_rejects_forged_payloads_indices_stores_and_transports() {
        let bool_array = Ty::array(Ty::Bool);
        let bad_alloc = expr(
            ExprKind::AllocArray {
                elem: Ty::Bool,
                len: Box::new(expr(ExprKind::BoolLit(true), Some(Ty::Int(IntTy::U64)))),
                init: Box::new(expr(ExprKind::IntLit(1), Some(Ty::Bool))),
            },
            Some(bool_array.clone()),
        );
        assert!(validate_interp_expr(&bad_alloc, &HashMap::new()).is_err());

        let bad_outer = expr(
            ExprKind::AllocArray {
                elem: Ty::Bool,
                len: Box::new(int_lit(1)),
                init: Box::new(expr(ExprKind::BoolLit(false), Some(Ty::Bool))),
            },
            Some(Ty::array(Ty::Int(IntTy::U8))),
        );
        assert!(validate_interp_expr(&bad_outer, &HashMap::new()).is_err());

        let mut program = empty_program();
        program.fns.push(function(
            "subject",
            Ty::Unit,
            vec![
                Stmt::Decl {
                    ty: bool_array.clone(),
                    name: "flags".into(),
                    name_span: Span::new(0, 0),
                    init: Some(expr(ExprKind::ArrayLit(vec![]), Some(bool_array.clone()))),
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

        // An ordinary call hands an owner over (ADR 0085), so it is a
        // producer. A *method* result is not: that boundary stays closed,
        // and forging one still meets the producer allow-list.
        let handed_over = expr(
            ExprKind::Call {
                callee: "make".into(),
                callee_span: Span::new(0, 0),
                type_args: vec![],
                args: vec![],
            },
            Some(bool_array.clone()),
        );
        validate_interp_expr(&handed_over, &HashMap::new())
            .expect("a call result is an owner the callee handed over");

        let forged_member = expr(
            ExprKind::MethodCall {
                recv: "holder".into(),
                recv_span: Span::new(0, 0),
                method: "make".into(),
                method_span: Span::new(0, 0),
                args: vec![],
            },
            Some(bool_array),
        );
        assert!(
            validate_interp_expr(&forged_member, &HashMap::new())
                .unwrap_err()
                .starts_with("interp.array_position_unsupported:")
        );
    }

    #[test]
    fn boolean_array_guard_rejects_object_option_and_scalar_operator_laundering() {
        let bool_array = Ty::array(Ty::Bool);
        let locals = HashMap::from([("flags".into(), local(bool_array.clone()))]);
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
                    operand: Box::new(expr(
                        ExprKind::Var("flags".into()),
                        Some(bool_array.clone()),
                    )),
                },
                Some(Ty::Bool),
            ),
            expr(
                ExprKind::OptValue {
                    operand: Box::new(expr(
                        ExprKind::Var("flags".into()),
                        Some(bool_array.clone()),
                    )),
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
                    arg: Box::new(expr(
                        ExprKind::Var("flags".into()),
                        Some(bool_array.clone()),
                    )),
                },
                Some(Ty::Int(IntTy::U64)),
            ),
            expr(
                ExprKind::Narrow {
                    target: IntTy::U8,
                    arg: Box::new(expr(
                        ExprKind::Var("flags".into()),
                        Some(bool_array.clone()),
                    )),
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

        let resource_locals =
            HashMap::from([("authority".into(), local(Ty::Res(ResKind::RawSpan)))]);
        let erased_place = expr(ExprKind::Var("authority".into()), None);
        reject_owned_bool_array_transport(&erased_place, &resource_locals, "sealed operand")
            .expect("an intentionally unannotated resource place is not a Boolean array");
    }

    #[test]
    fn boolean_array_guard_rejects_scalar_statement_sinks() {
        let span = Span::new(0, 0);
        let bool_array = Ty::array(Ty::Bool);
        let int_array = Ty::array(Ty::Int(IntTy::U8));
        let bool_var = || expr(ExprKind::Var("bits".into()), Some(bool_array.clone()));
        let byte = || expr(ExprKind::IntLit(1), Some(Ty::Int(IntTy::U8)));
        let base = HashMap::from([
            ("bits".into(), local(bool_array.clone())),
            ("ints".into(), local(int_array)),
            ("raw".into(), local(Ty::Res(ResKind::RawSpan))),
            ("release".into(), local(Ty::Res(ResKind::SystemDealloc))),
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
            Ty::option(Ty::Int(IntTy::U64)),
            vec![Stmt::Return {
                value: Some(expr(ExprKind::NoneE, Some(Ty::option(Ty::Int(IntTy::U64))))),
                span: Span::new(0, 0),
            }],
        ));
        program.fn_templates.push(function(
            "template",
            Ty::option(Ty::Param(TypeParamId::from_legacy(0))),
            Vec::new(),
        ));

        validate_interp_program(&program)
            .expect("the executable integer domain should remain unchanged");
    }
}
