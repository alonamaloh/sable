//! The (shape × stage gate) admission table.
//!
//! `docs/type-matrix.md` measures what a *source program* may write where. It
//! cannot measure what a *stage* would swallow, because it probes through the
//! parser: a shape no source program can spell has no probe, so a gate lost
//! for that shape leaves the matrix unchanged.
//!
//! This table closes that gap. Every constructor of `Ty`, plus a nesting and
//! a binding-mode battery, is handed to every payload gate, position gate, and
//! type traversal each consuming stage has — without going through the parser
//! — and the answer is blessed in `docs/shape-admission.md`. Making a shape
//! representable and silently making a stage accept it therefore become the
//! same table diff.
//!
//! The public [`explain_type`] query is a read-only view over these same gate
//! calls. It adds profile grouping for presentation, but no independent
//! accept/refuse policy.
//!
//! A gate answers `yes` or a machine-matchable name. A traversal that has no
//! accept/refuse answer — substitution, visibility collection, the present
//! case of an option — records what it produced instead, so losing one of its
//! recursive arms also moves a cell.
//!
//! A gate that panics is a failure here, not a passing row: "no source
//! program reaches this" is an argument about the parser, and this table
//! deliberately does not go through the parser. The LLVM backend's type
//! lowerings are not gates and so have no column; they are total, and
//! `llvm_lowering_is_total_on_admitted_shapes` checks the stronger property
//! the arrangement wants — that no shape a gate admits ever needs their
//! refusal.
//!
//! Run with `SABLE_BLESS=1` to rewrite the table after an intended change.

#[cfg(test)]
use crate::ast::{BindingMode, IntTy, Mutability, ResKind, TypeParamId};
use crate::ast::{Program, Ty};
use crate::span::Span;
use crate::speceval::SpecVal;
#[cfg(test)]
use std::path::{Path, PathBuf};

/// A shape's constructor, named for the coverage check below.
///
/// The match is exhaustive with no wildcard, so adding a constructor to the
/// grammar fails to compile here — and `CONSTRUCTORS` then fails the coverage
/// assertion until the new shape has a sample.
#[cfg(test)]
fn constructor(ty: &Ty) -> &'static str {
    match ty {
        Ty::Int(_) => "Int",
        Ty::Bool => "Bool",
        Ty::Param(_) => "Param",
        Ty::Class(_) => "Class",
        Ty::Record(_) => "Record",
        Ty::Array(..) => "Array",
        Ty::Slots(..) => "Slots",
        Ty::Option(_) => "Option",
        Ty::OptionRaw(_) => "OptionRaw",
        Ty::Res(_) => "Res",
        Ty::Raw(_) => "Raw",
        Ty::RawRecord(_) => "RawRecord",
        Ty::Borrow(..) => "Borrow",
        Ty::Unit => "Unit",
    }
}

#[cfg(test)]
const CONSTRUCTORS: &[&str] = &[
    "Int",
    "Bool",
    "Param",
    "Class",
    "Record",
    "Array",
    "Slots",
    "Option",
    "OptionRaw",
    "Res",
    "Raw",
    "RawRecord",
    "Borrow",
    "Unit",
];

#[cfg(test)]
fn param() -> TypeParamId {
    TypeParamId::new(0).expect("index 0 is within the parameter ceiling")
}

/// One representative of every constructor, plus two batteries.
///
/// The *nesting* battery is the shapes the grammar can spell whose refusal is
/// the whole point of a gate. The *binding-mode* battery is the same element
/// type under every mutability, because owned-versus-borrowed is a separate
/// answer wherever a stage decides a position: an element type that appears
/// only owned cannot catch the loss of a borrowed-position refusal.
#[cfg(test)]
pub(crate) fn samples() -> Vec<(&'static str, Ty)> {
    vec![
        ("u64", Ty::Int(IntTy::U64)),
        ("u64 (non-canonical parameter)", Ty::Int(IntTy::TParam(0))),
        ("bool", Ty::Bool),
        ("type parameter", Ty::Param(param())),
        ("class", Ty::Class(0)),
        ("&class", Ty::borrow(Mutability::Shared, Ty::Class(0))),
        ("&mut class", Ty::borrow(Mutability::Mut, Ty::Class(0))),
        ("record", Ty::Record(0)),
        ("[u64]", Ty::array(Ty::Int(IntTy::U64))),
        (
            "&[u64]",
            Ty::array_ref(Ty::Int(IntTy::U64), Mutability::Shared),
        ),
        (
            "&mut [u64]",
            Ty::array_ref(Ty::Int(IntTy::U64), Mutability::Mut),
        ),
        ("[u32]", Ty::array(Ty::Int(IntTy::U32))),
        (
            "&[u32]",
            Ty::array_ref(Ty::Int(IntTy::U32), Mutability::Shared),
        ),
        (
            "&mut [u32]",
            Ty::array_ref(Ty::Int(IntTy::U32), Mutability::Mut),
        ),
        ("[bool]", Ty::array(Ty::Bool)),
        ("&[bool]", Ty::array_ref(Ty::Bool, Mutability::Shared)),
        ("&mut [bool]", Ty::array_ref(Ty::Bool, Mutability::Mut)),
        ("[record]", Ty::array(Ty::Record(0))),
        ("[type parameter]", Ty::array(Ty::Param(param()))),
        ("slots<u64>", Ty::slots(Ty::Int(IntTy::U64))),
        ("slots<class>", Ty::slots(Ty::Class(0))),
        (
            "&slots<class>",
            Ty::borrow(Mutability::Shared, Ty::slots(Ty::Class(0))),
        ),
        (
            "&mut slots<class>",
            Ty::borrow(Mutability::Mut, Ty::slots(Ty::Class(0))),
        ),
        ("slots<record>", Ty::slots(Ty::Record(0))),
        (
            "&slots<record>",
            Ty::borrow(Mutability::Shared, Ty::slots(Ty::Record(0))),
        ),
        (
            "&mut slots<record>",
            Ty::borrow(Mutability::Mut, Ty::slots(Ty::Record(0))),
        ),
        ("slots<type parameter>", Ty::slots(Ty::Param(param()))),
        (
            "&slots<type parameter>",
            Ty::borrow(Mutability::Shared, Ty::slots(Ty::Param(param()))),
        ),
        (
            "&mut slots<type parameter>",
            Ty::borrow(Mutability::Mut, Ty::slots(Ty::Param(param()))),
        ),
        (
            "option<slots<u64>>",
            Ty::option(Ty::slots(Ty::Int(IntTy::U64))),
        ),
        (
            "&option<slots<u64>>",
            Ty::borrow(
                Mutability::Shared,
                Ty::option(Ty::slots(Ty::Int(IntTy::U64))),
            ),
        ),
        (
            "&mut option<slots<u64>>",
            Ty::borrow(Mutability::Mut, Ty::option(Ty::slots(Ty::Int(IntTy::U64)))),
        ),
        (
            "&slots<u64>",
            Ty::borrow(Mutability::Shared, Ty::slots(Ty::Int(IntTy::U64))),
        ),
        (
            "&mut slots<u64>",
            Ty::borrow(Mutability::Mut, Ty::slots(Ty::Int(IntTy::U64))),
        ),
        ("option<u64>", Ty::option(Ty::Int(IntTy::U64))),
        ("option<bool>", Ty::option(Ty::Bool)),
        ("option<record>", Ty::option(Ty::Record(0))),
        ("option<type parameter>", Ty::option(Ty::Param(param()))),
        ("option<[bool]>", Ty::affine_array_option(Ty::Bool)),
        (
            "option<[u64]>",
            Ty::affine_array_option(Ty::Int(IntTy::U64)),
        ),
        ("option<[record]>", Ty::affine_array_option(Ty::Record(0))),
        // A borrowed payload owns nothing, so an option over one is not in
        // the owning family however much it looks like `option<[bool]>`.
        (
            "option<&[bool]>",
            Ty::option(Ty::array_ref(Ty::Bool, Mutability::Shared)),
        ),
        (
            "option<&mut [bool]>",
            Ty::option(Ty::array_ref(Ty::Bool, Mutability::Mut)),
        ),
        ("option<raw<record>>", Ty::OptionRaw(0)),
        ("raw<u8>", Ty::Raw(IntTy::U8)),
        ("raw<record>", Ty::RawRecord(0)),
        ("resource", Ty::Res(ResKind::RawSpan)),
        ("resource<record>", Ty::Res(ResKind::PointsToRecord(0))),
        (
            "resource &",
            Ty::borrow(Mutability::Shared, Ty::Res(ResKind::RawSpan)),
        ),
        (
            "resource &mut",
            Ty::borrow(Mutability::Mut, Ty::Res(ResKind::RawSpan)),
        ),
        ("()", Ty::Unit),
        // Every referent a borrow can hold. Binding mode is orthogonal
        // to shape in the representation, so `&T` exists for every `T`; what
        // keeps the language's set of borrowable referents small is a rule,
        // and these rows are where that rule is measured. Each must show a
        // named refusal wherever the owned form was admitted.
        ("&u64", Ty::borrow(Mutability::Shared, Ty::Int(IntTy::U64))),
        ("&mut u64", Ty::borrow(Mutability::Mut, Ty::Int(IntTy::U64))),
        (
            "&u64 (non-canonical parameter)",
            Ty::borrow(Mutability::Shared, Ty::Int(IntTy::TParam(0))),
        ),
        (
            "&mut u64 (non-canonical parameter)",
            Ty::borrow(Mutability::Mut, Ty::Int(IntTy::TParam(0))),
        ),
        ("&bool", Ty::borrow(Mutability::Shared, Ty::Bool)),
        ("&mut bool", Ty::borrow(Mutability::Mut, Ty::Bool)),
        (
            "&type parameter",
            Ty::borrow(Mutability::Shared, Ty::Param(param())),
        ),
        (
            "&mut type parameter",
            Ty::borrow(Mutability::Mut, Ty::Param(param())),
        ),
        ("&record", Ty::borrow(Mutability::Shared, Ty::Record(0))),
        ("&mut record", Ty::borrow(Mutability::Mut, Ty::Record(0))),
        (
            "&option<u64>",
            Ty::borrow(Mutability::Shared, Ty::option(Ty::Int(IntTy::U64))),
        ),
        (
            "&mut option<u64>",
            Ty::borrow(Mutability::Mut, Ty::option(Ty::Int(IntTy::U64))),
        ),
        (
            "&option<bool>",
            Ty::borrow(Mutability::Shared, Ty::option(Ty::Bool)),
        ),
        (
            "&mut option<bool>",
            Ty::borrow(Mutability::Mut, Ty::option(Ty::Bool)),
        ),
        (
            "&option<record>",
            Ty::borrow(Mutability::Shared, Ty::option(Ty::Record(0))),
        ),
        (
            "&mut option<record>",
            Ty::borrow(Mutability::Mut, Ty::option(Ty::Record(0))),
        ),
        (
            "&option<type parameter>",
            Ty::borrow(Mutability::Shared, Ty::option(Ty::Param(param()))),
        ),
        (
            "&mut option<type parameter>",
            Ty::borrow(Mutability::Mut, Ty::option(Ty::Param(param()))),
        ),
        (
            "&option<[bool]>",
            Ty::borrow(Mutability::Shared, Ty::affine_array_option(Ty::Bool)),
        ),
        (
            "&mut option<[bool]>",
            Ty::borrow(Mutability::Mut, Ty::affine_array_option(Ty::Bool)),
        ),
        (
            "&option<[u64]>",
            Ty::borrow(
                Mutability::Shared,
                Ty::affine_array_option(Ty::Int(IntTy::U64)),
            ),
        ),
        (
            "&mut option<[u64]>",
            Ty::borrow(
                Mutability::Mut,
                Ty::affine_array_option(Ty::Int(IntTy::U64)),
            ),
        ),
        (
            "&option<[record]>",
            Ty::borrow(Mutability::Shared, Ty::affine_array_option(Ty::Record(0))),
        ),
        (
            "&mut option<[record]>",
            Ty::borrow(Mutability::Mut, Ty::affine_array_option(Ty::Record(0))),
        ),
        (
            "&option<&[bool]>",
            Ty::borrow(
                Mutability::Shared,
                Ty::option(Ty::array_ref(Ty::Bool, Mutability::Shared)),
            ),
        ),
        (
            "&mut option<&[bool]>",
            Ty::borrow(
                Mutability::Mut,
                Ty::option(Ty::array_ref(Ty::Bool, Mutability::Shared)),
            ),
        ),
        (
            "&option<&mut [bool]>",
            Ty::borrow(
                Mutability::Shared,
                Ty::option(Ty::array_ref(Ty::Bool, Mutability::Mut)),
            ),
        ),
        (
            "&mut option<&mut [bool]>",
            Ty::borrow(
                Mutability::Mut,
                Ty::option(Ty::array_ref(Ty::Bool, Mutability::Mut)),
            ),
        ),
        (
            "&option<raw<record>>",
            Ty::borrow(Mutability::Shared, Ty::OptionRaw(0)),
        ),
        (
            "&mut option<raw<record>>",
            Ty::borrow(Mutability::Mut, Ty::OptionRaw(0)),
        ),
        (
            "&raw<u8>",
            Ty::borrow(Mutability::Shared, Ty::Raw(IntTy::U8)),
        ),
        (
            "&mut raw<u8>",
            Ty::borrow(Mutability::Mut, Ty::Raw(IntTy::U8)),
        ),
        (
            "&raw<record>",
            Ty::borrow(Mutability::Shared, Ty::RawRecord(0)),
        ),
        (
            "&mut raw<record>",
            Ty::borrow(Mutability::Mut, Ty::RawRecord(0)),
        ),
        ("&()", Ty::borrow(Mutability::Shared, Ty::Unit)),
        ("&mut ()", Ty::borrow(Mutability::Mut, Ty::Unit)),
        (
            "&option<option<u64>>",
            Ty::borrow(
                Mutability::Shared,
                Ty::option(Ty::option(Ty::Int(IntTy::U64))),
            ),
        ),
        (
            "&mut option<option<u64>>",
            Ty::borrow(Mutability::Mut, Ty::option(Ty::option(Ty::Int(IntTy::U64)))),
        ),
        (
            "&option<class>",
            Ty::borrow(Mutability::Shared, Ty::option(Ty::Class(0))),
        ),
        (
            "&mut option<class>",
            Ty::borrow(Mutability::Mut, Ty::option(Ty::Class(0))),
        ),
        (
            "&option<[[bool]]>",
            Ty::borrow(
                Mutability::Shared,
                Ty::affine_array_option(Ty::array(Ty::Bool)),
            ),
        ),
        (
            "&mut option<[[bool]]>",
            Ty::borrow(
                Mutability::Mut,
                Ty::affine_array_option(Ty::array(Ty::Bool)),
            ),
        ),
        // The nesting battery: shapes the representation holds and no stage
        // has semantics for. Each must be refused by name.
        ("[[u64]]", Ty::array(Ty::array(Ty::Int(IntTy::U64)))),
        ("[[bool]]", Ty::array(Ty::array(Ty::Bool))),
        ("[class]", Ty::array(Ty::Class(0))),
        ("[option<u64>]", Ty::array(Ty::option(Ty::Int(IntTy::U64)))),
        (
            "[option<[bool]>]",
            Ty::array(Ty::affine_array_option(Ty::Bool)),
        ),
        (
            "option<option<u64>>",
            Ty::option(Ty::option(Ty::Int(IntTy::U64))),
        ),
        ("option<option<bool>>", Ty::option(Ty::option(Ty::Bool))),
        (
            "&option<option<bool>>",
            Ty::borrow(Mutability::Shared, Ty::option(Ty::option(Ty::Bool))),
        ),
        (
            "&mut option<option<bool>>",
            Ty::borrow(Mutability::Mut, Ty::option(Ty::option(Ty::Bool))),
        ),
        (
            "option<option<option<u64>>>",
            Ty::option(Ty::option(Ty::option(Ty::Int(IntTy::U64)))),
        ),
        (
            "&option<option<option<u64>>>",
            Ty::borrow(
                Mutability::Shared,
                Ty::option(Ty::option(Ty::option(Ty::Int(IntTy::U64)))),
            ),
        ),
        (
            "&mut option<option<option<u64>>>",
            Ty::borrow(
                Mutability::Mut,
                Ty::option(Ty::option(Ty::option(Ty::Int(IntTy::U64)))),
            ),
        ),
        ("option<class>", Ty::option(Ty::Class(0))),
        (
            "option<[[bool]]>",
            Ty::affine_array_option(Ty::array(Ty::Bool)),
        ),
        (
            "&[[u64]]",
            Ty::borrow(
                Mutability::Shared,
                Ty::array(Ty::array(Ty::Int(IntTy::U64))),
            ),
        ),
        (
            "&mut [[u64]]",
            Ty::borrow(Mutability::Mut, Ty::array(Ty::array(Ty::Int(IntTy::U64)))),
        ),
        (
            "&[[bool]]",
            Ty::borrow(Mutability::Shared, Ty::array(Ty::array(Ty::Bool))),
        ),
        (
            "&mut [[bool]]",
            Ty::borrow(Mutability::Mut, Ty::array(Ty::array(Ty::Bool))),
        ),
        (
            "&[record]",
            Ty::array_ref(Ty::Record(0), Mutability::Shared),
        ),
        (
            "&mut [record]",
            Ty::array_ref(Ty::Record(0), Mutability::Mut),
        ),
        ("&[class]", Ty::array_ref(Ty::Class(0), Mutability::Shared)),
        ("&mut [class]", Ty::array_ref(Ty::Class(0), Mutability::Mut)),
        (
            "&[type parameter]",
            Ty::array_ref(Ty::Param(param()), Mutability::Shared),
        ),
        (
            "&mut [type parameter]",
            Ty::array_ref(Ty::Param(param()), Mutability::Mut),
        ),
        (
            "&[option<u64>]",
            Ty::array_ref(Ty::option(Ty::Int(IntTy::U64)), Mutability::Shared),
        ),
        (
            "&mut [option<u64>]",
            Ty::array_ref(Ty::option(Ty::Int(IntTy::U64)), Mutability::Mut),
        ),
        (
            "&[option<[bool]>]",
            Ty::array_ref(Ty::affine_array_option(Ty::Bool), Mutability::Shared),
        ),
        (
            "&mut [option<[bool]>]",
            Ty::array_ref(Ty::affine_array_option(Ty::Bool), Mutability::Mut),
        ),
        (
            "resource<record> &",
            Ty::borrow(Mutability::Shared, Ty::Res(ResKind::PointsToRecord(0))),
        ),
        (
            "resource<record> &mut",
            Ty::borrow(Mutability::Mut, Ty::Res(ResKind::PointsToRecord(0))),
        ),
        // A borrow of a borrow: the referent of a `Ty::Borrow` is a full
        // type, so this is representable and nothing but a rule keeps it out.
        (
            "&&[u64]",
            Ty::borrow(
                Mutability::Shared,
                Ty::array_ref(Ty::Int(IntTy::U64), Mutability::Shared),
            ),
        ),
    ]
}

/// How a stage answered.
enum Answer {
    Accepted,
    /// The gate's machine-matchable name.
    Rejected {
        name: String,
        reason: String,
    },
    /// What a traversal produced, for a stage whose failure mode is a lost
    /// recursion rather than a refusal. A cell that moves here is a traversal
    /// that stopped seeing part of the shape.
    Observed(String),
}

impl Answer {
    #[cfg(test)]
    fn render(&self) -> String {
        match self {
            Answer::Accepted => "yes".into(),
            Answer::Rejected { name, .. } => format!("`{name}`"),
            Answer::Observed(what) => what.clone(),
        }
    }
}

/// The machine-matchable name at the head of a stage's internal error string.
fn error_name(message: &str) -> String {
    message
        .split_once(':')
        .map(|(name, _)| name.trim().to_string())
        .unwrap_or_else(|| message.trim().to_string())
}

fn from_message(message: String) -> Answer {
    let name = error_name(&message);
    let reason = message
        .split_once(':')
        .map(|(_, reason)| reason.trim())
        .filter(|reason| !reason.is_empty())
        .unwrap_or("the stage has no semantics for this type here")
        .to_string();
    Answer::Rejected { name, reason }
}

fn diagnostic_reason(diagnostic: &crate::diag::Diagnostic) -> String {
    diagnostic
        .notes
        .first()
        .map(|(_, note)| note.clone())
        .filter(|note| !note.is_empty())
        .unwrap_or_else(|| diagnostic.title.clone())
}

fn from_error(diagnostic: crate::diag::Diagnostic) -> Answer {
    let reason = diagnostic_reason(&diagnostic);
    Answer::Rejected {
        name: diagnostic.name,
        reason,
    }
}

fn from_string(result: Result<(), String>) -> Answer {
    match result {
        Ok(()) => Answer::Accepted,
        Err(message) => from_message(message),
    }
}

fn from_diagnostic(result: Result<(), crate::diag::Diagnostic>) -> Answer {
    match result {
        Ok(()) => Answer::Accepted,
        Err(diagnostic) => from_error(diagnostic),
    }
}

fn from_backend(result: Result<(), Vec<crate::llvm::BackendError>>) -> Answer {
    match result {
        Ok(()) => Answer::Accepted,
        Err(errors) => errors.into_iter().next().map_or_else(
            || Answer::Rejected {
                name: "backend.unnamed".into(),
                reason: "the backend returned an unnamed refusal".into(),
            },
            from_error,
        ),
    }
}

const SPAN: Span = Span { start: 0, end: 0 };

/// The program the nominal shapes are answered against.
///
/// It declares nothing, so the backend answers `class` and `record` as
/// identities it cannot resolve. What that costs is exact and worth stating:
/// the backend's rules *about* a declaration — the fixed-owner class shapes
/// and the concrete-integer record field rule — are not watched here, because
/// reaching them needs a declaration to inspect. Everything this table exists
/// for — payloads, nesting, binding mode, position — is a property of the
/// type, not of the program, and does not depend on it.
fn probe_program() -> Program {
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

/// Every declaration in `probe_program` counts as local to it.
const ROOT_SPAN_END: usize = usize::MAX;

#[derive(Clone, Copy, PartialEq, Eq)]
enum CapabilityProfile {
    Verified,
    Executable,
    FormalMachine,
    Native,
}

impl CapabilityProfile {
    const ALL: [CapabilityProfile; 4] = [
        CapabilityProfile::Verified,
        CapabilityProfile::Executable,
        CapabilityProfile::FormalMachine,
        CapabilityProfile::Native,
    ];

    fn label(self) -> &'static str {
        match self {
            CapabilityProfile::Verified => "verified core (checker + VC generation)",
            CapabilityProfile::Executable => "executable core (interpreter + monitor)",
            CapabilityProfile::FormalMachine => "formal-machine core (SVM)",
            CapabilityProfile::Native => "native core (LLVM)",
        }
    }
}

struct Gate {
    name: &'static str,
    profile: CapabilityProfile,
}

/// The admission table's one gate list, enriched with presentation-only
/// profile ownership for `sable explain-type`.
///
/// The profile tag does not decide support: each answer still comes from the
/// checker/backend function in [`answers`]. Keeping the tag on the table's
/// existing row prevents the CLI from acquiring a second semantic matrix.
const GATES: &[Gate] = &[
    Gate {
        name: "check array payload",
        profile: CapabilityProfile::Verified,
    },
    Gate {
        name: "check option payload",
        profile: CapabilityProfile::Verified,
    },
    Gate {
        name: "check affine payload",
        profile: CapabilityProfile::Verified,
    },
    Gate {
        name: "check aggregate",
        profile: CapabilityProfile::Verified,
    },
    Gate {
        name: "check parameter",
        profile: CapabilityProfile::Verified,
    },
    Gate {
        name: "check local",
        profile: CapabilityProfile::Verified,
    },
    Gate {
        name: "check return",
        profile: CapabilityProfile::Verified,
    },
    Gate {
        name: "check class field",
        profile: CapabilityProfile::Verified,
    },
    Gate {
        name: "check init param",
        profile: CapabilityProfile::Verified,
    },
    Gate {
        name: "check method param",
        profile: CapabilityProfile::Verified,
    },
    Gate {
        name: "check trait param",
        profile: CapabilityProfile::Verified,
    },
    Gate {
        name: "check trait return",
        profile: CapabilityProfile::Verified,
    },
    Gate {
        name: "record field",
        profile: CapabilityProfile::Verified,
    },
    Gate {
        name: "vc type",
        profile: CapabilityProfile::Verified,
    },
    Gate {
        name: "vc array payload",
        profile: CapabilityProfile::Verified,
    },
    Gate {
        name: "vc option payload",
        profile: CapabilityProfile::Verified,
    },
    Gate {
        name: "vc local position",
        profile: CapabilityProfile::Verified,
    },
    Gate {
        name: "vc parameter position",
        profile: CapabilityProfile::Verified,
    },
    Gate {
        name: "vc return position",
        profile: CapabilityProfile::Verified,
    },
    Gate {
        name: "vc class field",
        profile: CapabilityProfile::Verified,
    },
    Gate {
        name: "interp type",
        profile: CapabilityProfile::Executable,
    },
    Gate {
        name: "interp return",
        profile: CapabilityProfile::Executable,
    },
    Gate {
        name: "interp array payload",
        profile: CapabilityProfile::Executable,
    },
    Gate {
        name: "interp option payload",
        profile: CapabilityProfile::Executable,
    },
    Gate {
        name: "interp option value",
        profile: CapabilityProfile::Executable,
    },
    Gate {
        name: "interp class field",
        profile: CapabilityProfile::Executable,
    },
    Gate {
        name: "interp record field",
        profile: CapabilityProfile::Executable,
    },
    Gate {
        name: "svm type",
        profile: CapabilityProfile::FormalMachine,
    },
    Gate {
        name: "svm array payload",
        profile: CapabilityProfile::FormalMachine,
    },
    Gate {
        name: "svm option payload",
        profile: CapabilityProfile::FormalMachine,
    },
    Gate {
        name: "svm parameter",
        profile: CapabilityProfile::FormalMachine,
    },
    Gate {
        name: "svm return",
        profile: CapabilityProfile::FormalMachine,
    },
    Gate {
        name: "llvm runtime type",
        profile: CapabilityProfile::Native,
    },
    Gate {
        name: "llvm local",
        profile: CapabilityProfile::Native,
    },
    Gate {
        name: "llvm parameter",
        profile: CapabilityProfile::Native,
    },
    Gate {
        name: "mono substitution",
        profile: CapabilityProfile::Verified,
    },
    Gate {
        name: "module references",
        profile: CapabilityProfile::Verified,
    },
    Gate {
        name: "monitor default",
        profile: CapabilityProfile::Executable,
    },
];

/// The class and record names the visibility traversal would find, so a
/// nominal reference it stops collecting shows up as a cell losing a name.
const PROBE_CLASS_EXTERNS: &[&str] = &["ProbeClass"];
const PROBE_RECORD_EXTERNS: &[&str] = &["ProbeRecord"];

fn answers(ty: &Ty, context: &str) -> Vec<Answer> {
    let program = probe_program();
    let externs: Vec<String> = PROBE_CLASS_EXTERNS.iter().map(|s| s.to_string()).collect();
    let record_externs: Vec<String> = PROBE_RECORD_EXTERNS.iter().map(|s| s.to_string()).collect();

    let mut references = Vec::new();
    crate::modules::walk_ty(ty, SPAN, &externs, &record_externs, &mut references);
    let references = if references.is_empty() {
        "none".to_string()
    } else {
        references
            .iter()
            .map(|(_, name, _)| format!("`{name}`"))
            .collect::<Vec<_>>()
            .join(", ")
    };

    let mut substituted = ty.clone();
    let substitution = from_diagnostic(crate::mono::subst_ty(&mut substituted, &[], SPAN));

    vec![
        from_diagnostic(crate::check::validate_array_payload(ty, SPAN)),
        match crate::check::option_payload_ty(ty.clone(), SPAN) {
            Ok(_) => Answer::Accepted,
            Err(diagnostic) => from_error(diagnostic),
        },
        from_diagnostic(crate::check::affine_option_payload(
            &Ty::array(ty.clone()),
            SPAN,
        )),
        from_diagnostic(crate::check::validate_aggregate_ty(ty.clone(), SPAN)),
        from_diagnostic(crate::check::parameter_ty(ty, SPAN)),
        from_diagnostic(crate::check::local_ty(ty, SPAN)),
        from_diagnostic(crate::check::return_ty(ty, context, SPAN)),
        from_diagnostic(crate::check::class_field_ty(ty, SPAN)),
        from_diagnostic(crate::check::member_param_ty(ty, SPAN, true)),
        from_diagnostic(crate::check::member_param_ty(ty, SPAN, false)),
        from_diagnostic(crate::check::trait_param_ty(ty, SPAN)),
        from_diagnostic(crate::check::trait_return_ty(ty, context, SPAN)),
        match crate::check::record_field_layout(ty, context, SPAN) {
            Ok(_) => Answer::Accepted,
            Err(diagnostic) => from_error(diagnostic),
        },
        from_string(crate::vcgen::validate_vc_ty(ty.clone(), true, context)),
        from_string(crate::vcgen::validate_vc_payload_ty(
            ty,
            true,
            crate::vcgen::VcAggregateKind::Array,
            context,
        )),
        from_string(crate::vcgen::validate_vc_payload_ty(
            ty,
            true,
            crate::vcgen::VcAggregateKind::Option,
            context,
        )),
        from_string(crate::vcgen::validate_vc_type_position(
            ty.clone(),
            true,
            crate::vcgen::VcTypePosition::Local,
            context,
        )),
        from_string(crate::vcgen::validate_vc_type_position(
            ty.clone(),
            true,
            crate::vcgen::VcTypePosition::Parameter,
            context,
        )),
        from_string(crate::vcgen::validate_vc_type_position(
            ty.clone(),
            true,
            crate::vcgen::VcTypePosition::Return,
            context,
        )),
        from_string(crate::vcgen::validate_vc_type_position(
            ty.clone(),
            true,
            crate::vcgen::VcTypePosition::ClassField,
            context,
        )),
        from_string(crate::interp::validate_interp_ty(ty.clone(), context)),
        from_string(crate::interp::validate_interp_return_ty(
            ty.clone(),
            context,
        )),
        from_string(crate::interp::validate_interp_array_payload(ty, context)),
        from_string(crate::interp::validate_interp_option_payload(ty, context)),
        Answer::Observed(match crate::interp::option_value_ty(ty.clone()) {
            Some(value) => format!("`{}`", value.name()),
            None => "none".into(),
        }),
        from_string(crate::interp::validate_interp_class_field_ty(
            ty.clone(),
            context,
        )),
        from_string(crate::interp::validate_interp_field_ty(ty.clone(), context)),
        from_string(crate::svm::validate_ty_payload(ty.clone(), context)),
        from_string(crate::svm::validate_array_payload(ty, context)),
        from_string(crate::svm::validate_option_payload(ty, context)),
        from_string(crate::svm::validate_parameter_ty(ty, context)),
        from_string(crate::svm::validate_return_ty(ty, context)),
        from_backend(crate::llvm::require_runtime_type(
            &program,
            ROOT_SPAN_END,
            ty.clone(),
            SPAN,
            context,
        )),
        from_backend(crate::llvm::require_local_value(
            &program,
            ROOT_SPAN_END,
            ty.clone(),
            SPAN,
            context,
        )),
        from_backend(crate::llvm::require_parameter_value(
            &program,
            ROOT_SPAN_END,
            ty.clone(),
            SPAN,
            context,
        )),
        substitution,
        Answer::Observed(references),
        match SpecVal::default_of(ty.clone()) {
            Some(_) => Answer::Accepted,
            None => from_message(crate::speceval::no_junk_value(ty).0),
        },
    ]
}

fn one_line(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// Explain one closed type spelling through the parser's position authority
/// and the stage-gate authority that pins the shape-admission matrix.
///
/// The returned text is intentionally the public boundary: callers do not
/// receive checker-only enums, fake nominal indices, or mutable admission
/// structures that could become a second policy API.
pub(crate) fn explain_type(spelling: &str) -> Result<String, crate::diag::Diagnostic> {
    let tokens = crate::lexer::lex(spelling)?;
    let lines = crate::span::LineMap::new(spelling);
    let parsed = crate::parser::parse_type_for_explanation(&tokens, &lines, spelling)?;
    let gate_answers = answers(&parsed.ty, "this type query");
    assert_eq!(
        gate_answers.len(),
        GATES.len(),
        "every explain-type gate needs exactly one answer"
    );

    let mut out = String::new();
    out.push_str(&format!("type: {}\n", spelling.trim()));
    out.push_str(&format!("normalized: {}\n\n", parsed.ty.clone().name()));

    let admitted_positions: Vec<&str> = parsed
        .positions
        .iter()
        .filter(|position| position.diagnostic.is_none())
        .map(|position| position.name)
        .collect();
    out.push_str(&format!(
        "parser type positions — {}/{} lowerings accepted\n",
        admitted_positions.len(),
        parsed.positions.len()
    ));
    out.push_str(
        "  note: parser lowering is not full parse→consts→mono→check language admission\n",
    );
    if !admitted_positions.is_empty() {
        out.push_str(&format!(
            "  parser-accepted: {}\n",
            admitted_positions.join(", ")
        ));
    }
    for position in &parsed.positions {
        let Some(diagnostic) = &position.diagnostic else {
            continue;
        };
        out.push_str(&format!(
            "  {}: {} — {}\n",
            position.name,
            diagnostic.name,
            one_line(&diagnostic_reason(diagnostic))
        ));
    }

    out.push_str("\nevidence-profile stage coverage\n");
    for profile in CapabilityProfile::ALL {
        let entries: Vec<(&Gate, &Answer)> = GATES
            .iter()
            .zip(&gate_answers)
            .filter(|(gate, _)| gate.profile == profile)
            .collect();
        let accepted: Vec<&str> = entries
            .iter()
            .filter_map(|(gate, answer)| matches!(answer, Answer::Accepted).then_some(gate.name))
            .collect();
        let refused = entries
            .iter()
            .filter(|(_, answer)| matches!(answer, Answer::Rejected { .. }))
            .count();
        let admission_questions = accepted.len() + refused;
        out.push_str(&format!(
            "{} — {}/{} gates accepted\n",
            profile.label(),
            accepted.len(),
            admission_questions
        ));
        if !accepted.is_empty() {
            out.push_str(&format!("  accepted: {}\n", accepted.join(", ")));
        }
        for (gate, answer) in &entries {
            if let Answer::Rejected { name, reason } = answer {
                out.push_str(&format!(
                    "  {}: {} — {}\n",
                    gate.name,
                    name,
                    one_line(reason)
                ));
            }
        }
        for (gate, answer) in entries {
            if let Answer::Observed(what) = answer {
                out.push_str(&format!("  {}: observed {}\n", gate.name, one_line(what)));
            }
        }
    }
    Ok(out)
}

#[cfg(test)]
fn table_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("the crate sits inside the repository")
        .join("docs")
        .join("shape-admission.md")
}

#[cfg(test)]
const PROSE: &str = "# The shape × stage-gate admission table\n\n\
     Which shapes each consuming stage admits, probed directly rather than through the \
     parser.\nGenerated by `compiler/src/shape_admission.rs`; rewrite it with \
     `SABLE_BLESS=1 cargo test\n--lib shape_admission`.\n\n\
     `docs/type-matrix.md` answers what a source program may write where. This table \
     answers\nwhat a stage would accept if a shape reached it, which is the question a \
     change to the\ntype representation can silently move. A cell is `yes` when the gate \
     accepted the shape\nand the gate's machine-matchable name when it refused. A stage \
     that is a traversal rather\nthan a gate — substitution, visibility collection, the \
     present case of an option —\nrecords what it produced, so a lost recursive arm \
     moves a cell too.\n\nEvery stage is asked about every shape: the grammar is one \
     recursive type, so there is no\nshape a stage cannot be handed. A cell that moves is \
     either a refusal that was deleted or\nan admission that was widened, and both need a \
     reason.\n\nA gate that answers per position is asked once per position: the member-param \
     gate as\n`check init param` and `check method param`, because an init additionally \
     admits shared\narray borrows, and the trait-signature gate as `check trait param` and \
     `check trait\nreturn`.\n\n";

#[cfg(test)]
fn render() -> String {
    let mut out = String::from(PROSE);

    out.push_str("| shape |");
    for gate in GATES {
        out.push_str(&format!(" {} |", gate.name));
    }
    out.push_str("\n|---|");
    out.push_str(&"---|".repeat(GATES.len()));
    out.push('\n');

    for (name, ty) in samples() {
        let answers = answers(&ty, "shape probe");
        assert_eq!(
            answers.len(),
            GATES.len(),
            "every gate column needs exactly one answer"
        );
        out.push_str(&format!("| `{name}` |"));
        for answer in answers {
            out.push_str(&format!(" {} |", answer.render()));
        }
        out.push('\n');
    }
    out
}

/// The table's rows as (row label, cells), for a difference report that names
/// the cell rather than printing two thousand-character dumps. The header and
/// the alignment rule are dropped: the column set is compared separately.
#[cfg(test)]
fn rows(table: &str) -> Vec<(String, Vec<String>)> {
    table
        .lines()
        .filter(|line| line.starts_with("| `"))
        .map(|line| {
            let mut cells: Vec<String> = line
                .trim_matches('|')
                .split('|')
                .map(|cell| cell.trim().to_string())
                .collect();
            let label = if cells.is_empty() {
                String::new()
            } else {
                cells.remove(0)
            };
            (label, cells)
        })
        .collect()
}

/// The recorded table's gate columns, in order.
#[cfg(test)]
fn columns(table: &str) -> Vec<String> {
    table
        .lines()
        .find(|line| line.starts_with("| shape |"))
        .map(|line| {
            line.trim_matches('|')
                .split('|')
                .skip(1)
                .map(|cell| cell.trim().to_string())
                .collect()
        })
        .unwrap_or_default()
}

/// The first (shape, gate) pair whose recorded answer is not the computed one,
/// or the structural difference that stopped the comparison.
#[cfg(test)]
fn first_difference(recorded: &str, rendered: &str) -> Option<String> {
    let recorded_columns = columns(recorded);
    let expected_columns: Vec<&str> = GATES.iter().map(|gate| gate.name).collect();
    if recorded_columns != expected_columns {
        for (index, gate) in expected_columns.iter().enumerate() {
            match recorded_columns.get(index) {
                Some(recorded_gate) if recorded_gate == gate => {}
                Some(recorded_gate) => {
                    return Some(format!(
                        "column {index} is `{gate}`, but the recorded column there is \
                         `{recorded_gate}`"
                    ));
                }
                None => return Some(format!("gate `{gate}` has no recorded column")),
            }
        }
        return Some(format!(
            "the recorded table has {} extra column(s), starting with `{}`",
            recorded_columns.len() - GATES.len(),
            recorded_columns[GATES.len()]
        ));
    }

    let recorded_rows = rows(recorded);
    let rendered_rows = rows(rendered);

    for (label, cells) in &rendered_rows {
        let Some((_, recorded_cells)) = recorded_rows.iter().find(|(other, _)| other == label)
        else {
            return Some(format!("shape {label} has no row in the recorded table"));
        };
        for (index, cell) in cells.iter().enumerate() {
            let recorded_cell = recorded_cells.get(index);
            let gate = GATES
                .get(index)
                .map(|gate| gate.name)
                .unwrap_or("<unnamed column>");
            match recorded_cell {
                Some(recorded_cell) if recorded_cell == cell => {}
                Some(recorded_cell) => {
                    return Some(format!(
                        "shape {label}, gate `{gate}`: recorded {recorded_cell}, now {cell}"
                    ));
                }
                None => {
                    return Some(format!(
                        "shape {label} has no recorded cell for gate `{gate}` (now {cell})"
                    ));
                }
            }
        }
    }
    for (label, _) in &recorded_rows {
        if !rendered_rows.iter().any(|(other, _)| other == label) {
            return Some(format!("shape {label} is recorded but is no longer probed"));
        }
    }
    if recorded != rendered {
        return Some("every cell agrees; the surrounding prose differs".into());
    }
    None
}

/// Every checker rule guarding a source type position has a column.
///
/// The positions are enumerated by the parser's `TyPos`, so this match is
/// exhaustive by construction: a new position does not compile until it is
/// given its columns here — either the checker gates that watch it, or the
/// explicit statement that the parser's admissibility table and the lowering
/// routines are the whole rule (those positions are probed as contexts in
/// `docs/type-matrix.md` instead, which has its own coverage guard).
#[test]
fn every_checker_position_gate_has_a_column() {
    use crate::parser::TyPos;
    for pos in TyPos::all() {
        let columns: &'static [&'static str] = match pos {
            TyPos::Param => &[
                "check parameter",
                "check init param",
                "check method param",
                "check trait param",
            ],
            // Which referents a borrow may name is decided inside
            // `check::parameter_ty` (ADR 0067).
            TyPos::BorrowParam => &["check parameter"],
            TyPos::Return => &["check return", "check trait return"],
            TyPos::Local => &["check local"],
            TyPos::RecordField => &["record field"],
            TyPos::ClassField => &["check class field"],
            TyPos::ArrayElement => &["check array payload"],
            TyPos::SlotPayload => &[],
            TyPos::OptionPayload => &["check option payload", "check affine payload"],
            // Integer-narrowed positions: the admissibility table plus
            // `lower_int_ty` / `lower_raw_type` / `lower_res_kind` are the
            // whole rule, and no checker gate exists to probe.
            TyPos::ForIndex
            | TyPos::Const
            | TyPos::CastTarget
            | TyPos::TraitImplTarget
            | TyPos::RawElement
            | TyPos::ResourceExtent
            | TyPos::ResourceMapKey => &[],
        };
        for column in columns {
            assert!(
                GATES.iter().any(|gate| gate.name == *column),
                "position `{}` names the shape-admission column `{column}`, which does not \
                 exist: the checker gate watching this position is unprobed",
                pos.short_name()
            );
        }
    }
}

#[test]
fn every_constructor_has_a_sample() {
    let covered: Vec<&'static str> = samples()
        .iter()
        .map(|(_, ty)| constructor(ty))
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .collect();
    for expected in CONSTRUCTORS {
        assert!(
            covered.contains(expected),
            "`Ty::{expected}` has no sample in the shape-admission table"
        );
    }
}

/// Every binding mode a stage answers differently for is a sample.
///
/// Binding mode is decided separately from what a type names, so a shape that
/// appears in one mode only cannot catch the loss of another mode's refusal.
/// Rather than fix a list, this asks the stages: for every shape in the
/// samples that owns, if two binding modes get different answers, each
/// distinguished mode must itself be probed. The audit therefore widens
/// itself the day a stage starts distinguishing a mode it ignores today —
/// and, because `Ty::Borrow` holds every referent, it ranges over the whole
/// grammar rather than over array elements alone.
#[test]
fn every_distinguished_binding_mode_is_probed() {
    let referents: Vec<Ty> = samples()
        .iter()
        .filter(|(_, ty)| ty.binding_mode() == BindingMode::Owned)
        .map(|(_, ty)| ty.clone())
        .collect();
    let probed = |ty: &Ty| samples().iter().any(|(_, other)| other == ty);
    let mut unwatched: Vec<String> = Vec::new();

    for referent in &referents {
        let rendered: Vec<(BindingMode, Vec<String>)> = BindingMode::all()
            .iter()
            .map(|mode| {
                (
                    *mode,
                    answers(&mode.bind(referent.clone()), "shape probe")
                        .iter()
                        .map(|answer| answer.render())
                        .collect(),
                )
            })
            .collect();
        for (mode, answers) in &rendered {
            let distinguished = rendered
                .iter()
                .any(|(_, other)| other != answers)
                .then_some(*mode);
            let Some(mode) = distinguished else {
                continue;
            };
            let shape = mode.bind(referent.clone());
            if !probed(&shape) {
                unwatched.push(shape.name());
            }
        }
    }
    assert!(
        unwatched.is_empty(),
        "a stage answers these shapes differently from their other binding modes, and no sample \
         probes them, so those answers are unwatched: {}",
        unwatched.join(", ")
    );
}

/// The LLVM type lowering is total on every shape the backend admits.
///
/// `llvm::llvm_ty` and `llvm::type_code` are total: a shape they cannot spell
/// is `None`, which the emitter turns into a spanned
/// `internal.backend.type_lowering` diagnostic. That is the floor, not the
/// intent — the intent is that no admitted shape ever reaches it, because the
/// `require_*` gates refuse first under their own names. This test checks
/// that implication, so a widened gate that forgot to teach the lowering
/// fails here rather than shipping a compiler-bug diagnostic to a user.
#[test]
fn llvm_lowering_is_total_on_admitted_shapes() {
    fn lowers(name: &str, what: &str, lowering: Option<String>) {
        match lowering {
            Some(text) => assert!(!text.is_empty(), "`{name}` has an empty {what}"),
            None => panic!(
                "`{name}` is admitted by the backend's gate but has no {what}: the gate was \
                 widened without teaching the lowering, so a program using that shape would \
                 fail with a compiler-bug diagnostic instead of being compiled"
            ),
        }
    }

    let program = probe_program();
    for (name, ty) in samples() {
        let runtime =
            crate::llvm::require_runtime_type(&program, ROOT_SPAN_END, ty.clone(), SPAN, name);
        let local =
            crate::llvm::require_local_value(&program, ROOT_SPAN_END, ty.clone(), SPAN, name);
        if runtime.is_ok() || local.is_ok() {
            lowers(name, "LLVM value type", crate::llvm::llvm_ty(ty.clone()));
        }
        if crate::llvm::require_parameter_value(&program, ROOT_SPAN_END, ty.clone(), SPAN, name)
            .is_ok()
        {
            lowers(name, "symbol type code", crate::llvm::type_code(ty.clone()));
        }
    }
}

/// Every sample reaches both lowerings without a panic, whether or not a gate
/// admits it. Totality is the property; the implication above is the intent.
#[test]
fn llvm_lowering_answers_every_shape() {
    for (_, ty) in samples() {
        let _ = crate::llvm::llvm_ty(ty.clone());
        let _ = crate::llvm::type_code(ty);
    }
}

#[test]
fn shape_admission_is_pinned() {
    let rendered = render();
    let path = table_path();

    if std::env::var("SABLE_BLESS").is_ok() {
        std::fs::write(&path, &rendered).expect("write the shape-admission table");
        return;
    }

    let recorded = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "cannot read {}: {e}\nrun with SABLE_BLESS=1 to create it",
            path.display()
        )
    });

    if let Some(difference) = first_difference(&recorded, &rendered) {
        panic!(
            "{} is stale: {difference}\n\
             A stage changed its answer for a shape. Widening the type representation must not \
             change any cell on its own: a newly reachable shape must arrive as a named refusal \
             unless admitting it was the point of the change. Re-bless with `SABLE_BLESS=1 cargo \
             test --lib shape_admission` once the new answer is the intended one.\n",
            path.display()
        );
    }
}
