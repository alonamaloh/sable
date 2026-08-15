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
//! A gate answers `yes` or a machine-matchable name. A traversal that has no
//! accept/refuse answer — substitution, visibility collection, the runtime
//! value type of a payload — records what it produced instead, so losing one
//! of its recursive arms also moves a cell.
//!
//! A gate that panics is a failure here, not a passing row: "no source
//! program reaches this" is an argument about the parser, and this table
//! deliberately does not go through the parser. The one stage whose refusal
//! is a panic rather than a diagnostic is the LLVM backend's type lowering,
//! which is why `llvm_lowering_is_total_on_admitted_shapes` checks the
//! implication the panic rests on instead of recording it as an answer.
//!
//! Run with `SABLE_BLESS=1` to rewrite the table after an intended change.

use crate::ast::{AffineOptionTy, IntTy, Mutability, Program, ResKind, Ty, TypeParamId};
use crate::span::Span;
use crate::speceval::SpecVal;
use std::path::{Path, PathBuf};

/// A shape's constructor, named for the coverage check below.
///
/// The match is exhaustive with no wildcard, so adding a constructor to the
/// grammar fails to compile here — and `CONSTRUCTORS` then fails the coverage
/// assertion until the new shape has a sample.
fn constructor(ty: &Ty) -> &'static str {
    match ty {
        Ty::Int(_) => "Int",
        Ty::Bool => "Bool",
        Ty::Param(_) => "Param",
        Ty::Class(_) => "Class",
        Ty::ClassRef(..) => "ClassRef",
        Ty::Record(_) => "Record",
        Ty::Array(..) => "Array",
        Ty::Option(_) => "Option",
        Ty::AffineOption(_) => "AffineOption",
        Ty::OptionRaw(_) => "OptionRaw",
        Ty::Res(_) => "Res",
        Ty::Raw(_) => "Raw",
        Ty::RawRecord(_) => "RawRecord",
        Ty::ResRef(..) => "ResRef",
        Ty::Unit => "Unit",
    }
}

const CONSTRUCTORS: &[&str] = &[
    "Int",
    "Bool",
    "Param",
    "Class",
    "ClassRef",
    "Record",
    "Array",
    "Option",
    "AffineOption",
    "OptionRaw",
    "Res",
    "Raw",
    "RawRecord",
    "ResRef",
    "Unit",
];

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
pub(crate) fn samples() -> Vec<(&'static str, Ty)> {
    vec![
        ("u64", Ty::Int(IntTy::U64)),
        ("u64 (non-canonical parameter)", Ty::Int(IntTy::TParam(0))),
        ("bool", Ty::Bool),
        ("type parameter", Ty::Param(param())),
        ("class", Ty::Class(0)),
        ("&class", Ty::ClassRef(0, Mutability::Shared)),
        ("&mut class", Ty::ClassRef(0, Mutability::Mut)),
        ("record", Ty::Record(0)),
        ("[u64]", Ty::array(Ty::Int(IntTy::U64), Mutability::Owned)),
        ("&[u64]", Ty::array(Ty::Int(IntTy::U64), Mutability::Shared)),
        (
            "&mut [u64]",
            Ty::array(Ty::Int(IntTy::U64), Mutability::Mut),
        ),
        ("[u32]", Ty::array(Ty::Int(IntTy::U32), Mutability::Owned)),
        ("&[u32]", Ty::array(Ty::Int(IntTy::U32), Mutability::Shared)),
        (
            "&mut [u32]",
            Ty::array(Ty::Int(IntTy::U32), Mutability::Mut),
        ),
        ("[bool]", Ty::array(Ty::Bool, Mutability::Owned)),
        ("&[bool]", Ty::array(Ty::Bool, Mutability::Shared)),
        ("&mut [bool]", Ty::array(Ty::Bool, Mutability::Mut)),
        ("[record]", Ty::array(Ty::Record(0), Mutability::Owned)),
        (
            "[type parameter]",
            Ty::array(Ty::Param(param()), Mutability::Owned),
        ),
        ("option<u64>", Ty::option(Ty::Int(IntTy::U64))),
        ("option<bool>", Ty::option(Ty::Bool)),
        ("option<record>", Ty::option(Ty::Record(0))),
        ("option<type parameter>", Ty::option(Ty::Param(param()))),
        (
            "option<[bool]>",
            Ty::AffineOption(AffineOptionTy::array(Ty::Bool)),
        ),
        (
            "option<[u64]>",
            Ty::AffineOption(AffineOptionTy::array(Ty::Int(IntTy::U64))),
        ),
        (
            "option<[record]>",
            Ty::AffineOption(AffineOptionTy::array(Ty::Record(0))),
        ),
        ("option<raw<record>>", Ty::OptionRaw(0)),
        ("raw<u8>", Ty::Raw(IntTy::U8)),
        ("raw<record>", Ty::RawRecord(0)),
        ("resource", Ty::Res(ResKind::RawSpan)),
        ("resource<record>", Ty::Res(ResKind::PointsToRecord(0))),
        (
            "resource &",
            Ty::ResRef(ResKind::RawSpan, Mutability::Shared),
        ),
        (
            "resource &mut",
            Ty::ResRef(ResKind::RawSpan, Mutability::Mut),
        ),
        ("()", Ty::Unit),
        // The nesting battery: shapes the representation holds and no stage
        // has semantics for. Each must be refused by name.
        (
            "[[u64]]",
            Ty::array(
                Ty::array(Ty::Int(IntTy::U64), Mutability::Owned),
                Mutability::Owned,
            ),
        ),
        (
            "[[bool]]",
            Ty::array(Ty::array(Ty::Bool, Mutability::Owned), Mutability::Owned),
        ),
        ("[class]", Ty::array(Ty::Class(0), Mutability::Owned)),
        (
            "[option<u64>]",
            Ty::array(Ty::option(Ty::Int(IntTy::U64)), Mutability::Owned),
        ),
        (
            "[option<[bool]>]",
            Ty::array(Ty::affine_array_option(Ty::Bool), Mutability::Owned),
        ),
        (
            "option<option<u64>>",
            Ty::option(Ty::option(Ty::Int(IntTy::U64))),
        ),
        ("option<class>", Ty::option(Ty::Class(0))),
        (
            "option<[[bool]]>",
            Ty::affine_array_option(Ty::array(Ty::Bool, Mutability::Owned)),
        ),
        (
            "&[[u64]]",
            Ty::array(
                Ty::array(Ty::Int(IntTy::U64), Mutability::Owned),
                Mutability::Shared,
            ),
        ),
    ]
}

/// How a stage answered.
enum Answer {
    Accepted,
    /// The gate's machine-matchable name.
    Rejected(String),
    /// What a traversal produced, for a stage whose failure mode is a lost
    /// recursion rather than a refusal. A cell that moves here is a traversal
    /// that stopped seeing part of the shape.
    Observed(String),
}

impl Answer {
    fn render(&self) -> String {
        match self {
            Answer::Accepted => "yes".into(),
            Answer::Rejected(name) => format!("`{name}`"),
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

fn from_string(result: Result<(), String>) -> Answer {
    match result {
        Ok(()) => Answer::Accepted,
        Err(message) => Answer::Rejected(error_name(&message)),
    }
}

fn from_diagnostic(result: Result<(), crate::diag::Diagnostic>) -> Answer {
    match result {
        Ok(()) => Answer::Accepted,
        Err(diagnostic) => Answer::Rejected(diagnostic.name),
    }
}

fn from_backend(result: Result<(), Vec<crate::llvm::BackendError>>) -> Answer {
    match result {
        Ok(()) => Answer::Accepted,
        Err(errors) => Answer::Rejected(
            errors
                .first()
                .map(|error| error.name.clone())
                .unwrap_or_else(|| "backend.unnamed".into()),
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

const GATES: &[&str] = &[
    "check array payload",
    "check option payload",
    "check affine payload",
    "check aggregate",
    "check parameter",
    "record field",
    "vc type",
    "vc array payload",
    "vc option payload",
    "vc local position",
    "vc parameter position",
    "interp type",
    "interp array payload",
    "interp option payload",
    "interp payload value",
    "interp option value",
    "svm type",
    "svm array payload",
    "svm option payload",
    "svm parameter",
    "llvm runtime type",
    "llvm local",
    "llvm parameter",
    "mono substitution",
    "module references",
    "monitor default",
];

/// The class and record names the visibility traversal would find, so a
/// nominal reference it stops collecting shows up as a cell losing a name.
const PROBE_CLASS_EXTERNS: &[&str] = &["ProbeClass"];
const PROBE_RECORD_EXTERNS: &[&str] = &["ProbeRecord"];

fn answers(ty: &Ty) -> Vec<Answer> {
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
        match crate::check::array_payload_ty(ty.clone(), SPAN) {
            Ok(_) => Answer::Accepted,
            Err(diagnostic) => Answer::Rejected(diagnostic.name),
        },
        match crate::check::option_payload_ty(ty.clone(), SPAN) {
            Ok(_) => Answer::Accepted,
            Err(diagnostic) => Answer::Rejected(diagnostic.name),
        },
        from_diagnostic(crate::check::affine_option_payload(
            AffineOptionTy::array(ty.clone()),
            SPAN,
        )),
        from_diagnostic(crate::check::validate_aggregate_ty(ty.clone(), SPAN)),
        from_diagnostic(crate::check::parameter_ty(ty, SPAN)),
        match crate::check::record_field_layout(ty, "probe", SPAN) {
            Ok(_) => Answer::Accepted,
            Err(diagnostic) => Answer::Rejected(diagnostic.name),
        },
        from_string(crate::vcgen::validate_vc_ty(
            ty.clone(),
            true,
            "shape probe",
        )),
        from_string(crate::vcgen::validate_vc_payload_ty(
            ty,
            true,
            crate::vcgen::VcAggregateKind::Array,
            "shape probe",
        )),
        from_string(crate::vcgen::validate_vc_payload_ty(
            ty,
            true,
            crate::vcgen::VcAggregateKind::Option,
            "shape probe",
        )),
        from_string(crate::vcgen::validate_vc_type_position(
            ty.clone(),
            true,
            crate::vcgen::VcTypePosition::Local,
            "shape probe",
        )),
        from_string(crate::vcgen::validate_vc_type_position(
            ty.clone(),
            true,
            crate::vcgen::VcTypePosition::Parameter,
            "shape probe",
        )),
        from_string(crate::interp::validate_interp_ty(ty.clone(), "shape probe")),
        from_string(crate::interp::validate_interp_array_payload(
            ty.clone(),
            "shape probe",
        )),
        from_string(crate::interp::validate_interp_option_payload(
            ty.clone(),
            "shape probe",
        )),
        Answer::Observed(match crate::interp::value_ty(ty) {
            Some(value) => format!("`{}`", value.name()),
            None => "none".into(),
        }),
        Answer::Observed(match crate::interp::option_value_ty(ty.clone()) {
            Some(value) => format!("`{}`", value.name()),
            None => "none".into(),
        }),
        from_string(crate::svm::validate_ty_payload(ty.clone(), "shape probe")),
        from_string(crate::svm::array_element_ty(ty.clone(), "shape probe").map(|_| ())),
        from_string(crate::svm::ordinary_option_payload_ty(ty.clone()).map(|_| ())),
        from_string(crate::svm::validate_parameter_ty(ty, "shape probe")),
        from_backend(crate::llvm::require_runtime_type(
            &program,
            ROOT_SPAN_END,
            ty.clone(),
            SPAN,
            "shape probe",
        )),
        from_backend(crate::llvm::require_local_value(
            &program,
            ROOT_SPAN_END,
            ty.clone(),
            SPAN,
            "shape probe",
        )),
        from_backend(crate::llvm::require_parameter_value(
            &program,
            ROOT_SPAN_END,
            ty.clone(),
            SPAN,
            "shape probe",
        )),
        substitution,
        Answer::Observed(references),
        match SpecVal::default_of(ty.clone()) {
            Some(_) => Answer::Accepted,
            None => Answer::Rejected(error_name(&crate::speceval::no_junk_value(ty).0)),
        },
    ]
}

fn table_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("the crate sits inside the repository")
        .join("docs")
        .join("shape-admission.md")
}

const PROSE: &str = "# The shape × stage-gate admission table\n\n\
     Which shapes each consuming stage admits, probed directly rather than through the \
     parser.\nGenerated by `compiler/src/shape_admission.rs`; rewrite it with \
     `SABLE_BLESS=1 cargo test\n--lib shape_admission`.\n\n\
     `docs/type-matrix.md` answers what a source program may write where. This table \
     answers\nwhat a stage would accept if a shape reached it, which is the question a \
     change to the\ntype representation can silently move. A cell is `yes` when the gate \
     accepted the shape\nand the gate's machine-matchable name when it refused. A stage \
     that is a traversal rather\nthan a gate — substitution, visibility collection, the \
     runtime value type of a payload —\nrecords what it produced, so a lost recursive arm \
     moves a cell too.\n\nEvery stage is asked about every shape: the grammar is one \
     recursive type, so there is no\nshape a stage cannot be handed. A cell that moves is \
     either a refusal that was deleted or\nan admission that was widened, and both need a \
     reason.\n\n";

fn render() -> String {
    let mut out = String::from(PROSE);

    out.push_str("| shape |");
    for gate in GATES {
        out.push_str(&format!(" {gate} |"));
    }
    out.push_str("\n|---|");
    out.push_str(&"---|".repeat(GATES.len()));
    out.push('\n');

    for (name, ty) in samples() {
        let answers = answers(&ty);
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
fn first_difference(recorded: &str, rendered: &str) -> Option<String> {
    let recorded_columns = columns(recorded);
    if recorded_columns != GATES {
        for (index, gate) in GATES.iter().enumerate() {
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
            let gate = GATES.get(index).copied().unwrap_or("<unnamed column>");
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
/// Owned-versus-borrowed is decided separately from the element type, so an
/// element that appears in one binding mode only cannot catch the loss of
/// another mode's refusal. Rather than fix a list, this asks the stages: for
/// each array element type in the samples, if two binding modes get different
/// answers, both must be probed. The audit therefore widens itself the day a
/// stage starts distinguishing a mode it used to ignore.
#[test]
fn every_distinguished_binding_mode_is_probed() {
    let modes = [Mutability::Owned, Mutability::Shared, Mutability::Mut];
    let elements: Vec<Ty> = samples()
        .iter()
        .filter_map(|(_, ty)| match ty {
            Ty::Array(element, _) => Some(element.as_ref().clone()),
            _ => None,
        })
        .collect();
    let probed = |ty: &Ty| samples().iter().any(|(_, other)| other == ty);

    for element in &elements {
        let rendered: Vec<(Mutability, Vec<String>)> = modes
            .iter()
            .map(|mutability| {
                let array = Ty::array(element.clone(), *mutability);
                (
                    *mutability,
                    answers(&array)
                        .iter()
                        .map(|answer| answer.render())
                        .collect(),
                )
            })
            .collect();
        for (mutability, answers) in &rendered {
            let distinguished = rendered
                .iter()
                .any(|(_, other)| other != answers)
                .then_some(*mutability);
            let Some(mutability) = distinguished else {
                continue;
            };
            assert!(
                probed(&Ty::array(element.clone(), mutability)),
                "a stage answers `{}` differently when it is bound {mutability:?}, and no sample \
                 probes it: that mode's answer is unwatched",
                Ty::array(element.clone(), mutability).name()
            );
        }
    }
}

/// The LLVM type lowering is total on every shape the backend admits.
///
/// `llvm::llvm_ty` and `llvm::type_code` end in `unreachable!`: they are
/// lowerings, not gates, and the backend's refusal is issued earlier by the
/// `require_*` gates, which carry a span. This test checks the implication
/// that arrangement rests on — admitted implies lowerable — so a widened gate
/// that forgot to teach the lowering fails here instead of aborting the
/// process later. A shape the gates refuse is never handed to the lowering,
/// which is why the table records the gates' answers and never a panic.
#[test]
fn llvm_lowering_is_total_on_admitted_shapes() {
    /// Run a lowering on a shape the backend admits and report the shape by
    /// name if it has none. The lowering's own refusal is a panic, so it is
    /// caught here rather than allowed to end the run without saying which
    /// shape the gate and the lowering disagree about.
    fn lowers(name: &str, what: &str, lowering: impl FnOnce() -> String + std::panic::UnwindSafe) {
        match std::panic::catch_unwind(lowering) {
            Ok(text) => assert!(!text.is_empty(), "`{name}` has an empty {what}"),
            Err(_) => panic!(
                "`{name}` is admitted by the backend's gate but has no {what}: the gate was \
                 widened without teaching the lowering, and the disagreement would reach a user \
                 as an aborted compile with no span"
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
            let lowered = ty.clone();
            lowers(name, "LLVM value type", move || {
                crate::llvm::llvm_ty(lowered)
            });
        }
        if crate::llvm::require_parameter_value(&program, ROOT_SPAN_END, ty.clone(), SPAN, name)
            .is_ok()
        {
            let coded = ty.clone();
            lowers(name, "symbol type code", move || {
                crate::llvm::type_code(coded)
            });
        }
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
