//! The Sable compiler library. `check_file` runs the full pipeline:
//! scan → parse → typecheck → vcgen → emit Lean → check → map diagnostics.

mod argument_schedule;
pub mod artifacts;
pub mod ast;
pub mod check;
pub mod consts;
mod control;
pub mod daemon;
pub mod diag;
pub mod doctor;
pub mod interp;
pub mod lean;
pub mod lexer;
pub mod llvm;
pub mod lsp;
pub mod modules;
pub mod mono;
mod ownership;
pub mod parser;
mod place;
pub mod profile;
pub mod scan;
#[doc(hidden)]
pub mod sha256;
mod shape_admission;
pub mod span;
pub mod speceval;
pub mod svm;
mod transition;
pub mod vcgen;

use diag::Diagnostic;
use span::LineMap;
use std::path::{Path, PathBuf};

/// Explain one closed type spelling using the parser-position authority and
/// the stage gates that generate Sable's shape-admission matrix.
pub fn explain_type(spelling: &str) -> Result<String, Diagnostic> {
    shape_admission::explain_type(spelling)
}

pub struct Failure {
    /// Machine-matchable name (obligation name or error code).
    pub name: String,
    pub rendered: String,
}

/// What Sable has established about a generated Lean document and, when Lean
/// was invoked, the transitive proof dependencies behind its acceptance.
///
/// Priority zero deliberately has no "audited" variant yet. Adding one is a
/// semantic event: it requires the content-bound dependency manifest and
/// fail-closed axiom audit described in `docs/PLAN.md`, not merely another
/// successful Lean invocation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProofAssurance {
    /// Sable generated the root Lean document, but did not submit that root
    /// document to Lean. Imported artifacts may still have been prepared.
    GeneratedOnly,
    /// Lean accepted the generated declarations, but Sable has not
    /// authenticated their complete transitive axiom dependency closure.
    LeanAcceptedDependenciesUnaudited,
}

impl ProofAssurance {
    /// Human-readable assurance carried by non-CLI consumers and emitted
    /// artifacts. This deliberately has no axiom-clean/full result yet.
    pub const fn summary(self) -> &'static str {
        match self {
            Self::GeneratedOnly => "Lean generated only; proof not checked",
            Self::LeanAcceptedDependenciesUnaudited => {
                "Lean accepted; proof dependencies unaudited"
            }
        }
    }

    /// Exact terminal status. Escape and extern qualifiers remain visible,
    /// but neither can upgrade an unaudited proof dependency closure.
    pub const fn status_line(self, has_declared_escapes: bool, has_externs: bool) -> &'static str {
        match self {
            Self::GeneratedOnly => "status: Lean generated only; proof not checked",
            Self::LeanAcceptedDependenciesUnaudited => match (has_declared_escapes, has_externs) {
                (false, false) => "status: Lean accepted; proof dependencies unaudited",
                (true, false) => {
                    "status: Lean accepted with declared escapes; proof dependencies unaudited"
                }
                (false, true) => {
                    "status: Lean accepted relative to an audited extern boundary; proof dependencies unaudited"
                }
                (true, true) => {
                    "status: Lean accepted with declared escapes and an audited extern boundary; proof dependencies unaudited"
                }
            },
        }
    }
}

pub enum Outcome {
    /// The requested pipeline completed. `proof_assurance` says whether this
    /// means generation only or Lean acceptance relative to an unaudited
    /// dependency environment; it does not currently mean axiom-clean proof.
    Verified {
        functions: usize,
        obligations: usize,
        unsafe_regions: usize,
        externs: Vec<(String, String, String)>,
        machine_profiles: Vec<(String, String)>,
        machine_intrinsics: Vec<String>,
        /// Obligations compiled to runtime traps (sound escape).
        deferred: Vec<String>,
        /// Obligations taken as audited axioms (unsound escape): (name, reason).
        assumed: Vec<(String, String)>,
        /// Non-fatal, rendered: automation-budget warnings (an obligation
        /// verified but leaned on an expensive `grind`).
        warnings: Vec<String>,
        /// Assurance about the Lean environment behind the accepted result.
        proof_assurance: ProofAssurance,
    },
    /// Failing obligations; any budget warnings are withheld until the
    /// errors are fixed (they would be noise next to real failures).
    Failed(Vec<Failure>),
}

#[derive(Debug, Clone)]
pub struct VerifiedInfo {
    pub functions: usize,
    /// Ordinary source obligations emitted in this module's generated Lean
    /// document. This deliberately excludes compiler-authored certificates.
    pub obligations: usize,
    /// Non-skippable symbolic-transition certificate theorems emitted in this
    /// module's generated Lean document.
    pub transition_certificates: usize,
    /// Non-skippable argument-schedule certificate theorems emitted in this
    /// module's generated Lean document.
    pub argument_schedule_certificates: usize,
    /// Exact byte length of this module's generated Lean document.
    pub generated_lean_bytes: usize,
    /// `unsafe` regions in the checked file. Surfaced in build output
    /// because the count of places a reader must audit is a fact about
    /// the program, and burying it would defeat having a boundary
    /// (ADR 0026).
    pub unsafe_regions: usize,
    /// Audited extern contracts this module (or anything it imports)
    /// trusts: `(audit id, reason, name)`. Non-empty means the build is
    /// verified *relative to* a boundary, and the status must say so
    /// (ADR 0027).
    pub externs: Vec<(String, String, String)>,
    /// Formal machine profiles and their semantic content hashes. These are
    /// dependencies, not audited assumptions.
    pub machine_profiles: Vec<(String, String)>,
    pub machine_intrinsics: Vec<String>,
    pub deferred: Vec<String>,
    pub assumed: Vec<(String, String)>,
    /// Automation-budget warnings (non-fatal), as diagnostics.
    pub warnings: Vec<Diagnostic>,
    /// Assurance about the Lean environment behind the accepted result.
    pub proof_assurance: ProofAssurance,
}

/// A typed, monomorphized program and the checker-sealed semantic plans built
/// for that exact AST.
///
/// Keeping the control table beside the AST prevents dynamic and formal
/// execution paths from silently rebuilding scope/drop identities after the
/// checker has finished. The table is intentionally opaque outside the crate;
/// public callers may inspect the typed program, while compiler consumers use
/// the exact sealed plan through the crate-private accessor.
#[derive(Debug)]
pub struct CheckedProgram {
    program: ast::Program,
    control: control::ControlProgram,
    ownership: ownership::CheckedOwnershipPlan,
}

impl CheckedProgram {
    pub fn program(&self) -> &ast::Program {
        &self.program
    }

    pub(crate) fn control(&self) -> &control::ControlProgram {
        &self.control
    }

    pub(crate) fn ownership(&self) -> &ownership::CheckedOwnershipPlan {
        &self.ownership
    }
}

/// A typed, monomorphized program together with exact Lean acceptance relative
/// to its captured proof environment.
///
/// `program` is moved directly out of the [`artifacts::Prepared`] value whose
/// generated Lean document was checked and stamped. It is never reconstructed
/// by reloading the source after verification. The two identities let callers
/// record which content-addressed artifact and immutable proof environment the
/// result came from. Release and production policy must additionally consult
/// [`VerifiedInfo::proof_assurance`]; Lean acceptance alone is not currently an
/// authenticated axiom-clean result.
#[derive(Debug)]
pub struct VerifiedProgram {
    program: ast::Program,
    /// The checker-sealed control table that accompanied `program` through
    /// VC generation and Lean verification.
    control: control::ControlProgram,
    /// Checker-authored ownership/mutation facts paired with the exact AST.
    ownership: ownership::CheckedOwnershipPlan,
    info: VerifiedInfo,
    /// End of the root module's coordinate range in `program` spans. Keeping
    /// this inside the capability prevents callers from pairing the verified
    /// AST with an unrelated `ModuleSet` to bypass root-entry selection.
    root_span_end: usize,
    /// Content-addressed Lean artifact name stamped by verification.
    artifact_name: String,
    /// Identity of the immutable Lean prelude/profile environment used.
    proof_fingerprint: String,
}

impl VerifiedProgram {
    /// The exact checked and monomorphized AST paired with Lean's acceptance.
    /// See [`Self::info`] for the strictly weaker current assurance boundary.
    pub fn program(&self) -> &ast::Program {
        &self.program
    }

    pub(crate) fn control(&self) -> &control::ControlProgram {
        &self.control
    }

    pub(crate) fn ownership(&self) -> &ownership::CheckedOwnershipPlan {
        &self.ownership
    }

    /// Verification and audit metadata for reporting and backend policy.
    pub fn info(&self) -> &VerifiedInfo {
        &self.info
    }

    pub fn artifact_name(&self) -> &str {
        &self.artifact_name
    }

    pub fn proof_fingerprint(&self) -> &str {
        &self.proof_fingerprint
    }

    pub(crate) fn root_span_end(&self) -> usize {
        self.root_span_end
    }
}

/// Fast, Lean-free pass over source text: scan → lex → parse → typecheck.
/// Returns the first diagnostic, if any (used by the LSP on every edit).
pub fn front_diagnostics(source: &str) -> Vec<Diagnostic> {
    let lines = LineMap::new(source);
    let scanned = scan::scan(source);
    let tokens = match lexer::lex(&scanned.program_text) {
        Ok(t) => t,
        Err(d) => return vec![d],
    };
    let mut program = match parser::parse(&tokens, &scanned.blocks, &lines, &scanned.program_text) {
        Ok(p) => p,
        Err(d) => return vec![d],
    };
    if let Err(d) = consts::apply(&mut program) {
        return vec![d];
    }
    if let Err(d) = mono::monomorphize(&mut program) {
        return vec![d];
    }
    if let Err(d) = check::check(&mut program) {
        return vec![d];
    }
    Vec::new()
}

pub struct Options {
    /// Print the generated Lean file to stdout instead of checking it.
    pub emit_lean_only: bool,
    /// Directories searched for `use` imports, after the importing
    /// file's own directory (ADR 0013).
    pub module_paths: Vec<std::path::PathBuf>,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            emit_lean_only: false,
            module_paths: Vec::new(),
        }
    }
}

/// Lean-free front end over a file and its imports: load, expand
/// consts and generics, and typecheck, returning the typed program —
/// the shared entry for `sable test` and the SVM differential harness.
pub fn load_checked(
    path: &Path,
    opts: &Options,
) -> Result<(CheckedProgram, modules::ModuleSet), Vec<Failure>> {
    let (mut program, mods) = modules::load(path, &opts.module_paths).map_err(|(d, partial)| {
        vec![Failure {
            name: d.name.clone(),
            rendered: partial.render(&d),
        }]
    })?;
    let render = |d: &Diagnostic| Failure {
        name: d.name.clone(),
        rendered: mods.render(d),
    };
    consts::apply(&mut program).map_err(|d| vec![render(&d)])?;
    mono::monomorphize(&mut program).map_err(|d| vec![render(&d)])?;
    let checked = check::check(&mut program).map_err(|d| vec![render(&d)])?;
    Ok((
        CheckedProgram {
            program,
            control: checked.control,
            ownership: checked.ownership,
        },
        mods,
    ))
}

/// Lean-free front end plus VC generation over a file and its imports:
/// the exact obligation list `sable check` would send to Lean, computed
/// in process without invoking it. This is the entry the differential-pair
/// harness (`compiler/tests/pairs.rs`) compares across equivalent-program
/// rewrites; it accepts only a source path, so the pipeline's own mono and
/// checking stages still gate everything VC generation sees.
pub fn load_obligations(
    path: &Path,
    opts: &Options,
) -> Result<(CheckedProgram, modules::ModuleSet, vcgen::VcResult), Vec<Failure>> {
    let (mut program, mods) = modules::load(path, &opts.module_paths).map_err(|(d, partial)| {
        vec![Failure {
            name: d.name.clone(),
            rendered: partial.render(&d),
        }]
    })?;
    let render = |d: &Diagnostic| Failure {
        name: d.name.clone(),
        rendered: mods.render(d),
    };
    consts::apply(&mut program).map_err(|d| vec![render(&d)])?;
    mono::monomorphize(&mut program).map_err(|d| vec![render(&d)])?;
    let checked = check::check(&mut program).map_err(|d| vec![render(&d)])?;
    let Some(repo_root) =
        lean::find_repo_root(&path.canonicalize().unwrap_or_else(|_| path.to_path_buf()))
            .or_else(|| lean::find_repo_root(&std::env::current_dir().ok()?))
    else {
        return Err(vec![Failure {
            name: "internal.no_lean_dir".into(),
            rendered: "cannot locate the Sable Lean prelude (no ancestor directory \
                       contains lean/lean-toolchain)"
                .into(),
        }]);
    };
    let vc = vcgen::generate(&program, &checked, &mods.combined_source, &repo_root).map_err(
        |message| {
            // Fail-closed vcgen refusals carry their name as a `name:` prefix.
            let name = message
                .split(':')
                .next()
                .filter(|head| head.contains('.') && !head.contains(char::is_whitespace))
                .unwrap_or("internal.vcgen")
                .to_string();
            vec![Failure {
                name,
                rendered: message,
            }]
        },
    )?;
    Ok((
        CheckedProgram {
            program,
            control: checked.control,
            ownership: checked.ownership,
        },
        mods,
        vc,
    ))
}

/// Run the front end and the dynamic test interpreter (`sable test`).
/// Never invokes Lean; contracts are checked dynamically (design §9).
pub fn test_file(path: &Path, opts: &Options) -> Result<Vec<interp::TestReport>, Vec<Failure>> {
    let (checked, mods) = load_checked(path, opts)?;
    Ok(interp::run_checked_tests(&checked, &mods))
}

/// Rendered-output wrapper around `check_file_structured`.
pub fn check_file(path: &Path, opts: &Options) -> Outcome {
    let (mods, result) = check_file_structured(path, opts);
    match result {
        Ok(info) => Outcome::Verified {
            functions: info.functions,
            obligations: info.obligations,
            unsafe_regions: info.unsafe_regions,
            externs: info.externs,
            machine_profiles: info.machine_profiles,
            machine_intrinsics: info.machine_intrinsics,
            deferred: info.deferred,
            assumed: info.assumed,
            warnings: info
                .warnings
                .iter()
                .map(|d| mods.render_level("warning", d))
                .collect(),
            proof_assurance: info.proof_assurance,
        },
        Err(diags) => Outcome::Failed(
            diags
                .iter()
                .map(|d| Failure {
                    name: d.name.clone(),
                    rendered: mods.render(d),
                })
                .collect(),
        ),
    }
}

fn io_diag(name: &str, message: String) -> Diagnostic {
    Diagnostic {
        name: name.into(),
        title: message,
        span: span::Span::new(0, 0),
        label: String::new(),
        notes: vec![],
    }
}

/// The generation-or-verification pipeline with structured (span-carrying)
/// diagnostics — the entry point the LSP uses. With `emit_lean_only`, this
/// returns [`ProofAssurance::GeneratedOnly`] and proves nothing. Otherwise,
/// verification is per-module (ADR 0013 slice 2): imported modules are checked
/// once into content-addressed artifacts (`artifacts.rs`), and the root result
/// carries the exact current proof-assurance boundary.
pub fn check_file_structured(
    path: &Path,
    opts: &Options,
) -> (modules::ModuleSet, Result<VerifiedInfo, Vec<Diagnostic>>) {
    if !opts.emit_lean_only {
        let (mods, result) = verify_file_structured(path, opts);
        return (mods, result.map(|verified| verified.info));
    }

    let (mods, prepared) = prepare_file_structured(path, opts);
    let prep = match prepared {
        Ok((_, prep)) => prep,
        Err(diags) => return (mods, Err(diags)),
    };

    print!("{}", prep.emitted.lean_source);
    (
        mods,
        Ok(verified_info(
            &prep,
            Vec::new(),
            ProofAssurance::GeneratedOnly,
        )),
    )
}

/// Verify a file with Lean and return the exact typed program it accepted
/// relative to the captured proof environment.
///
/// Unlike [`check_file_structured`], this function always runs Lean and stamps
/// the successful artifact, even when `opts.emit_lean_only` is set. It also
/// never prints generated Lean. Production backends should use this entry
/// point so they cannot accidentally compile an AST reloaded after Lean
/// acceptance. During priority zero, acceptance always uses the strict batch
/// transport; daemon messages cannot mint this capability. Backend release
/// policy must still inspect `proof_assurance`.
pub fn verify_file_structured(
    path: &Path,
    opts: &Options,
) -> (modules::ModuleSet, Result<VerifiedProgram, Vec<Diagnostic>>) {
    verify_file_structured_inner(path, opts)
}

/// Explicit batch-verification entry point for reproducible instrumentation.
/// This currently has the same transport as [`verify_file_structured`]; the
/// separate API preserves the instrumentation contract if an authenticated
/// warm path returns later.
pub fn verify_file_batch_structured(
    path: &Path,
    opts: &Options,
) -> (modules::ModuleSet, Result<VerifiedProgram, Vec<Diagnostic>>) {
    verify_file_structured_inner(path, opts)
}

fn verify_file_structured_inner(
    path: &Path,
    opts: &Options,
) -> (modules::ModuleSet, Result<VerifiedProgram, Vec<Diagnostic>>) {
    let (mods, prepared) = prepare_file_structured(path, opts);
    let (repo_root, prep) = match prepared {
        Ok(prepared) => prepared,
        Err(diags) => return (mods, Err(diags)),
    };
    let result = verify_prepared(&repo_root, opts, &mods, prep);
    (mods, result)
}

fn prepare_file_structured(
    path: &Path,
    opts: &Options,
) -> (
    modules::ModuleSet,
    Result<(PathBuf, artifacts::Prepared), Vec<Diagnostic>>,
) {
    let Some(repo_root) =
        lean::find_repo_root(&path.canonicalize().unwrap_or_else(|_| path.to_path_buf()))
            .or_else(|| lean::find_repo_root(&std::env::current_dir().ok()?))
    else {
        return (
            modules::ModuleSet::single(path.display().to_string(), String::new()),
            Err(vec![io_diag(
                "internal.no_lean_dir",
                "cannot locate the Sable Lean prelude (no ancestor directory \
                 contains lean/lean-toolchain)"
                    .into(),
            )]),
        );
    };

    let (mods, prepared) = artifacts::prepare(path, opts, &repo_root);
    (mods, prepared.map(|prep| (repo_root, prep)))
}

fn emitted_certificate_category_counts<'a>(
    emitted: &std::collections::HashSet<String>,
    transition_names: impl IntoIterator<Item = &'a str>,
    argument_schedule_names: impl IntoIterator<Item = &'a str>,
) -> (usize, usize) {
    let mut occurrences = std::collections::HashMap::<&str, [usize; 2]>::new();
    for name in transition_names {
        if emitted.contains(name) {
            let count = &mut occurrences.entry(name).or_default()[0];
            *count = count
                .checked_add(1)
                .expect("transition-certificate category count fits usize");
        }
    }
    for name in argument_schedule_names {
        if emitted.contains(name) {
            let count = &mut occurrences.entry(name).or_default()[1];
            *count = count
                .checked_add(1)
                .expect("argument-schedule-certificate category count fits usize");
        }
    }

    let mut transition_certificates = 0usize;
    let mut argument_schedule_certificates = 0usize;
    for name in emitted {
        let [transition, argument_schedule] =
            occurrences.get(name.as_str()).copied().unwrap_or_default();
        assert_eq!(
            transition
                .checked_add(argument_schedule)
                .expect("certificate-category occurrence count fits usize"),
            1,
            "emitted certificate `{name}` must occur exactly once across transition and argument-schedule categories (transition={transition}, argument_schedule={argument_schedule})"
        );
        if transition == 1 {
            transition_certificates += 1;
        } else {
            argument_schedule_certificates += 1;
        }
    }
    assert_eq!(
        transition_certificates + argument_schedule_certificates,
        emitted.len(),
        "emitted certificate categories must be an exact disjoint partition"
    );
    (transition_certificates, argument_schedule_certificates)
}

fn verified_info(
    prep: &artifacts::Prepared,
    warnings: Vec<Diagnostic>,
    proof_assurance: ProofAssurance,
) -> VerifiedInfo {
    let deferred: Vec<String> = prep.program.defers.iter().map(|d| d.name.clone()).collect();
    let assumed: Vec<(String, String)> = prep
        .program
        .assumes
        .iter()
        .map(|a| (a.name.clone(), a.reason.clone()))
        .collect();
    let functions = prep.program.fns.len();
    let obligations = prep.emitted.names.thms.len();
    let (transition_certificates, argument_schedule_certificates) =
        emitted_certificate_category_counts(
            &prep.emitted.names.certificates,
            prep.vc
                .transition_certificates
                .iter()
                .map(|certificate| certificate.thm_name.as_str()),
            prep.vc
                .argument_schedule_certificates
                .iter()
                .map(|certificate| certificate.thm_name.as_str()),
        );
    let generated_lean_bytes = prep.emitted.lean_source.len();
    let unsafe_regions = prep.unsafe_regions;
    let externs = prep.vc.trust.externs.clone();
    let machine_profiles = prep.vc.machine.profiles.clone();
    let machine_intrinsics = prep.vc.machine.intrinsics.clone();

    VerifiedInfo {
        functions,
        obligations,
        transition_certificates,
        argument_schedule_certificates,
        generated_lean_bytes,
        unsafe_regions,
        externs,
        machine_profiles,
        machine_intrinsics,
        deferred,
        assumed,
        warnings,
        proof_assurance,
    }
}

fn verify_prepared(
    repo_root: &Path,
    opts: &Options,
    mods: &modules::ModuleSet,
    mut prep: artifacts::Prepared,
) -> Result<VerifiedProgram, Vec<Diagnostic>> {
    if let Err(failure) = lean::audit_ingress(repo_root, &prep.proof_environment, &prep.emitted) {
        return Err(vec![failure.into_diagnostic()]);
    }
    // Root documents are immutable and content-addressed. Concurrent checks
    // of the same basename or different source versions cannot overwrite the
    // exact bytes this verification is about to send to Lean.
    let lean_file = match artifacts::write_root_generated(repo_root, opts, &prep) {
        Ok(path) => path,
        Err(message) => return Err(vec![io_diag("io.write", message)]),
    };

    // Verification remains on the strict batch transport while the optional
    // warm daemon cannot authenticate its complete server stderr/protocol
    // transcript. The parked daemon currently has no verification caller and
    // cannot mint a stamp or `VerifiedProgram` in this policy version.
    let messages = match lean::run_lean(
        repo_root,
        &prep.proof_environment,
        &lean_file,
        None,
        &prep.emitted.lean_source,
    ) {
        Ok(messages) => messages,
        Err(message) => return Err(vec![io_diag("internal.lean_invocation", message)]),
    };

    let mut diags = lean::diagnose(&prep.emitted, &prep.vc, &messages, mods);
    diags.extend(lean::diagnose_unexpected_warnings(
        &prep.emitted,
        &prep.vc,
        &messages,
    ));
    let diags = lean::dedup_by_name(diags);
    if diags.is_empty() {
        // Record the verification so importers reuse it (ADR 0013
        // slice 2): same content, same artifact, proven once.
        if let Err(msg) = artifacts::stamp_verified(repo_root, opts, &prep) {
            return Err(vec![io_diag("io.write", msg)]);
        }
        let mut warnings =
            lean::dedup_by_name(lean::diagnose_warnings(&prep.emitted, &prep.vc, &messages));
        warnings.append(&mut prep.dep_warnings);
        let info = verified_info(
            &prep,
            warnings,
            // Lean acceptance is useful development evidence, but the current
            // artifact format does not authenticate the complete transitive
            // axiom closure. Keep this fail-safe until Priority Zero lands.
            ProofAssurance::LeanAcceptedDependenciesUnaudited,
        );
        let root_span_end = mods
            .modules
            .first()
            .map_or(0, |module| module.base + module.len.max(1));
        Ok(VerifiedProgram {
            program: prep.program,
            control: prep.control,
            ownership: prep.ownership,
            info,
            root_span_end,
            artifact_name: prep.lean_name,
            proof_fingerprint: prep.proof_fingerprint,
        })
    } else {
        Err(diags)
    }
}

#[cfg(test)]
mod verified_info_tests {
    use super::emitted_certificate_category_counts;
    use std::collections::HashSet;

    fn names(values: &[&str]) -> HashSet<String> {
        values.iter().map(|value| (*value).to_owned()).collect()
    }

    #[test]
    fn emitted_certificate_categories_are_an_exact_partition() {
        let emitted = names(&["transition", "argument"]);
        assert_eq!(
            emitted_certificate_category_counts(
                &emitted,
                ["transition", "imported_transition"],
                ["argument", "imported_argument"],
            ),
            (1, 1),
            "imported category records are intentionally outside the root-emitted partition"
        );

        for (transition, argument) in [
            (vec!["transition", "transition"], vec![]),
            (vec!["transition"], vec!["transition"]),
            (vec![], vec!["argument"]),
        ] {
            assert!(
                std::panic::catch_unwind(|| {
                    emitted_certificate_category_counts(&emitted, transition, argument)
                })
                .is_err(),
                "duplicates, category overlap, and uncategorized emitted names must all fail closed"
            );
        }
    }
}
