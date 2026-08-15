//! The Sable compiler library. `check_file` runs the full pipeline:
//! scan → parse → typecheck → vcgen → emit Lean → check → map diagnostics.

pub mod artifacts;
pub mod ast;
pub mod check;
pub mod consts;
pub mod daemon;
pub mod diag;
pub mod interp;
pub mod lean;
pub mod lexer;
pub mod llvm;
pub mod lsp;
pub mod modules;
pub mod mono;
pub mod parser;
pub mod profile;
pub mod scan;
#[cfg(test)]
mod shape_admission;
pub mod span;
pub mod speceval;
pub mod svm;
pub mod vcgen;

use diag::Diagnostic;
use span::LineMap;
use std::path::{Path, PathBuf};

pub struct Failure {
    /// Machine-matchable name (obligation name or error code).
    pub name: String,
    pub rendered: String,
}

pub enum Outcome {
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
    },
    /// Failing obligations; any budget warnings are withheld until the
    /// errors are fixed (they would be noise next to real failures).
    Failed(Vec<Failure>),
}

#[derive(Debug, Clone)]
pub struct VerifiedInfo {
    pub functions: usize,
    pub obligations: usize,
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
}

/// A typed, monomorphized program together with the exact Lean verification
/// that authorizes a production backend to consume it.
///
/// `program` is moved directly out of the [`artifacts::Prepared`] value whose
/// generated Lean document was checked and stamped. It is never reconstructed
/// by reloading the source after verification. The two identities let callers
/// record which content-addressed artifact and immutable proof environment the
/// result came from.
#[derive(Debug)]
pub struct VerifiedProgram {
    program: ast::Program,
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
    /// The exact checked and monomorphized AST authorized by Lean.
    pub fn program(&self) -> &ast::Program {
        &self.program
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
) -> Result<(ast::Program, modules::ModuleSet), Vec<Failure>> {
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
    check::check(&mut program).map_err(|d| vec![render(&d)])?;
    Ok((program, mods))
}

/// Run the front end and the dynamic test interpreter (`sable test`).
/// Never invokes Lean; contracts are checked dynamically (design §9).
pub fn test_file(path: &Path, opts: &Options) -> Result<Vec<interp::TestReport>, Vec<Failure>> {
    let (program, mods) = load_checked(path, opts)?;
    Ok(interp::run_tests(&program, &mods))
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

/// The full pipeline with structured (span-carrying) diagnostics — the
/// entry point the LSP uses. Verification is per-module (ADR 0013
/// slice 2): imported modules are verified once into content-addressed
/// artifacts (`artifacts.rs`); this check proves only what its own
/// generated file declares.
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
    (mods, Ok(verified_info(&prep, Vec::new())))
}

/// Verify a file with Lean and return the exact typed program that was proved.
///
/// Unlike [`check_file_structured`], this function always runs Lean and stamps
/// the successful artifact, even when `opts.emit_lean_only` is set. It also
/// never prints generated Lean. Production backends should use this entry
/// point so they cannot accidentally compile an AST reloaded after proof.
pub fn verify_file_structured(
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

fn verified_info(prep: &artifacts::Prepared, warnings: Vec<Diagnostic>) -> VerifiedInfo {
    let deferred: Vec<String> = prep.program.defers.iter().map(|d| d.name.clone()).collect();
    let assumed: Vec<(String, String)> = prep
        .program
        .assumes
        .iter()
        .map(|a| (a.name.clone(), a.reason.clone()))
        .collect();
    let functions = prep.program.fns.len();
    let obligations = prep.emitted.names.thms.len();
    let unsafe_regions = prep.unsafe_regions;
    let externs = prep.vc.trust.externs.clone();
    let machine_profiles = prep.vc.machine.profiles.clone();
    let machine_intrinsics = prep.vc.machine.intrinsics.clone();

    VerifiedInfo {
        functions,
        obligations,
        unsafe_regions,
        externs,
        machine_profiles,
        machine_intrinsics,
        deferred,
        assumed,
        warnings,
    }
}

fn verify_prepared(
    repo_root: &Path,
    opts: &Options,
    mods: &modules::ModuleSet,
    mut prep: artifacts::Prepared,
) -> Result<VerifiedProgram, Vec<Diagnostic>> {
    // Root documents are immutable and content-addressed. Concurrent checks
    // of the same basename or different source versions cannot overwrite the
    // exact bytes this verification is about to send to Lean.
    let lean_file = match artifacts::write_root_generated(repo_root, opts, &prep) {
        Ok(path) => path,
        Err(message) => return Err(vec![io_diag("io.write", message)]),
    };

    // Warm path: a running `sable daemon` keeps a Lean server alive and
    // skips the per-check cold start. Any daemon problem falls back to
    // the batch invocation, unchanged — including a daemon started
    // before the generated-artifact directory was on its search path
    // (its messages then report unknown modules).
    let daemon_messages = daemon::try_check(
        repo_root,
        &lean_file,
        &prep.proof_environment,
        &prep.emitted.lean_source,
    )
    .filter(|ms| !ms.iter().any(|m| m.data.contains("unknown module")));
    let messages = match daemon_messages {
        Some(m) => m,
        None => match lean::run_lean(
            repo_root,
            &prep.proof_environment,
            &lean_file,
            None,
            &prep.emitted.lean_source,
        ) {
            Ok(m) => m,
            Err(msg) => return Err(vec![io_diag("internal.lean_invocation", msg)]),
        },
    };

    let diags = lean::dedup_by_name(lean::diagnose(&prep.emitted, &prep.vc, &messages, mods));
    if diags.is_empty() {
        // Record the verification so importers reuse it (ADR 0013
        // slice 2): same content, same artifact, proven once.
        if let Err(msg) = artifacts::stamp_verified(repo_root, opts, &prep) {
            return Err(vec![io_diag("io.write", msg)]);
        }
        let mut warnings =
            lean::dedup_by_name(lean::diagnose_warnings(&prep.emitted, &prep.vc, &messages));
        warnings.append(&mut prep.dep_warnings);
        let info = verified_info(&prep, warnings);
        let root_span_end = mods
            .modules
            .first()
            .map_or(0, |module| module.base + module.len.max(1));
        Ok(VerifiedProgram {
            program: prep.program,
            info,
            root_span_end,
            artifact_name: prep.lean_name,
            proof_fingerprint: prep.proof_fingerprint,
        })
    } else {
        Err(diags)
    }
}
