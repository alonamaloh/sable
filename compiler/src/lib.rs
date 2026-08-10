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
pub mod lsp;
pub mod modules;
pub mod mono;
pub mod parser;
pub mod scan;
pub mod span;
pub mod speceval;
pub mod svm;
pub mod vcgen;

use diag::Diagnostic;
use span::LineMap;
use std::path::Path;

pub struct Failure {
    /// Machine-matchable name (obligation name or error code).
    pub name: String,
    pub rendered: String,
}

pub enum Outcome {
    Verified {
        functions: usize,
        obligations: usize,
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
    pub deferred: Vec<String>,
    pub assumed: Vec<(String, String)>,
    /// Automation-budget warnings (non-fatal), as diagnostics.
    pub warnings: Vec<Diagnostic>,
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
    let prep = match prepared {
        Ok(p) => p,
        Err(diags) => return (mods, Err(diags)),
    };

    let deferred: Vec<String> = prep.program.defers.iter().map(|d| d.name.clone()).collect();
    let assumed: Vec<(String, String)> = prep
        .program
        .assumes
        .iter()
        .map(|a| (a.name.clone(), a.reason.clone()))
        .collect();
    let functions = prep.program.fns.len();
    let obligations = prep.emitted.names.thms.len();

    if opts.emit_lean_only {
        print!("{}", prep.emitted.lean_source);
        return (
            mods,
            Ok(VerifiedInfo {
                functions,
                obligations,
                deferred,
                assumed,
                warnings: Vec::new(),
            }),
        );
    }

    // The root's file is checked at a *stable* path so the daemon's
    // warm document reuse keeps working across edits (its header still
    // changes whenever a dep artifact does, which is exactly when the
    // worker must reload imports).
    let out_dir = repo_root.join(".sable-out");
    if let Err(err) = std::fs::create_dir_all(&out_dir) {
        return (
            mods,
            Err(vec![io_diag(
                "io.out_dir",
                format!("cannot create {}: {err}", out_dir.display()),
            )]),
        );
    }
    let stem = path
        .file_stem()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| "module".into());
    let lean_file = out_dir.join(format!("{stem}.lean"));
    if let Err(err) = std::fs::write(&lean_file, &prep.emitted.lean_source) {
        return (
            mods,
            Err(vec![io_diag(
                "io.write",
                format!("cannot write {}: {err}", lean_file.display()),
            )]),
        );
    }

    // Warm path: a running `sable daemon` keeps a Lean server alive and
    // skips the per-check cold start. Any daemon problem falls back to
    // the batch invocation, unchanged — including a daemon started
    // before the generated-artifact directory was on its search path
    // (its messages then report unknown modules).
    let daemon_messages = daemon::try_check(&repo_root, &lean_file)
        .filter(|ms| !ms.iter().any(|m| m.data.contains("unknown module")));
    let messages = match daemon_messages {
        Some(m) => m,
        None => match lean::run_lean(&repo_root, &lean_file, None) {
            Ok(m) => m,
            Err(msg) => return (mods, Err(vec![io_diag("internal.lean_invocation", msg)])),
        },
    };

    let diags = lean::dedup_by_name(lean::diagnose(&prep.emitted, &prep.vc, &messages, &mods));
    if diags.is_empty() {
        // Record the verification so importers reuse it (ADR 0013
        // slice 2): same content, same artifact, proven once.
        if let Err(msg) = artifacts::stamp_verified(&repo_root, &prep) {
            return (mods, Err(vec![io_diag("io.write", msg)]));
        }
        let mut warnings =
            lean::dedup_by_name(lean::diagnose_warnings(&prep.emitted, &prep.vc, &messages));
        warnings.extend(prep.dep_warnings);
        (
            mods,
            Ok(VerifiedInfo {
                functions,
                obligations,
                deferred,
                assumed,
                warnings,
            }),
        )
    } else {
        (mods, Err(diags))
    }
}
