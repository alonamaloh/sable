//! The Sable compiler library. `check_file` runs the full pipeline:
//! scan → parse → typecheck → vcgen → emit Lean → check → map diagnostics.

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
/// entry point the LSP uses.
pub fn check_file_structured(
    path: &Path,
    opts: &Options,
) -> (modules::ModuleSet, Result<VerifiedInfo, Vec<Diagnostic>>) {
    let display_path = path.display().to_string();
    // Loader: the root file plus its `use` DAG, merged with combined-
    // source spans (ADR 0013).
    let (mut program, mods) = match modules::load(path, &opts.module_paths) {
        Ok(ok) => ok,
        Err((d, partial)) => return (partial, Err(vec![d])),
    };
    let _ = display_path;
    let source = mods.combined_source.clone();
    if let Err(d) = consts::apply(&mut program) {
        return (mods, Err(vec![d]));
    }
    if let Err(d) = mono::monomorphize(&mut program) {
        return (mods, Err(vec![d]));
    }
    let checked = match check::check(&mut program) {
        Ok(c) => c,
        Err(d) => return (mods, Err(vec![d])),
    };

    // Verification conditions → Lean.
    let vc = vcgen::generate(&program, &checked.sigs, &source);

    // Escape-hatch validation: every defer/assume/discharge must name a
    // real obligation; one obligation gets at most one treatment; a
    // deferred obligation must be runtime-monitorable (design §9 —
    // the quantifier-free fragment).
    {
        let find = |name: &str| vc.obligations.iter().find(|ob| ob.name == name);
        let mut treated: std::collections::HashMap<&str, &str> = std::collections::HashMap::new();
        let conflict_or_orphan = |name: &str, what: &'static str, span: span::Span| {
            if find(name).is_none() {
                return Some(diag::Diagnostic {
                    name: format!("proof.unknown_{what}"),
                    title: format!("`{what} {name}` names no obligation"),
                    span,
                    label: "no obligation with this name exists".into(),
                    notes: vec![(
                        "note".into(),
                        "obligation names appear in `sable check` failure output".into(),
                    )],
                });
            }
            None
        };
        for d in &program.defers {
            if let Some(diag) = conflict_or_orphan(&d.name, "defer", d.span) {
                return (mods, Err(vec![diag]));
            }
            let goal = &find(&d.name).unwrap().goal;
            if goal.contains('∀') || goal.contains('∃') {
                let diag = diag::Diagnostic {
                    name: "proof.defer_unmonitorable".into(),
                    title: format!("`{}` cannot be deferred", d.name),
                    span: d.span,
                    label: "its goal quantifies over an unbounded range".into(),
                    notes: vec![
                        ("goal".into(), goal.clone()),
                        (
                            "note".into(),
                            "defer compiles an obligation to a runtime check; only the \
                             quantifier-free fragment is supported (bounded-quantifier \
                             checking loops are scheduled)"
                                .into(),
                        ),
                    ],
                };
                return (mods, Err(vec![diag]));
            }
            treated.insert(d.name.as_str(), "defer");
        }
        for a in &program.assumes {
            if let Some(diag) = conflict_or_orphan(&a.name, "assume", a.span) {
                return (mods, Err(vec![diag]));
            }
            if let Some(prev) = treated.insert(a.name.as_str(), "assume") {
                let diag = diag::Diagnostic {
                    name: "proof.conflicting_escape".into(),
                    title: format!("`{}` is both {prev}red and assumed", a.name),
                    span: a.span,
                    label: "one obligation, one treatment".into(),
                    notes: vec![],
                };
                return (mods, Err(vec![diag]));
            }
        }
        for d in &program.discharges {
            if let Some(prev) = treated.get(d.name.as_str()) {
                let diag = diag::Diagnostic {
                    name: "proof.conflicting_escape".into(),
                    title: format!("`{}` is both {prev}d and discharged", d.name),
                    span: d.span,
                    label: "one obligation, one treatment".into(),
                    notes: vec![],
                };
                return (mods, Err(vec![diag]));
            }
        }
    }

    // Every discharge must name a real obligation — a renamed or vanished
    // obligation must never silently orphan its proof (design §6).
    for d in &program.discharges {
        if !vc.obligations.iter().any(|ob| ob.name == d.name) {
            let mut near: Vec<&str> = vc
                .obligations
                .iter()
                .map(|ob| ob.name.as_str())
                .filter(|n| n.split('.').next() == d.name.split('.').next())
                .collect();
            near.truncate(8);
            let d_diag = diag::Diagnostic {
                name: "proof.unknown_discharge".into(),
                title: format!("`discharge {}` names no obligation", d.name),
                span: d.span,
                label: "no obligation with this name exists".into(),
                notes: if near.is_empty() {
                    vec![(
                        "note".into(),
                        "run `sable check` to list obligation names".into(),
                    )]
                } else {
                    vec![("nearby obligations".into(), near.join("\n"))]
                },
            };
            return (mods, Err(vec![d_diag]));
        }
    }

    let skip: std::collections::HashSet<String> = program
        .defers
        .iter()
        .map(|d| d.name.clone())
        .chain(program.assumes.iter().map(|a| a.name.clone()))
        .collect();
    let emitted = lean::emit(&vc, &program.discharges, &skip);

    let deferred: Vec<String> = program.defers.iter().map(|d| d.name.clone()).collect();
    let assumed: Vec<(String, String)> = program
        .assumes
        .iter()
        .map(|a| (a.name.clone(), a.reason.clone()))
        .collect();

    if opts.emit_lean_only {
        print!("{}", emitted.lean_source);
        return (
            mods,
            Ok(VerifiedInfo {
                functions: program.fns.len(),
                obligations: vc.obligations.len(),
                deferred,
                assumed,
                warnings: Vec::new(),
            }),
        );
    }

    let Some(repo_root) =
        lean::find_repo_root(&path.canonicalize().unwrap_or_else(|_| path.to_path_buf()))
            .or_else(|| lean::find_repo_root(&std::env::current_dir().ok()?))
    else {
        return (
            mods,
            Err(vec![io_diag(
                "internal.no_lean_dir",
                "cannot locate the Sable Lean prelude (no ancestor directory \
                 contains lean/lean-toolchain)"
                    .into(),
            )]),
        );
    };

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
    if let Err(err) = std::fs::write(&lean_file, &emitted.lean_source) {
        return (
            mods,
            Err(vec![io_diag(
                "io.write",
                format!("cannot write {}: {err}", lean_file.display()),
            )]),
        );
    }

    // Warm path: a running `sable daemon` keeps a Lean server alive and
    // skips the per-check cold start. Any daemon problem falls back to the
    // batch invocation below, unchanged.
    let messages = match daemon::try_check(&repo_root, &lean_file) {
        Some(m) => m,
        None => match lean::run_lean(&repo_root, &lean_file) {
            Ok(m) => m,
            Err(msg) => return (mods, Err(vec![io_diag("internal.lean_invocation", msg)])),
        },
    };

    let diags = lean::dedup_by_name(lean::diagnose(&emitted, &vc, &messages, &mods));
    if diags.is_empty() {
        let warnings = lean::dedup_by_name(lean::diagnose_warnings(&emitted, &vc, &messages));
        (
            mods,
            Ok(VerifiedInfo {
                functions: program.fns.len(),
                obligations: vc.obligations.len(),
                deferred,
                assumed,
                warnings,
            }),
        )
    } else {
        (mods, Err(diags))
    }
}
