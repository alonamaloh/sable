//! The Sable compiler library. `check_file` runs the full pipeline:
//! scan → parse → typecheck → vcgen → emit Lean → check → map diagnostics.

pub mod ast;
pub mod check;
pub mod diag;
pub mod interp;
pub mod lean;
pub mod lexer;
pub mod lsp;
pub mod parser;
pub mod scan;
pub mod span;
pub mod speceval;
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
    },
    Failed(Vec<Failure>),
}

#[derive(Debug, Clone)]
pub struct VerifiedInfo {
    pub functions: usize,
    pub obligations: usize,
    pub deferred: Vec<String>,
    pub assumed: Vec<(String, String)>,
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
    let mut program = match parser::parse(&tokens, &scanned.blocks, &lines, &scanned.program_text)
    {
        Ok(p) => p,
        Err(d) => return vec![d],
    };
    if let Err(d) = check::check(&mut program) {
        return vec![d];
    }
    Vec::new()
}

pub struct Options {
    /// Print the generated Lean file to stdout instead of checking it.
    pub emit_lean_only: bool,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            emit_lean_only: false,
        }
    }
}

/// Run the front end and the dynamic test interpreter (`sable test`).
/// Never invokes Lean; contracts are checked dynamically (design §9).
pub fn test_file(path: &Path) -> Result<Vec<interp::TestReport>, Vec<Failure>> {
    let display_path = path.display().to_string();
    let source = std::fs::read_to_string(path).map_err(|err| {
        vec![Failure {
            name: "io.read".into(),
            rendered: format!("error: cannot read `{display_path}`: {err}\n"),
        }]
    })?;
    let lines = LineMap::new(&source);
    let render = |d: &Diagnostic| Failure {
        name: d.name.clone(),
        rendered: d.render(&display_path, &source, &lines),
    };
    let scanned = scan::scan(&source);
    let tokens = lexer::lex(&scanned.program_text).map_err(|d| vec![render(&d)])?;
    let mut program = parser::parse(&tokens, &scanned.blocks, &lines, &scanned.program_text)
        .map_err(|d| vec![render(&d)])?;
    check::check(&mut program).map_err(|d| vec![render(&d)])?;
    Ok(interp::run_tests(&program, &source, &display_path))
}

/// Rendered-output wrapper around `check_file_structured`.
pub fn check_file(path: &Path, opts: &Options) -> Outcome {
    let display_path = path.display().to_string();
    let (source, result) = check_file_structured(path, opts);
    let lines = LineMap::new(&source);
    match result {
        Ok(info) => Outcome::Verified {
            functions: info.functions,
            obligations: info.obligations,
            deferred: info.deferred,
            assumed: info.assumed,
        },
        Err(diags) => Outcome::Failed(
            diags
                .iter()
                .map(|d| Failure {
                    name: d.name.clone(),
                    rendered: d.render(&display_path, &source, &lines),
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
) -> (String, Result<VerifiedInfo, Vec<Diagnostic>>) {
    let display_path = path.display().to_string();
    let source = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(err) => {
            return (
                String::new(),
                Err(vec![io_diag(
                    "io.read",
                    format!("cannot read `{display_path}`: {err}"),
                )]),
            )
        }
    };
    let lines = LineMap::new(&source);
    let render = |d: &Diagnostic| d.clone();

    // Front end.
    let scanned = scan::scan(&source);
    let tokens = match lexer::lex(&scanned.program_text) {
        Ok(t) => t,
        Err(d) => return (source, Err(vec![render(&d)])),
    };
    let mut program = match parser::parse(&tokens, &scanned.blocks, &lines, &scanned.program_text) {
        Ok(p) => p,
        Err(d) => return (source, Err(vec![render(&d)])),
    };
    let checked = match check::check(&mut program) {
        Ok(c) => c,
        Err(d) => return (source, Err(vec![render(&d)])),
    };

    // Verification conditions → Lean.
    let vc = vcgen::generate(&program, &checked.sigs, &source);

    // Escape-hatch validation: every defer/assume/discharge must name a
    // real obligation; one obligation gets at most one treatment; a
    // deferred obligation must be runtime-monitorable (design §9 — M3
    // supports the quantifier-free fragment).
    {
        let find = |name: &str| vc.obligations.iter().find(|ob| ob.name == name);
        let mut treated: std::collections::HashMap<&str, &str> =
            std::collections::HashMap::new();
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
                return (source, Err(vec![diag]));
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
                            "defer compiles an obligation to a runtime check; M3 supports \
                             the quantifier-free fragment (bounded-quantifier checking \
                             loops are scheduled)"
                                .into(),
                        ),
                    ],
                };
                return (source, Err(vec![diag]));
            }
            treated.insert(d.name.as_str(), "defer");
        }
        for a in &program.assumes {
            if let Some(diag) = conflict_or_orphan(&a.name, "assume", a.span) {
                return (source, Err(vec![diag]));
            }
            if let Some(prev) = treated.insert(a.name.as_str(), "assume") {
                let diag = diag::Diagnostic {
                    name: "proof.conflicting_escape".into(),
                    title: format!("`{}` is both {prev}red and assumed", a.name),
                    span: a.span,
                    label: "one obligation, one treatment".into(),
                    notes: vec![],
                };
                return (source, Err(vec![diag]));
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
                return (source, Err(vec![diag]));
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
                .filter(|n| {
                    n.split('.').next() == d.name.split('.').next()
                })
                .collect();
            near.truncate(8);
            let d_diag = diag::Diagnostic {
                name: "proof.unknown_discharge".into(),
                title: format!("`discharge {}` names no obligation", d.name),
                span: d.span,
                label: "no obligation with this name exists".into(),
                notes: if near.is_empty() {
                    vec![("note".into(), "run `sable check` to list obligation names".into())]
                } else {
                    vec![("nearby obligations".into(), near.join("\n"))]
                },
            };
            return (source, Err(vec![d_diag]));
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
            source,
            Ok(VerifiedInfo {
                functions: program.fns.len(),
                obligations: vc.obligations.len(),
                deferred,
                assumed,
            }),
        );
    }

    let Some(repo_root) = lean::find_repo_root(
        &path.canonicalize().unwrap_or_else(|_| path.to_path_buf()),
    )
    .or_else(|| lean::find_repo_root(&std::env::current_dir().ok()?))
    else {
        return (
            source,
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
            source,
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
            source,
            Err(vec![io_diag(
                "io.write",
                format!("cannot write {}: {err}", lean_file.display()),
            )]),
        );
    }

    let messages = match lean::run_lean(&repo_root, &lean_file) {
        Ok(m) => m,
        Err(msg) => {
            return (
                source,
                Err(vec![io_diag("internal.lean_invocation", msg)]),
            )
        }
    };

    let diags = lean::dedup_by_name(lean::diagnose(&emitted, &vc, &messages));
    if diags.is_empty() {
        (
            source,
            Ok(VerifiedInfo {
                functions: program.fns.len(),
                obligations: vc.obligations.len(),
                deferred,
                assumed,
            }),
        )
    } else {
        (source, Err(diags))
    }
}
