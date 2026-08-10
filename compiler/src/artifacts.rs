//! Separate verification (ADR 0013 slice 2): one generated Lean file
//! per module, compiled to an importable, content-addressed artifact
//! and verified once — importers consume contracts through Lean's own
//! module system instead of re-proving the whole DAG.
//!
//! An artifact is `.sable-out/modules/<stem>_<hash>.{lean,olean,ok}`,
//! where the hash covers the generated content and the prelude. Import
//! lines name dep artifacts by that hash, so a module's artifact name
//! transitively pins everything its verification depended on: a changed
//! dep changes the importer's generated header, which also makes the
//! warm daemon reload imports exactly when needed. Cache validity is
//! just artifact existence — `.ok` is written only after a successful,
//! kernel-checked run; failures leave nothing behind.
//!
//! Each generated file declares only what no imported artifact already
//! declares (name subtraction), so template instances demanded by an
//! importer land in the importer's file while everything a dependency
//! proves is proven exactly once.

use crate::Options;
use crate::diag::Diagnostic;
use crate::lean::{self, Emitted, EmittedNames};
use crate::modules::{self, ModuleSet};
use crate::span::Span;
use crate::vcgen::{self, VcResult};
use crate::{check, consts, mono};
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, OnceLock};

/// A verified (or cache-hit) module artifact, as importers need it.
pub struct ModuleArtifact {
    /// Content-addressed Lean module name (`<stem>_<hash>`).
    pub lean_name: String,
    /// What its generated file declares.
    pub names: EmittedNames,
    /// Path as shown in diagnostics.
    pub display: String,
    /// Canonical source path.
    pub path: PathBuf,
    /// Warnings from a fresh verification (empty on cache hits),
    /// including those bubbled up from its own dependencies.
    pub warnings: Vec<PortableDiag>,
}

/// A diagnostic pinned to (module file, module-local span) so it can be
/// re-rendered in any importer's combined coordinate space.
#[derive(Clone)]
pub struct PortableDiag {
    pub file: PathBuf,
    pub start: usize,
    pub end: usize,
    pub diag: Diagnostic,
}

pub fn to_portable(mods: &ModuleSet, d: &Diagnostic) -> PortableDiag {
    let m = mods.module_of(d.span.start);
    PortableDiag {
        file: m.path.clone(),
        start: d.span.start.saturating_sub(m.base),
        end: d.span.end.saturating_sub(m.base),
        diag: d.clone(),
    }
}

pub fn from_portable(mods: &ModuleSet, pd: &PortableDiag) -> Diagnostic {
    let mut d = pd.diag.clone();
    d.span = match mods.modules.iter().find(|m| m.path == pd.file) {
        Some(m) => Span::new(m.base + pd.start, m.base + pd.end),
        None => Span::new(0, 0),
    };
    d
}

/// A module through the front end, vcgen, and per-module emission, with
/// every imported module's artifact ensured (verified) first.
pub struct Prepared {
    pub program: crate::ast::Program,
    pub vc: VcResult,
    pub emitted: Emitted,
    /// Content-addressed artifact name for this module.
    pub lean_name: String,
    /// Warnings from freshly verified dependencies, in this module's
    /// combined coordinates.
    pub dep_warnings: Vec<Diagnostic>,
}

pub fn prepare(
    path: &Path,
    opts: &Options,
    repo_root: &Path,
) -> (ModuleSet, Result<Prepared, Vec<Diagnostic>>) {
    let (mut program, mods) = match modules::load(path, &opts.module_paths) {
        Ok(ok) => ok,
        Err((d, partial)) => return (partial, Err(vec![d])),
    };
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
    let vc = vcgen::generate(&program, &checked.sigs, &mods.combined_source);

    if let Err(d) = validate_escapes(&program, &vc) {
        return (mods, Err(vec![d]));
    }

    // Dependencies: every module in the closure gets its own verified
    // artifact; a dep failure surfaces here in this load's coordinates.
    let mut dep_arts: Vec<Arc<ModuleArtifact>> = Vec::new();
    let mut dep_warnings: Vec<Diagnostic> = Vec::new();
    for m in &mods.modules[1..] {
        match ensure_artifact(&m.path, opts, repo_root) {
            Ok(a) => {
                dep_warnings.extend(a.warnings.iter().map(|w| from_portable(&mods, w)));
                dep_arts.push(a);
            }
            Err(pds) => {
                let diags = pds.iter().map(|pd| from_portable(&mods, pd)).collect();
                return (mods, Err(diags));
            }
        }
    }

    // One declaration, one owner: a name two imported artifacts both
    // declare would collide at `import` time (the flat-namespace analog
    // of `module.name_collision`, reachable via template instances
    // demanded by two sibling modules).
    let mut owner: HashMap<&str, usize> = HashMap::new();
    let mut exclude = EmittedNames::default();
    for (i, a) in dep_arts.iter().enumerate() {
        for n in a
            .names
            .classes
            .iter()
            .chain(&a.names.ghosts)
            .chain(&a.names.wfs)
            .chain(&a.names.thms)
        {
            if let Some(prev) = owner.insert(n, i) {
                if prev != i {
                    let d = Diagnostic {
                        name: "module.duplicate_decl".into(),
                        title: format!("`{n}` is declared by two imported modules"),
                        span: Span::new(0, 0),
                        label: "conflicting imports".into(),
                        notes: vec![(
                            "note".into(),
                            format!(
                                "both `{}` and `{}` produce `{n}` (typically a generic \
                                 instantiated in both); instantiate it in one shared module",
                                dep_arts[prev].display, a.display
                            ),
                        )],
                    };
                    return (mods, Err(vec![d]));
                }
            }
        }
        exclude.classes.extend(a.names.classes.iter().cloned());
        exclude.ghosts.extend(a.names.ghosts.iter().cloned());
        exclude.wfs.extend(a.names.wfs.iter().cloned());
        exclude.thms.extend(a.names.thms.iter().cloned());
        exclude.obligations.extend(a.names.obligations.iter().cloned());
    }

    // A ghost defined here under a name an import already declares
    // would be silently *replaced* by the import under name
    // subtraction — reject it like any cross-module collision.
    let own_path = &mods.modules[0].path;
    for g in &vc.ghosts {
        if mods.module_of(g.span.start).path == *own_path
            && exclude.ghosts.contains(&lean::ghost_head_name(&g.text))
        {
            let d = Diagnostic {
                name: "module.name_collision".into(),
                title: format!(
                    "ghost `{}` is also declared by an imported module",
                    lean::ghost_head_name(&g.text)
                ),
                span: g.span,
                label: "second declaration here".into(),
                notes: vec![(
                    "note".into(),
                    "imports are a flat namespace; rename one of them".into(),
                )],
            };
            return (mods, Err(vec![d]));
        }
    }

    // Escape hatches live in the module that owns the obligation: an
    // importer must not defer/assume/discharge something a dependency
    // proves in its own artifact.
    let foreign = |name: &str, what: &str, span: Span| -> Option<Diagnostic> {
        let owner_art = dep_arts
            .iter()
            .find(|a| a.names.obligations.contains(name))?;
        if mods.module_of(span.start).path == owner_art.path {
            return None;
        }
        Some(Diagnostic {
            name: "module.foreign_escape".into(),
            title: format!("`{what} {name}` targets an imported module's obligation"),
            span,
            label: "escape hatches live with the obligation".into(),
            notes: vec![(
                "note".into(),
                format!(
                    "`{name}` is proven in `{}`'s own verification; move the \
                     `{what}` there",
                    owner_art.display
                ),
            )],
        })
    };
    for d in &program.defers {
        if let Some(diag) = foreign(&d.name, "defer", d.span) {
            return (mods, Err(vec![diag]));
        }
    }
    for a in &program.assumes {
        if let Some(diag) = foreign(&a.name, "assume", a.span) {
            return (mods, Err(vec![diag]));
        }
    }
    for d in &program.discharges {
        if let Some(diag) = foreign(&d.name, "discharge", d.span) {
            return (mods, Err(vec![diag]));
        }
    }

    let skip: std::collections::HashSet<String> = program
        .defers
        .iter()
        .map(|d| d.name.clone())
        .chain(program.assumes.iter().map(|a| a.name.clone()))
        .collect();
    let imports: Vec<String> = dep_arts.iter().map(|a| a.lean_name.clone()).collect();
    let emitted = lean::emit(&vc, &program.discharges, &skip, &imports, &exclude);
    let lean_name = artifact_name(path, &emitted.lean_source, repo_root);

    (
        mods,
        Ok(Prepared {
            program,
            vc,
            emitted,
            lean_name,
            dep_warnings,
        }),
    )
}

/// Escape-hatch validation: every defer/assume/discharge must name a
/// real obligation; one obligation gets at most one treatment; a
/// deferred obligation must be runtime-monitorable (design §9 —
/// the quantifier-free fragment).
fn validate_escapes(program: &crate::ast::Program, vc: &VcResult) -> Result<(), Diagnostic> {
    let find = |name: &str| vc.obligations.iter().find(|ob| ob.name == name);
    let mut treated: HashMap<&str, &str> = HashMap::new();
    let orphan = |name: &str, what: &'static str, span: Span| -> Option<Diagnostic> {
        if find(name).is_none() {
            return Some(Diagnostic {
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
        if let Some(diag) = orphan(&d.name, "defer", d.span) {
            return Err(diag);
        }
        let goal = &find(&d.name).unwrap().goal;
        if goal.contains('∀') || goal.contains('∃') {
            return Err(Diagnostic {
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
            });
        }
        treated.insert(d.name.as_str(), "defer");
    }
    for a in &program.assumes {
        if let Some(diag) = orphan(&a.name, "assume", a.span) {
            return Err(diag);
        }
        if let Some(prev) = treated.insert(a.name.as_str(), "assume") {
            return Err(Diagnostic {
                name: "proof.conflicting_escape".into(),
                title: format!("`{}` is both {prev}red and assumed", a.name),
                span: a.span,
                label: "one obligation, one treatment".into(),
                notes: vec![],
            });
        }
    }
    for d in &program.discharges {
        if let Some(prev) = treated.get(d.name.as_str()) {
            return Err(Diagnostic {
                name: "proof.conflicting_escape".into(),
                title: format!("`{}` is both {prev}d and discharged", d.name),
                span: d.span,
                label: "one obligation, one treatment".into(),
                notes: vec![],
            });
        }
        // A renamed or vanished obligation must never silently orphan
        // its proof (design §6).
        if find(&d.name).is_none() {
            let mut near: Vec<&str> = vc
                .obligations
                .iter()
                .map(|ob| ob.name.as_str())
                .filter(|n| n.split('.').next() == d.name.split('.').next())
                .collect();
            near.truncate(8);
            return Err(Diagnostic {
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
            });
        }
    }
    Ok(())
}

type ArtifactResult = Result<Arc<ModuleArtifact>, Arc<Vec<PortableDiag>>>;

/// In-process artifact cache: one build per module per process, however
/// many importers race for it (corpus threads share dependencies).
fn cache() -> &'static Mutex<HashMap<PathBuf, Arc<Mutex<Option<ArtifactResult>>>>> {
    static CACHE: OnceLock<Mutex<HashMap<PathBuf, Arc<Mutex<Option<ArtifactResult>>>>>> =
        OnceLock::new();
    CACHE.get_or_init(|| Mutex::new(HashMap::new()))
}

/// Ensure `path`'s artifact exists and is verified, building it (and its
/// own dependencies, recursively) if the content-addressed stamp is
/// absent. Lock order follows the import DAG, so no deadlock.
pub fn ensure_artifact(path: &Path, opts: &Options, repo_root: &Path) -> ArtifactResult {
    let canonical = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    let cell = {
        let mut map = cache().lock().unwrap();
        map.entry(canonical.clone()).or_default().clone()
    };
    let mut slot = cell.lock().unwrap();
    if let Some(r) = &*slot {
        return r.clone();
    }
    let result = build_artifact(&canonical, opts, repo_root);
    *slot = Some(result.clone());
    result
}

fn io_portable(path: &Path, name: &str, message: String) -> Arc<Vec<PortableDiag>> {
    Arc::new(vec![PortableDiag {
        file: path.to_path_buf(),
        start: 0,
        end: 0,
        diag: Diagnostic {
            name: name.into(),
            title: message,
            span: Span::new(0, 0),
            label: String::new(),
            notes: vec![],
        },
    }])
}

fn build_artifact(path: &Path, opts: &Options, repo_root: &Path) -> ArtifactResult {
    let (mods, prep) = prepare(path, opts, repo_root);
    let prep = match prep {
        Ok(p) => p,
        Err(diags) => {
            return Err(Arc::new(
                diags.iter().map(|d| to_portable(&mods, d)).collect(),
            ));
        }
    };
    let display = mods.modules[0].display.clone();
    let dir = lean::modules_dir(repo_root);
    if let Err(err) = std::fs::create_dir_all(&dir) {
        return Err(io_portable(
            path,
            "io.out_dir",
            format!("cannot create {}: {err}", dir.display()),
        ));
    }
    let lean_path = dir.join(format!("{}.lean", prep.lean_name));
    let olean_path = dir.join(format!("{}.olean", prep.lean_name));
    let ok_path = dir.join(format!("{}.ok", prep.lean_name));

    // Content-addressed: existence is validity. `.ok` is only written
    // after a successful kernel-checked run that also produced the
    // importable olean.
    if ok_path.is_file() && olean_path.is_file() {
        return Ok(Arc::new(ModuleArtifact {
            lean_name: prep.lean_name,
            names: prep.emitted.names.clone(),
            display,
            path: path.to_path_buf(),
            warnings: Vec::new(),
        }));
    }

    if let Err(err) = write_atomic(&lean_path, &prep.emitted.lean_source) {
        return Err(io_portable(path, "io.write", err));
    }
    let tmp_olean = dir.join(format!("{}.olean.tmp{}", prep.lean_name, std::process::id()));
    let messages = match lean::run_lean(repo_root, &lean_path, Some(&tmp_olean)) {
        Ok(m) => m,
        Err(msg) => {
            let _ = std::fs::remove_file(&tmp_olean);
            return Err(io_portable(path, "internal.lean_invocation", msg));
        }
    };
    let errors = lean::dedup_by_name(lean::diagnose(&prep.emitted, &prep.vc, &messages, &mods));
    if !errors.is_empty() {
        let _ = std::fs::remove_file(&tmp_olean);
        return Err(Arc::new(
            errors.iter().map(|d| to_portable(&mods, d)).collect(),
        ));
    }
    if let Err(err) = std::fs::rename(&tmp_olean, &olean_path) {
        return Err(io_portable(
            path,
            "io.write",
            format!("cannot move {}: {err}", tmp_olean.display()),
        ));
    }
    if let Err(err) = write_atomic(&ok_path, "ok\n") {
        return Err(io_portable(path, "io.write", err));
    }
    let mut warnings: Vec<PortableDiag> =
        lean::dedup_by_name(lean::diagnose_warnings(&prep.emitted, &prep.vc, &messages))
            .iter()
            .map(|d| to_portable(&mods, d))
            .collect();
    warnings.extend(
        prep.dep_warnings
            .iter()
            .map(|d| to_portable(&mods, d)),
    );
    Ok(Arc::new(ModuleArtifact {
        lean_name: prep.lean_name,
        names: prep.emitted.names.clone(),
        display,
        path: path.to_path_buf(),
        warnings,
    }))
}

/// Record a root check's successful verification as an artifact stamp,
/// so importers reuse it instead of re-proving (the olean is compiled
/// on first import if this check ran through the daemon).
pub fn stamp_verified(repo_root: &Path, prep: &Prepared) -> Result<(), String> {
    let dir = lean::modules_dir(repo_root);
    std::fs::create_dir_all(&dir).map_err(|e| format!("cannot create {}: {e}", dir.display()))?;
    write_atomic(
        &dir.join(format!("{}.lean", prep.lean_name)),
        &prep.emitted.lean_source,
    )?;
    write_atomic(&dir.join(format!("{}.ok", prep.lean_name)), "ok\n")
}

/// Atomic-enough write for concurrent checkers: temp file + rename, so
/// readers never see a torn file.
fn write_atomic(path: &Path, content: &str) -> Result<(), String> {
    let tmp = path.with_extension(format!("tmp{}", std::process::id()));
    std::fs::write(&tmp, content).map_err(|e| format!("cannot write {}: {e}", tmp.display()))?;
    std::fs::rename(&tmp, path).map_err(|e| format!("cannot move {}: {e}", tmp.display()))
}

/// `<stem>_<hash>` — the content-addressed Lean module name. The hash
/// seeds with the prelude (sources, toolchain pin, lakefile), so a
/// prelude change invalidates every artifact; dep artifacts are pinned
/// transitively through the `import` lines inside `content`.
fn artifact_name(path: &Path, content: &str, repo_root: &Path) -> String {
    let stem: String = path
        .file_stem()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| "module".into())
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect();
    let stem = if stem.chars().next().is_some_and(|c| c.is_ascii_digit()) {
        format!("m{stem}")
    } else {
        stem
    };
    let h = fnv64(prelude_hash(repo_root), content.as_bytes());
    format!("{stem}_{h:016x}")
}

fn fnv64(seed: u64, bytes: &[u8]) -> u64 {
    let mut h = if seed == 0 { 0xcbf29ce484222325 } else { seed };
    for &b in bytes {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

/// Hash of everything the prelude contributes to a proof: the Lean
/// sources, the toolchain pin, and the lakefile. Computed once per
/// process.
fn prelude_hash(repo_root: &Path) -> u64 {
    static HASH: OnceLock<u64> = OnceLock::new();
    *HASH.get_or_init(|| {
        let lean_dir = repo_root.join("lean");
        let mut files: Vec<PathBuf> = vec![
            lean_dir.join("lean-toolchain"),
            lean_dir.join("lakefile.toml"),
            lean_dir.join("Sable.lean"),
        ];
        if let Ok(entries) = std::fs::read_dir(lean_dir.join("Sable")) {
            files.extend(entries.filter_map(|e| Some(e.ok()?.path())));
        }
        files.sort();
        let mut h = 0u64;
        for f in files {
            h = fnv64(h, f.to_string_lossy().as_bytes());
            if let Ok(content) = std::fs::read(&f) {
                h = fnv64(h, &content);
            }
        }
        h
    })
}
