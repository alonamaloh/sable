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
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Condvar, Mutex, OnceLock};

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
    /// Exact source bytes whose contracts this artifact exports. Importers
    /// compare this to their already-loaded closure before using `names`.
    pub source: Arc<str>,
    /// Exact proof environment used to verify this dependency.
    proof_fingerprint: String,
    /// Exact transitive module graph used to prove this artifact. A parent
    /// requires equality with the dependency subgraph from its already-loaded
    /// closure, including resolved edges and order.
    inputs: SourceSnapshot,
    /// Warnings from a fresh verification (empty on cache hits),
    /// including those bubbled up from its own dependencies.
    pub warnings: Vec<PortableDiag>,
}

#[derive(Clone)]
struct SourceSnapshot {
    modules: Vec<(PathBuf, Arc<str>)>,
    edges: Vec<(usize, usize)>,
}

impl SourceSnapshot {
    fn exact_eq(&self, other: &SourceSnapshot) -> bool {
        self.edges == other.edges
            && self.modules.len() == other.modules.len()
            && self.modules.iter().zip(&other.modules).all(
                |((left_path, left_source), (right_path, right_source))| {
                    left_path == right_path && left_source == right_source
                },
            )
    }

    fn rooted_at(&self, root_path: &Path) -> Option<SourceSnapshot> {
        let root = self
            .modules
            .iter()
            .position(|(path, _)| path == root_path)?;
        fn visit(snapshot: &SourceSnapshot, module: usize, ordered: &mut Vec<usize>) {
            if ordered.contains(&module) {
                return;
            }
            ordered.push(module);
            for &(_, dependency) in snapshot
                .edges
                .iter()
                .filter(|(importer, _)| *importer == module)
            {
                visit(snapshot, dependency, ordered);
            }
        }
        let mut ordered = Vec::new();
        visit(self, root, &mut ordered);
        let remap: HashMap<usize, usize> = ordered
            .iter()
            .enumerate()
            .map(|(new, old)| (*old, new))
            .collect();
        let mut edges = Vec::new();
        for importer in &ordered {
            for &(_, dependency) in self.edges.iter().filter(|(from, _)| from == importer) {
                if let (Some(&from), Some(&to)) = (remap.get(importer), remap.get(&dependency)) {
                    edges.push((from, to));
                }
            }
        }
        Some(SourceSnapshot {
            modules: ordered
                .iter()
                .map(|&index| self.modules[index].clone())
                .collect(),
            edges,
        })
    }
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
    /// Exact proof environment used to derive `lean_name` and emit this
    /// artifact. Verification and stamping must compare against this value;
    /// recomputing a request fingerprint would hide an intervening edit.
    pub proof_fingerprint: String,
    /// Exact captured bytes behind `proof_fingerprint`. Profile generation,
    /// dependency verification, batch Lean, and the daemon all use this same
    /// immutable handle rather than re-reading the mutable checkout.
    pub(crate) proof_environment: lean::ProofEnvironment,
    /// Exact Sable source/module-resolution snapshot loaded for this VC. It is
    /// rechecked after dependency ensuring, before Lean, and before stamping,
    /// so a root cannot combine contracts from closure A with artifacts from
    /// concurrently edited closure B.
    input_snapshot: SourceSnapshot,
    root_path: PathBuf,
    /// Warnings from freshly verified dependencies, in this module's
    /// combined coordinates.
    pub dep_warnings: Vec<Diagnostic>,
    /// `unsafe` regions the checker counted (ADR 0026).
    pub unsafe_regions: usize,
}

pub fn prepare(
    path: &Path,
    opts: &Options,
    repo_root: &Path,
) -> (ModuleSet, Result<Prepared, Vec<Diagnostic>>) {
    // Capture this before any profile or dependency work. The resulting bytes,
    // not a later same-valued hash of the checkout, are the proof environment.
    let proof_environment = lean::ProofEnvironment::capture(repo_root);
    let proof_environment = match proof_environment {
        Ok(environment) => environment,
        Err(message) => {
            let mods = modules::load(path, &opts.module_paths)
                .map(|(_, modules)| modules)
                .unwrap_or_else(|(_, partial)| partial);
            return (mods, Err(vec![proof_fingerprint_diag(message)]));
        }
    };
    prepare_with_environment(path, opts, repo_root, &proof_environment)
}

fn prepare_with_environment(
    path: &Path,
    opts: &Options,
    repo_root: &Path,
    proof_environment: &lean::ProofEnvironment,
) -> (ModuleSet, Result<Prepared, Vec<Diagnostic>>) {
    let (mut program, mods) = match modules::load(path, &opts.module_paths) {
        Ok(ok) => ok,
        Err((d, partial)) => return (partial, Err(vec![d])),
    };
    let snapshot_repo_root = match proof_environment.materialize_source(repo_root) {
        Ok(root) => root,
        Err(message) => return (mods, Err(vec![proof_fingerprint_diag(message)])),
    };
    let proof_fingerprint = proof_environment.id().to_string();
    let input_snapshot = module_snapshot(&mods);
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
    let vc = match vcgen::generate(
        &program,
        &checked.sigs,
        &mods.combined_source,
        &snapshot_repo_root,
    ) {
        Ok(vc) => vc,
        Err(message) => return (mods, Err(vec![proof_fingerprint_diag(message)])),
    };

    if let Err(d) = validate_escapes(&program, &vc) {
        return (mods, Err(vec![d]));
    }

    // Dependencies: every module in the closure gets its own verified
    // artifact; a dep failure surfaces here in this load's coordinates.
    let mut dep_arts: Vec<Arc<ModuleArtifact>> = Vec::new();
    let mut dep_warnings: Vec<Diagnostic> = Vec::new();
    for module_index in 1..mods.modules.len() {
        let module_path = mods.modules[module_index].path.clone();
        let module_display = mods.modules[module_index].display.clone();
        let module_source = mods.modules[module_index].source.clone();
        let Some(expected_dependency) = input_snapshot.rooted_at(&module_path) else {
            return (
                mods,
                Err(vec![proof_fingerprint_diag(format!(
                    "module `{}` is missing from its loaded import graph",
                    module_display
                ))]),
            );
        };
        match ensure_artifact_snapshot(
            &module_path,
            opts,
            repo_root,
            Some(&expected_dependency),
            proof_environment,
        ) {
            Ok(a) => {
                if a.path != module_path
                    || a.source.as_ref() != module_source
                    || !a.inputs.exact_eq(&expected_dependency)
                    || a.proof_fingerprint.as_str() != proof_fingerprint
                {
                    return (
                        mods,
                        Err(vec![proof_fingerprint_diag(format!(
                            "module `{}` changed while its artifact was being prepared; retry the check",
                            module_display
                        ))]),
                    );
                }
                dep_warnings.extend(a.warnings.iter().map(|w| from_portable(&mods, w)));
                dep_arts.push(a);
            }
            Err(pds) => {
                let diags = pds.iter().map(|pd| from_portable(&mods, pd)).collect();
                return (mods, Err(diags));
            }
        }
    }
    if let Err(message) = require_module_snapshot(path, opts, &input_snapshot) {
        return (mods, Err(vec![proof_fingerprint_diag(message)]));
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
        exclude
            .obligations
            .extend(a.names.obligations.iter().cloned());
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
    let lean_name = artifact_name(path, &emitted.lean_source, &proof_fingerprint);
    let root_path = mods.modules[0].path.clone();

    (
        mods,
        Ok(Prepared {
            program,
            vc,
            emitted,
            lean_name,
            proof_fingerprint,
            proof_environment: proof_environment.clone(),
            input_snapshot,
            root_path,
            dep_warnings,
            unsafe_regions: checked.unsafe_regions,
        }),
    )
}

fn require_prepared_inputs(
    path: &Path,
    opts: &Options,
    prep: &Prepared,
    phase: &str,
) -> Result<(), String> {
    require_module_snapshot(path, opts, &prep.input_snapshot)
        .map_err(|_| format!("the Sable module closure changed {phase}; retry the check"))
}

fn module_snapshot(modules: &ModuleSet) -> SourceSnapshot {
    let raw = SourceSnapshot {
        modules: modules
            .modules
            .iter()
            .map(|module| (module.path.clone(), Arc::from(module.source.as_str())))
            .collect(),
        edges: modules.import_edges.clone(),
    };
    let root = raw.modules.first().map(|(path, _)| path.clone());
    root.and_then(|path| raw.rooted_at(&path)).unwrap_or(raw)
}

fn require_module_snapshot(
    path: &Path,
    opts: &Options,
    expected: &SourceSnapshot,
) -> Result<(), String> {
    let (_, current) = modules::load(path, &opts.module_paths)
        .map_err(|(diagnostic, _)| format!("{}: {}", diagnostic.name, diagnostic.title))?;
    if module_snapshot(&current).exact_eq(expected) {
        Ok(())
    } else {
        Err("the Sable module closure changed while preparing artifacts; retry the check".into())
    }
}

fn proof_fingerprint_diag(message: String) -> Diagnostic {
    Diagnostic {
        name: "internal.proof_fingerprint".into(),
        title: message,
        span: Span::new(0, 0),
        label: "cannot identify a stable current proof environment".into(),
        notes: vec![],
    }
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

#[derive(Clone, Eq, Hash, PartialEq)]
struct ArtifactBuildKey {
    path: PathBuf,
    inputs: u64,
}

struct ArtifactFlight {
    result: Mutex<Option<ArtifactResult>>,
    ready: Condvar,
}

struct ArtifactLeader {
    key: ArtifactBuildKey,
    flight: Arc<ArtifactFlight>,
    path: PathBuf,
    published: bool,
}

impl ArtifactLeader {
    fn publish(mut self, result: ArtifactResult) -> ArtifactResult {
        complete_flight(&self.key, &self.flight, result.clone());
        self.published = true;
        result
    }
}

impl Drop for ArtifactLeader {
    fn drop(&mut self) {
        if self.published {
            return;
        }
        // A compiler panic must not strand every importer waiting forever.
        // Preserve the leader's unwind, but wake followers with a portable
        // internal diagnostic and remove the failed flight for future retries.
        complete_flight(
            &self.key,
            &self.flight,
            Err(io_portable(
                &self.path,
                "internal.artifact_build_panicked",
                "the concurrent artifact build panicked; retry the check".into(),
            )),
        );
    }
}

fn complete_flight(key: &ArtifactBuildKey, flight: &Arc<ArtifactFlight>, result: ArtifactResult) {
    let mut map = cache().lock().unwrap_or_else(|poison| poison.into_inner());
    *flight
        .result
        .lock()
        .unwrap_or_else(|poison| poison.into_inner()) = Some(result);
    if map.get(key).is_some_and(|entry| Arc::ptr_eq(entry, flight)) {
        map.remove(key);
    }
    drop(map);
    flight.ready.notify_all();
}

/// In-process artifact coordinator: callers racing on the same module and
/// the same current inputs share one build. Completed results are removed
/// immediately. Long-lived processes must re-snapshot source, options, and
/// the Lean proof environment on their next request rather than returning a
/// result retained under a path that may since have changed.
fn cache() -> &'static Mutex<HashMap<ArtifactBuildKey, Arc<ArtifactFlight>>> {
    static CACHE: OnceLock<Mutex<HashMap<ArtifactBuildKey, Arc<ArtifactFlight>>>> = OnceLock::new();
    CACHE.get_or_init(|| Mutex::new(HashMap::new()))
}

/// Ensure `path`'s artifact exists and is verified, building it (and its
/// own dependencies, recursively) if the content-addressed stamp is
/// absent. Lock order follows the import DAG, so no deadlock.
pub fn ensure_artifact(path: &Path, opts: &Options, repo_root: &Path) -> ArtifactResult {
    let environment = match lean::ProofEnvironment::capture(repo_root) {
        Ok(environment) => environment,
        Err(message) => {
            return Err(io_portable(
                path,
                "internal.proof_fingerprint",
                message,
            ));
        }
    };
    ensure_artifact_snapshot(path, opts, repo_root, None, &environment)
}

fn ensure_artifact_snapshot(
    path: &Path,
    opts: &Options,
    repo_root: &Path,
    expected: Option<&SourceSnapshot>,
    proof_environment: &lean::ProofEnvironment,
) -> ArtifactResult {
    let canonical = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    if let Err(message) = proof_environment.materialize_source(repo_root) {
        return Err(io_portable(
            &canonical,
            "internal.proof_fingerprint",
            message,
        ));
    }
    if let Some(expected) = expected {
        match load_snapshot(&canonical, opts) {
            Ok(current) if current.exact_eq(expected) => {}
            Ok(_) => {
                return Err(io_portable(
                    &canonical,
                    "internal.artifact_inputs_changed",
                    "the dependency import graph changed before its artifact build; retry the check"
                        .into(),
                ));
            }
            Err(message) => {
                return Err(io_portable(
                    &canonical,
                    "internal.artifact_inputs_changed",
                    message,
                ));
            }
        }
    }
    let inputs = match artifact_input_fingerprint(&canonical, opts, repo_root, proof_environment) {
        Ok(inputs) => inputs,
        Err(message) => {
            return Err(io_portable(
                &canonical,
                "internal.proof_fingerprint",
                message,
            ));
        }
    };
    let key = ArtifactBuildKey {
        path: canonical.clone(),
        inputs,
    };
    let (flight, leader) = {
        let mut map = cache().lock().unwrap_or_else(|poison| poison.into_inner());
        match map.get(&key) {
            Some(flight) => (flight.clone(), false),
            None => {
                let flight = Arc::new(ArtifactFlight {
                    result: Mutex::new(None),
                    ready: Condvar::new(),
                });
                map.insert(key.clone(), flight.clone());
                (flight, true)
            }
        }
    };

    if !leader {
        let mut slot = flight
            .result
            .lock()
            .unwrap_or_else(|poison| poison.into_inner());
        while slot.is_none() {
            slot = flight
                .ready
                .wait(slot)
                .unwrap_or_else(|poison| poison.into_inner());
        }
        let result = slot.as_ref().unwrap().clone();
        return result;
    }

    let leader = ArtifactLeader {
        key: key.clone(),
        flight,
        path: canonical.clone(),
        published: false,
    };
    let result = build_artifact(
        &canonical,
        opts,
        repo_root,
        key.inputs,
        expected,
        proof_environment,
    );
    leader.publish(result)
}

fn load_snapshot(path: &Path, opts: &Options) -> Result<SourceSnapshot, String> {
    let (_, modules) = modules::load(path, &opts.module_paths)
        .map_err(|(diagnostic, _)| format!("{}: {}", diagnostic.name, diagnostic.title))?;
    Ok(module_snapshot(&modules))
}

/// Fingerprint all inputs that can affect a per-module result before joining
/// an in-flight build. `modules::load` gives us the current resolved import
/// closure, so an unchanged root cannot reuse a flight after one of its
/// dependencies (or module-path resolution) changes.
fn artifact_input_fingerprint(
    path: &Path,
    opts: &Options,
    repo_root: &Path,
    proof_environment: &lean::ProofEnvironment,
) -> Result<u64, String> {
    let (load_error, modules) = match modules::load(path, &opts.module_paths) {
        Ok((_, modules)) => (None, modules),
        Err((diagnostic, modules)) => (Some(diagnostic), modules),
    };
    let mut hash = module_set_fingerprint(&modules, opts, repo_root, proof_environment.id());
    if let Some(diagnostic) = load_error {
        hash = fnv64(hash, b"load-error\0");
        hash = fnv64(hash, diagnostic.name.as_bytes());
        hash = fnv64(hash, &[0]);
        hash = fnv64(hash, diagnostic.title.as_bytes());
        hash = fnv64(hash, &[0]);
        hash = fnv64(hash, &diagnostic.span.start.to_le_bytes());
        hash = fnv64(hash, &diagnostic.span.end.to_le_bytes());
    }
    Ok(hash)
}

fn module_set_fingerprint(
    modules: &ModuleSet,
    opts: &Options,
    repo_root: &Path,
    proof_fingerprint: &str,
) -> u64 {
    let mut hash = fnv64(0, proof_fingerprint.as_bytes());
    hash = fnv64(hash, &[u8::from(opts.emit_lean_only)]);
    if let Ok(heartbeats) = std::env::var("SABLE_GRIND_HEARTBEATS") {
        hash = fnv64(hash, heartbeats.as_bytes());
    }

    hash = fnv64(hash, b"module-paths\0");
    for module_path in &opts.module_paths {
        hash = hash_relative_path(hash, repo_root, module_path);
        hash = fnv64(hash, &[0]);
    }

    for module in &modules.modules {
        hash = hash_relative_path(hash, repo_root, &module.path);
        hash = fnv64(hash, &[0]);
        hash = fnv64(hash, module.source.as_bytes());
        hash = fnv64(hash, &[0]);
    }
    hash = fnv64(hash, b"resolved-import-edges\0");
    for (importer, dependency) in &modules.import_edges {
        hash = fnv64(hash, &importer.to_le_bytes());
        hash = fnv64(hash, &dependency.to_le_bytes());
    }
    hash
}

fn hash_relative_path(seed: u64, repo_root: &Path, path: &Path) -> u64 {
    let root = repo_root
        .canonicalize()
        .unwrap_or_else(|_| repo_root.to_path_buf());
    let resolved = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    let label = resolved.strip_prefix(&root).unwrap_or(&resolved);
    fnv64(seed, label.to_string_lossy().as_bytes())
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

fn build_artifact(
    path: &Path,
    opts: &Options,
    repo_root: &Path,
    expected_inputs: u64,
    expected_snapshot: Option<&SourceSnapshot>,
    proof_environment: &lean::ProofEnvironment,
) -> ArtifactResult {
    let (mods, prep) = prepare_with_environment(path, opts, repo_root, proof_environment);
    let prep = match prep {
        Ok(p) => p,
        Err(diags) => {
            return Err(Arc::new(
                diags.iter().map(|d| to_portable(&mods, d)).collect(),
            ));
        }
    };
    if expected_snapshot.is_some_and(|expected| !prep.input_snapshot.exact_eq(expected)) {
        return Err(io_portable(
            path,
            "internal.artifact_inputs_changed",
            "the dependency import graph changed while its artifact was being prepared; retry the check"
                .into(),
        ));
    }
    if prep.proof_fingerprint != proof_environment.id() {
        return Err(io_portable(
            path,
            "internal.proof_fingerprint",
            "dependency preparation substituted a different immutable proof environment".into(),
        ));
    }
    let display = mods.modules[0].display.clone();
    let source: Arc<str> = Arc::from(mods.modules[0].source.as_str());
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
        if let Some(expected) = expected_snapshot {
            match load_snapshot(path, opts) {
                Ok(current) if current.exact_eq(expected) => {}
                _ => {
                    return Err(io_portable(
                        path,
                        "internal.artifact_inputs_changed",
                        "the dependency import graph changed before artifact reuse; retry the check"
                            .into(),
                    ));
                }
            }
        }
        if artifact_input_fingerprint(path, opts, repo_root, proof_environment).as_ref()
            != Ok(&expected_inputs)
        {
            return Err(io_portable(
                path,
                "internal.artifact_inputs_changed",
                "module inputs changed while locating its verified artifact; retry the check"
                    .into(),
            ));
        }
        if let Err(message) = require_file_content(&lean_path, &prep.emitted.lean_source) {
            return Err(io_portable(
                path,
                "internal.artifact_content_collision",
                message,
            ));
        }
        return Ok(Arc::new(ModuleArtifact {
            lean_name: prep.lean_name,
            names: prep.emitted.names.clone(),
            display,
            path: path.to_path_buf(),
            source,
            proof_fingerprint: prep.proof_fingerprint.clone(),
            inputs: prep.input_snapshot.clone(),
            warnings: Vec::new(),
        }));
    }

    if let Err(err) = write_immutable(&lean_path, &prep.emitted.lean_source) {
        return Err(io_portable(
            path,
            "internal.artifact_content_collision",
            err,
        ));
    }
    let tmp_olean = dir.join(format!(
        "{}.olean.tmp{}.{}",
        prep.lean_name,
        std::process::id(),
        temp_nonce(),
    ));
    let messages = match lean::run_lean(
        repo_root,
        proof_environment,
        &lean_path,
        Some(&tmp_olean),
        &prep.emitted.lean_source,
    ) {
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
    if artifact_input_fingerprint(path, opts, repo_root, proof_environment).as_ref()
        != Ok(&expected_inputs)
    {
        let _ = std::fs::remove_file(&tmp_olean);
        return Err(io_portable(
            path,
            "internal.artifact_inputs_changed",
            "module inputs changed while Lean was checking; retry the check".into(),
        ));
    }
    if let Err(message) = require_prepared_inputs(
        &prep.root_path,
        opts,
        &prep,
        "while Lean was checking the dependency artifact",
    ) {
        let _ = std::fs::remove_file(&tmp_olean);
        return Err(io_portable(
            path,
            "internal.artifact_inputs_changed",
            message,
        ));
    }
    if let Some(expected) = expected_snapshot {
        match load_snapshot(path, opts) {
            Ok(current) if current.exact_eq(expected) => {}
            _ => {
                let _ = std::fs::remove_file(&tmp_olean);
                return Err(io_portable(
                    path,
                    "internal.artifact_inputs_changed",
                    "the dependency import graph changed while Lean was checking; retry the check"
                        .into(),
                ));
            }
        }
    }
    if let Err(err) = std::fs::rename(&tmp_olean, &olean_path) {
        return Err(io_portable(
            path,
            "io.write",
            format!("cannot move {}: {err}", tmp_olean.display()),
        ));
    }
    if let Err(err) = write_atomic(&ok_path, "ok\n") {
        let _ = std::fs::remove_file(&olean_path);
        return Err(io_portable(path, "io.write", err));
    }
    if artifact_input_fingerprint(path, opts, repo_root, proof_environment).as_ref()
        != Ok(&expected_inputs)
    {
        let _ = std::fs::remove_file(&ok_path);
        let _ = std::fs::remove_file(&olean_path);
        return Err(io_portable(
            path,
            "internal.artifact_inputs_changed",
            "module inputs changed while publishing its verified artifact; retry the check".into(),
        ));
    }
    if let Err(message) = require_prepared_inputs(
        &prep.root_path,
        opts,
        &prep,
        "while publishing the dependency artifact",
    ) {
        let _ = std::fs::remove_file(&ok_path);
        let _ = std::fs::remove_file(&olean_path);
        return Err(io_portable(
            path,
            "internal.artifact_inputs_changed",
            message,
        ));
    }
    let mut warnings: Vec<PortableDiag> =
        lean::dedup_by_name(lean::diagnose_warnings(&prep.emitted, &prep.vc, &messages))
            .iter()
            .map(|d| to_portable(&mods, d))
            .collect();
    warnings.extend(prep.dep_warnings.iter().map(|d| to_portable(&mods, d)));
    Ok(Arc::new(ModuleArtifact {
        lean_name: prep.lean_name,
        names: prep.emitted.names.clone(),
        display,
        path: path.to_path_buf(),
        source,
        proof_fingerprint: prep.proof_fingerprint.clone(),
        inputs: prep.input_snapshot.clone(),
        warnings,
    }))
}

/// Materialize the root document at a content-addressed, immutable path.
/// Different source/profile/prelude versions therefore cannot overwrite the
/// bytes a concurrent daemon or batch check is reading. Identical versions
/// converge on the same exact file and may safely share a warm LSP document.
pub fn write_root_generated(
    repo_root: &Path,
    opts: &Options,
    prep: &Prepared,
) -> Result<PathBuf, String> {
    require_prepared_inputs(
        &prep.root_path,
        opts,
        prep,
        "before writing the generated root document",
    )?;
    prep.proof_environment.materialize_source(repo_root)?;
    let dir = repo_root.join(".sable-out").join("roots");
    std::fs::create_dir_all(&dir).map_err(|error| {
        format!(
            "cannot create generated-root directory {}: {error}",
            dir.display()
        )
    })?;
    let path = root_generated_path(repo_root, &prep.lean_name);
    write_immutable(&path, &prep.emitted.lean_source)?;
    require_prepared_inputs(
        &prep.root_path,
        opts,
        prep,
        "while writing the generated root document",
    )?;
    Ok(path)
}

fn root_generated_path(repo_root: &Path, lean_name: &str) -> PathBuf {
    repo_root
        .join(".sable-out")
        .join("roots")
        .join(format!("{lean_name}.lean"))
}

/// Record a root check's successful verification as an artifact stamp,
/// so importers reuse it instead of re-proving (the olean is compiled
/// on first import if this check ran through the daemon).
pub fn stamp_verified(repo_root: &Path, opts: &Options, prep: &Prepared) -> Result<(), String> {
    require_prepared_inputs(
        &prep.root_path,
        opts,
        prep,
        "before stamping the root artifact",
    )?;
    prep.proof_environment.validate_built(
        &prep.proof_environment.ensure_built(repo_root)?,
    )?;
    let dir = lean::modules_dir(repo_root);
    std::fs::create_dir_all(&dir).map_err(|e| format!("cannot create {}: {e}", dir.display()))?;
    write_immutable(
        &dir.join(format!("{}.lean", prep.lean_name)),
        &prep.emitted.lean_source,
    )?;
    let ok_path = dir.join(format!("{}.ok", prep.lean_name));
    write_atomic(&ok_path, "ok\n")?;
    if let Err(error) = require_prepared_inputs(
        &prep.root_path,
        opts,
        prep,
        "while stamping the root artifact",
    ) {
        let _ = std::fs::remove_file(&ok_path);
        return Err(error);
    }
    Ok(())
}

/// Atomic-enough write for concurrent checkers: temp file + rename, so
/// readers never see a torn file.
fn write_atomic(path: &Path, content: &str) -> Result<(), String> {
    let tmp = path.with_extension(format!("tmp{}.{}", std::process::id(), temp_nonce()));
    std::fs::write(&tmp, content).map_err(|e| format!("cannot write {}: {e}", tmp.display()))?;
    std::fs::rename(&tmp, path).map_err(|e| format!("cannot move {}: {e}", tmp.display()))
}

/// Publish a content-addressed file without ever replacing an existing path.
/// `hard_link` is the atomic create-if-absent operation; a racing identical
/// writer merely verifies the winner's bytes.
fn write_immutable(path: &Path, content: &str) -> Result<(), String> {
    if path.is_file() {
        return require_file_content(path, content);
    }
    let tmp = path.with_extension(format!("tmp{}.{}", std::process::id(), temp_nonce()));
    std::fs::write(&tmp, content).map_err(|error| {
        format!(
            "cannot write temporary generated document {}: {error}",
            tmp.display()
        )
    })?;
    let publish = std::fs::hard_link(&tmp, path);
    let _ = std::fs::remove_file(&tmp);
    match publish {
        Ok(()) => require_file_content(path, content),
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
            require_file_content(path, content)
        }
        Err(error) => Err(format!(
            "cannot publish generated document {}: {error}",
            path.display()
        )),
    }
}

fn require_file_content(path: &Path, expected: &str) -> Result<(), String> {
    let actual = std::fs::read_to_string(path)
        .map_err(|error| format!("cannot read generated document {}: {error}", path.display()))?;
    if actual == expected {
        Ok(())
    } else {
        Err(format!(
            "content-addressed generated document {} contains different bytes",
            path.display()
        ))
    }
}

fn temp_nonce() -> u64 {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    NEXT.fetch_add(1, Ordering::Relaxed)
}

/// `<stem>_<hash>` — the content-addressed Lean module name. The hash
/// seeds with the prelude (sources, toolchain pin, lakefile), so a
/// prelude change invalidates every artifact; dep artifacts are pinned
/// transitively through the `import` lines inside `content`.
fn artifact_name(path: &Path, content: &str, proof_fingerprint: &str) -> String {
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
    let h = fnv64(fnv64(0, proof_fingerprint.as_bytes()), content.as_bytes());
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

#[cfg(test)]
mod tests {
    use super::{SourceSnapshot, artifact_name, root_generated_path};
    use std::path::{Path, PathBuf};
    use std::sync::Arc;

    #[test]
    fn root_generated_paths_bind_content_and_proof_environment() {
        let source = Path::new("left/main.sable");
        let first = artifact_name(source, "import Sable\n-- first\n", "proof-a");
        let edited = artifact_name(source, "import Sable\n-- edited\n", "proof-a");
        let new_proof = artifact_name(source, "import Sable\n-- first\n", "proof-b");

        assert_ne!(first, edited);
        assert_ne!(first, new_proof);
        assert_ne!(
            root_generated_path(Path::new("/repo"), &first),
            root_generated_path(Path::new("/repo"), &edited)
        );
        assert_eq!(
            root_generated_path(Path::new("/repo"), &first),
            root_generated_path(Path::new("/repo"), &first)
        );
    }

    #[test]
    fn dependency_snapshot_keeps_exact_resolved_subgraph() {
        // A imports B then D; B imports C. Edge storage may be postorder,
        // while the canonical snapshot must match loading B as its own root.
        let graph = SourceSnapshot {
            modules: ["A", "B", "C", "D"]
                .into_iter()
                .map(|name| (PathBuf::from(format!("/{name}.sable")), Arc::from(name)))
                .collect(),
            edges: vec![(1, 2), (0, 1), (0, 3)],
        };
        let b = graph.rooted_at(Path::new("/B.sable")).unwrap();
        assert_eq!(
            b.modules
                .iter()
                .map(|(path, _)| path.as_path())
                .collect::<Vec<_>>(),
            [Path::new("/B.sable"), Path::new("/C.sable")]
        );
        assert_eq!(b.edges, vec![(0, 1)]);
    }
}
