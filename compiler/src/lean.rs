//! Lean file generation, invocation, and diagnostic mapping.
//!
//! One generated file per checked .sable file: clause well-formedness defs
//! first (so a clause that fails to elaborate maps to its own span), then
//! one theorem per obligation, proved `by sable_auto`. A source map from
//! generated-file lines back to obligations/clauses turns `lean --json`
//! messages into .sable diagnostics.

use crate::diag::Diagnostic;
use crate::span::Span;
use crate::vcgen::{Obligation, VcResult};
use std::collections::BTreeMap;
use std::fs::{File, OpenOptions};
use std::io::Write;
use std::os::fd::AsRawFd;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

enum MapTarget {
    Clause {
        span: Span,
        desc: String,
    },
    Obligation(usize),
    /// Theorem proved by a user discharge script; errors point at the
    /// discharge block.
    Discharged {
        name: String,
        span: Span,
        goal: String,
    },
}

struct MapEntry {
    first_line: usize,
    last_line: usize,
    target: MapTarget,
}

/// The Lean-level names a generated module file declares. Importers
/// subtract these sets so a declaration is emitted (and verified) in
/// exactly one file of the import DAG.
#[derive(Default, Clone)]
pub struct EmittedNames {
    /// Structure names (`lean_class_name`).
    pub classes: std::collections::HashSet<String>,
    /// Ghost def/theorem head names.
    pub ghosts: std::collections::HashSet<String>,
    /// Clause well-formedness def names.
    pub wfs: std::collections::HashSet<String>,
    /// Obligation theorem names.
    pub thms: std::collections::HashSet<String>,
    /// Obligation names (escape-hatch ownership checks).
    pub obligations: std::collections::HashSet<String>,
}

impl EmittedNames {
    pub fn is_empty(&self) -> bool {
        self.classes.is_empty()
            && self.ghosts.is_empty()
            && self.wfs.is_empty()
            && self.thms.is_empty()
    }
}

pub struct Emitted {
    pub lean_source: String,
    /// What this file declares (after exclusion filtering).
    pub names: EmittedNames,
    map: Vec<MapEntry>,
}

struct Emitter {
    buf: String,
    line: usize,
}

impl Emitter {
    fn push(&mut self, s: &str) {
        for l in s.split('\n') {
            self.buf.push_str(l);
            self.buf.push('\n');
            self.line += 1;
        }
    }
}

/// Emit a module's Lean file. `imports` are generated dependency
/// artifacts (`import <name>` lines after `import Sable`); anything
/// named in `exclude` is declared by one of those imports and is
/// filtered out here — the import supplies it, already verified.
pub fn emit(
    vc: &VcResult,
    discharges: &[crate::ast::Discharge],
    skip: &std::collections::HashSet<String>,
    imports: &[String],
    exclude: &EmittedNames,
) -> Emitted {
    let mut e = Emitter {
        buf: String::new(),
        line: 0,
    };
    let mut map = Vec::new();
    let mut names = EmittedNames::default();

    e.push("import Sable");
    for i in imports {
        e.push(&format!("import {i}"));
    }
    e.push("open Sable");
    e.push("set_option linter.unusedVariables false");
    // Test/CI hook: shrink or disable the grind heartbeat budget
    // without touching source (the option itself lives in the prelude).
    if let Ok(v) = std::env::var("SABLE_GRIND_HEARTBEATS") {
        if v.parse::<u64>().is_ok() {
            e.push(&format!("set_option sable.grindHeartbeats {v}"));
        }
    }
    // The trust manifest, inside the hashed content. Changing an audit id
    // or adding an extern has to invalidate the artifact exactly as
    // changing a proof does, and an artifact's validity is mere existence
    // of its `.ok` file — so this must be part of the bytes, not a file
    // beside them (ADR 0027).
    if !vc.trust.externs.is_empty() {
        e.push("-- trusted boundary: audited extern contracts");
        for (id, reason, name) in &vc.trust.externs {
            e.push(&format!("--   {id} ({name}): {reason}"));
        }
    }
    if !vc.machine.profiles.is_empty() {
        e.push("-- formal machine profiles (kernel-checked, not trusted axioms)");
        for (id, hash) in &vc.machine.profiles {
            e.push(&format!("--   {id} {hash}"));
        }
        if !vc.machine.intrinsics.is_empty() {
            e.push(&format!(
                "--   intrinsics: {}",
                vc.machine.intrinsics.join(", ")
            ));
        }
    }
    e.push("");

    for r in &vc.records {
        let lean_name = crate::vcgen::lean_record_name(&r.name);
        if exclude.classes.contains(&lean_name) {
            continue;
        }
        names.classes.insert(lean_name.clone());
        let first = e.line + 1;
        e.push(&format!("structure {lean_name} where"));
        for field in &r.fields {
            e.push(&format!("  {} : {}", field.name, field.lean_ty));
        }
        e.push("");
        e.push(&format!("namespace {lean_name}"));
        e.push(&format!(
            "def layout : Sable.Layout := ⟨{}, {}⟩",
            r.layout.size, r.layout.align
        ));
        e.push(&format!(
            "@[simp] theorem layout_size : layout.size = {} := rfl",
            r.layout.size
        ));
        e.push(&format!(
            "@[simp] theorem layout_align : layout.align = {} := rfl",
            r.layout.align
        ));
        for field in &r.fields {
            e.push(&format!(
                "def {}Offset : Int := {}",
                field.name, field.offset
            ));
        }
        let mut exponent = 0u32;
        let mut align = r.layout.align;
        while align > 1 {
            align /= 2;
            exponent += 1;
        }
        e.push("theorem layout_wf : layout.wf := by");
        e.push(&format!(
            "  refine ⟨by decide, by decide, ⟨{exponent}, rfl⟩⟩"
        ));
        for field in &r.fields {
            e.push(&format!(
                "theorem {}_fits : Sable.Layout.fieldFits layout {} {}Offset := by simp [Sable.Layout.fieldFits, layout, {}Offset, {}]",
                field.name, field.layout, field.name, field.name, field.layout
            ));
        }
        for left in 0..r.fields.len() {
            for right in (left + 1)..r.fields.len() {
                let lfield = &r.fields[left];
                let rfield = &r.fields[right];
                e.push(&format!(
                    "theorem {}_{}_disjoint : Sable.Layout.fieldsDisjoint {} {}Offset {} {}Offset := by simp [Sable.Layout.fieldsDisjoint, {}Offset, {}Offset, {}, {}]",
                    lfield.name,
                    rfield.name,
                    lfield.layout,
                    lfield.name,
                    rfield.layout,
                    rfield.name,
                    lfield.name,
                    rfield.name,
                    lfield.layout,
                    rfield.layout
                ));
            }
        }
        let value_wf: Vec<&str> = r.fields.iter().filter_map(|f| f.wf.as_deref()).collect();
        e.push(&format!("def wf (value : {lean_name}) : Prop :="));
        e.push(&format!(
            "  {}",
            if value_wf.is_empty() {
                "True".to_string()
            } else {
                value_wf.join(" ∧ ")
            }
        ));
        e.push(&format!(
            "def cellWf (cell : Sable.PointsToView {lean_name}) : Prop :="
        ));
        e.push("  cell.layout = layout ∧ 0 ≤ cell.off ∧ cell.off % cell.layout.align = 0 ∧");
        e.push("    match cell.state with | .uninit => True | .init value => wf value");
        e.push(&format!(
            "def fromSpan (span : Sable.SpanView) : Sable.PointsToView {lean_name} :="
        ));
        e.push("  { alloc := span.alloc, off := span.off, layout := layout, state := .uninit }");
        e.push("@[simp] theorem fromSpan_alloc (span : Sable.SpanView) : (fromSpan span).alloc = span.alloc := rfl");
        e.push("@[simp] theorem fromSpan_off (span : Sable.SpanView) : (fromSpan span).off = span.off := rfl");
        e.push("@[simp] theorem fromSpan_layout (span : Sable.SpanView) : (fromSpan span).layout = layout := rfl");
        e.push("@[simp] theorem fromSpan_state (span : Sable.SpanView) : (fromSpan span).state = .uninit := rfl");
        e.push(&format!(
            "def toSpan (cell : Sable.PointsToView {lean_name}) : Sable.SpanView :="
        ));
        e.push("  { alloc := cell.alloc, off := cell.off, len := cell.layout.size,");
        e.push("    bytes := ⟨cell.layout.size, fun _ => .init 0⟩ }");
        e.push(&format!("@[simp] theorem toSpan_alloc (cell : Sable.PointsToView {lean_name}) : (toSpan cell).alloc = cell.alloc := rfl"));
        e.push(&format!("@[simp] theorem toSpan_off (cell : Sable.PointsToView {lean_name}) : (toSpan cell).off = cell.off := rfl"));
        e.push(&format!("@[simp] theorem toSpan_len (cell : Sable.PointsToView {lean_name}) : (toSpan cell).len = cell.layout.size := rfl"));
        e.push(&format!("end {lean_name}"));
        e.push("");
        map.push(MapEntry {
            first_line: first,
            last_line: e.line,
            target: MapTarget::Clause {
                span: r.span,
                desc: "record declaration".into(),
            },
        });
    }

    for c in &vc.classes {
        let lean_name = crate::vcgen::lean_class_name(&c.name);
        if exclude.classes.contains(&lean_name) {
            continue;
        }
        names.classes.insert(lean_name);
        let first = e.line + 1;
        e.push(&format!(
            "structure {} where",
            crate::vcgen::lean_class_name(&c.name)
        ));
        for (fname, fty) in &c.fields {
            e.push(&format!("  {fname} : {fty}"));
        }
        e.push("");
        map.push(MapEntry {
            first_line: first,
            last_line: e.line,
            target: MapTarget::Clause {
                span: c.span,
                desc: "class declaration".into(),
            },
        });
    }

    for g in &vc.ghosts {
        let head = ghost_head_name(&g.text);
        if exclude.ghosts.contains(&head) {
            continue;
        }
        names.ghosts.insert(head);
        let first = e.line + 1;
        // Non-recursive ghost defs get @[simp] so contracts naming them
        // unfold under the portfolio; recursive ones would loop and are
        // unfolded manually in discharges. `#[unfold]` opts an item in
        // explicitly — typically a conditional step lemma whose side
        // conditions gate the rewrite to concrete data.
        let attr = if g.unfold || (g.keyword == "def" && !ghost_recursive(&g.text)) {
            "@[simp] "
        } else {
            ""
        };
        e.push(&format!("{attr}{} {}", g.keyword, g.text));
        e.push("");
        map.push(MapEntry {
            first_line: first,
            last_line: e.line,
            target: MapTarget::Clause {
                span: g.span,
                desc: format!("ghost `{}`", g.keyword),
            },
        });
    }

    for wf in &vc.clause_wfs {
        if exclude.wfs.contains(&wf.def_name) {
            continue;
        }
        names.wfs.insert(wf.def_name.clone());
        let first = e.line + 1;
        e.push(&format!(
            "def {} {} : {} :=",
            wf.def_name,
            binder_list(&wf.binders),
            wf.result_ty
        ));
        e.push(&format!("  ({})", wf.text));
        e.push("");
        map.push(MapEntry {
            first_line: first,
            last_line: e.line,
            target: MapTarget::Clause {
                span: wf.span,
                desc: wf.desc.clone(),
            },
        });
    }

    for (i, ob) in vc.obligations.iter().enumerate() {
        // Deferred/assumed obligations become runtime traps or axioms;
        // no theorem is emitted (their goals are already assumed
        // downstream by the generator, which is exactly their semantics).
        if skip.contains(&ob.name) || exclude.thms.contains(&ob.thm_name) {
            continue;
        }
        names.thms.insert(ob.thm_name.clone());
        names.obligations.insert(ob.name.clone());
        let discharge = discharges.iter().find(|d| d.name == ob.name);
        let first = e.line + 1;
        e.push(&format!(
            "/-- `{}` — {} -/",
            ob.name,
            doc_safe(&ob.kind_desc)
        ));
        e.push(&format!(
            "theorem {} {}",
            ob.thm_name,
            binder_list(&ob.binders)
        ));
        for (hname, hprop) in &ob.hyps {
            e.push(&format!("    ({hname} : {hprop})"));
        }
        match discharge {
            None => e.push(&format!("    : ({}) := by sable_auto", ob.goal)),
            Some(d) => {
                e.push(&format!("    : ({}) := by", ob.goal));
                for line in d.script.lines() {
                    e.push(&format!("  {line}"));
                }
            }
        }
        e.push("");
        map.push(MapEntry {
            first_line: first,
            last_line: e.line,
            target: match discharge {
                None => MapTarget::Obligation(i),
                Some(d) => MapTarget::Discharged {
                    name: ob.name.clone(),
                    span: d.span,
                    goal: ob.goal.clone(),
                },
            },
        });
    }

    Emitted {
        lean_source: e.buf,
        names,
        map,
    }
}

/// Head name of a ghost `def`/`theorem` (the first identifier of its
/// verbatim text).
pub fn ghost_head_name(text: &str) -> String {
    text.trim_start()
        .chars()
        .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
        .collect()
}

fn binder_list(binders: &[(String, String)]) -> String {
    binders
        .iter()
        .map(|(name, ty)| format!("({name} : {ty})"))
        .collect::<Vec<_>>()
        .join(" ")
}

/// A ghost def is recursive if its body mentions its own head name.
fn ghost_recursive(text: &str) -> bool {
    let name = ghost_head_name(text);
    match text.split_once(":=") {
        Some((_, body)) => !name.is_empty() && crate::vcgen::mentions(body, &name),
        None => false,
    }
}

fn doc_safe(s: &str) -> String {
    s.replace("-/", "- /")
}

/// Locate the repo root: the nearest ancestor containing `lean/lean-toolchain`.
pub fn find_repo_root(start: &Path) -> Option<PathBuf> {
    let mut dir = if start.is_dir() {
        start.to_path_buf()
    } else {
        start.parent()?.to_path_buf()
    };
    loop {
        if dir.join("lean").join("lean-toolchain").is_file() {
            return Some(dir);
        }
        if !dir.pop() {
            return None;
        }
    }
}

pub struct LeanMessage {
    pub severity: String,
    pub line: usize,
    pub data: String,
}

/// The generated-artifact directory (`import`able compiled modules) —
/// on `LEAN_PATH` for every check, whether or not it exists yet.
pub fn modules_dir(repo_root: &Path) -> PathBuf {
    repo_root.join(".sable-out").join("modules")
}

/// Exact repository-local inputs that can affect a generated proof. The FNV
/// identifier is only a compact directory/name tag; every reuse also compares
/// this complete map, so a hash collision fails closed.
#[derive(Clone)]
pub struct ProofEnvironment {
    id: String,
    files: Arc<BTreeMap<String, Vec<u8>>>,
}

impl ProofEnvironment {
    /// Capture one immutable view before profile generation or dependency work.
    pub fn capture(repo_root: &Path) -> Result<Self, String> {
        Self::from_files(capture_proof_files(repo_root)?)
    }

    fn from_files(files: BTreeMap<String, Vec<u8>>) -> Result<Self, String> {
        if files.is_empty() {
            return Err("proof environment contains no inputs".into());
        }
        let mut hash = 0xcbf29ce484222325u64;
        for (label, bytes) in &files {
            hash = fingerprint_bytes(hash, &(label.len() as u64).to_le_bytes());
            hash = fingerprint_bytes(hash, label.as_bytes());
            hash = fingerprint_bytes(hash, &(bytes.len() as u64).to_le_bytes());
            hash = fingerprint_bytes(hash, bytes);
        }
        Ok(Self {
            // Version the identity domain so evidence produced by the old
            // mutable-checkout builder can never be mistaken for v2 evidence.
            id: format!("proof-env-v2-fnv64:{hash:016x}"),
            files: Arc::new(files),
        })
    }

    pub fn id(&self) -> &str {
        &self.id
    }

    /// Load a client-selected published snapshot without consulting the live
    /// checkout. This is how a long-lived daemon recovers the exact bytes named
    /// in a request after those checkout files have changed.
    pub fn load_published(repo_root: &Path, id: &str) -> Result<Self, String> {
        validate_environment_id(id)?;
        validate_proof_environment_dir(repo_root, id)?;
        let source = proof_environment_dir(repo_root, id).join("source");
        let environment = Self::capture(&source)?;
        if environment.id != id {
            return Err(format!(
                "published proof environment {} contains bytes for {}",
                source.display(),
                environment.id
            ));
        }
        Ok(environment)
    }

    /// Atomically publish a repo-shaped source snapshot. A racing process may
    /// win the rename, but it is accepted only after an exact byte-map match.
    pub fn materialize_source(&self, repo_root: &Path) -> Result<PathBuf, String> {
        let environment_dir = ensure_proof_environment_dir(repo_root, &self.id)?;
        let source = environment_dir.join("source");
        if std::fs::symlink_metadata(&source).is_ok() {
            self.validate_snapshot(&source, "published source snapshot")?;
            return Ok(source);
        }

        let temporary = unique_directory(&environment_dir, "source.tmp")?;
        let result = (|| {
            write_proof_files(&temporary, &self.files)?;
            self.validate_snapshot(&temporary, "temporary source snapshot")?;
            match std::fs::rename(&temporary, &source) {
                Ok(()) => {}
                Err(_error) if std::fs::symlink_metadata(&source).is_ok() => {
                    self.validate_snapshot(&source, "racing published source snapshot")?;
                    let _ = std::fs::remove_dir_all(&temporary);
                    return Ok(source.clone());
                }
                Err(error) => {
                    return Err(format!(
                        "cannot publish proof source snapshot {}: {error}",
                        source.display()
                    ));
                }
            }
            self.validate_snapshot(&source, "published source snapshot")?;
            Ok(source.clone())
        })();
        if result.is_err() && temporary.is_dir() {
            // The name is unique to this process/attempt; never clean a path a
            // different builder could own.
            let _ = std::fs::remove_dir_all(&temporary);
        }
        result
    }

    /// Build at the final stable path. Lake and Lean can embed absolute paths,
    /// so building elsewhere and renaming would not produce an immutable,
    /// reproducible workspace. A per-id advisory lock serializes processes;
    /// READY is written last and a READY workspace is never rebuilt.
    pub fn ensure_built(&self, repo_root: &Path) -> Result<PathBuf, String> {
        self.materialize_source(repo_root)?;
        let environment_dir = proof_environment_dir(repo_root, &self.id);
        let _lock = ProofBuildLock::acquire(&environment_dir.join("build.lock"))?;
        self.validate_snapshot(&environment_dir.join("source"), "published source snapshot")?;

        let built = environment_dir.join("built");
        let ready = built.join("READY");
        if std::fs::symlink_metadata(&ready).is_ok() {
            match self.validate_built(&built) {
                Ok(()) => return Ok(built),
                Err(_) => {
                    // READY is published atomically below, but older/crashed
                    // writers may have left a partial marker. Under this id's
                    // lock, an invalid marker is incomplete state, not a
                    // permanent poisoned cache entry.
                    remove_unready_built(&environment_dir, &built)?;
                }
            }
        }
        // The invalid-READY branch above has already removed `built`.
        if std::fs::symlink_metadata(&built).is_ok() {
            remove_unready_built(&environment_dir, &built)?;
        }

        std::fs::create_dir(&built)
            .map_err(|error| format!("cannot create proof build {}: {error}", built.display()))?;
        write_proof_files(&built, &self.files)?;
        self.validate_snapshot(&built, "unbuilt proof workspace")?;

        let lean_dir = built.join("lean");
        let build = Command::new("lake")
            .args(["-Kjobs=1", "build"])
            .current_dir(&lean_dir)
            .output()
            .map_err(|error| format!("failed to run `lake -Kjobs=1 build`: {error}"))?;
        if !build.status.success() {
            return Err(format!(
                "`lake -Kjobs=1 build` failed in {}:\n{}{}",
                lean_dir.display(),
                String::from_utf8_lossy(&build.stdout),
                String::from_utf8_lossy(&build.stderr),
            ));
        }
        self.validate_snapshot(&built, "completed proof build")?;
        require_sable_olean(&built)?;
        publish_ready(&built, &ready, &self.id)?;
        self.validate_built(&built)?;
        Ok(built)
    }

    pub fn validate_built(&self, built: &Path) -> Result<(), String> {
        self.validate_snapshot(built, "immutable proof build")?;
        let ready = built.join("READY");
        let metadata = std::fs::symlink_metadata(&ready).map_err(|error| {
            format!(
                "cannot inspect proof readiness {}: {error}",
                ready.display()
            )
        })?;
        if metadata.file_type().is_symlink() || !metadata.is_file() {
            return Err(format!(
                "proof readiness {} is not a regular file",
                ready.display()
            ));
        }
        let actual = std::fs::read_to_string(&ready)
            .map_err(|error| format!("cannot read proof readiness {}: {error}", ready.display()))?;
        if actual != format!("{}\n", self.id) {
            return Err(format!(
                "proof readiness {} does not match environment {}",
                ready.display(),
                self.id
            ));
        }
        require_sable_olean(built)
    }

    fn validate_snapshot(&self, root: &Path, description: &str) -> Result<(), String> {
        let actual = capture_proof_files(root)?;
        if actual == *self.files {
            Ok(())
        } else {
            Err(format!(
                "{description} {} does not exactly match proof environment {} (possible content-address collision)",
                root.display(),
                self.id
            ))
        }
    }
}

fn publish_ready(built: &Path, ready: &Path, id: &str) -> Result<(), String> {
    let temporary = built.join(format!(
        ".READY.tmp.{}.{}",
        std::process::id(),
        NEXT_PROOF_TEMP.fetch_add(1, Ordering::Relaxed)
    ));
    let result = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&temporary)
        .and_then(|mut file| {
            writeln!(file, "{id}")?;
            file.sync_all()
        })
        .and_then(|()| std::fs::rename(&temporary, ready));
    if result.is_err() {
        let _ = std::fs::remove_file(&temporary);
    }
    result.map_err(|error| {
        format!(
            "cannot publish proof-build readiness {}: {error}",
            ready.display()
        )
    })
}

/// Compatibility helper for callers that only need a fresh tag. Verification
/// paths carry `ProofEnvironment` itself and never rely on before/after hashes.
pub fn proof_environment_fingerprint(repo_root: &Path) -> Result<String, String> {
    ProofEnvironment::capture(repo_root).map(|environment| environment.id)
}

fn proof_environment_dir(repo_root: &Path, id: &str) -> PathBuf {
    repo_root
        .join(".sable-out")
        .join("proof-envs")
        .join(id.replace(':', "_"))
}

fn validate_environment_id(id: &str) -> Result<(), String> {
    let Some(hex) = id.strip_prefix("proof-env-v2-fnv64:") else {
        return Err(format!("invalid proof-environment id `{id}`"));
    };
    if hex.len() == 16 && hex.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        Ok(())
    } else {
        Err(format!("invalid proof-environment id `{id}`"))
    }
}

fn ensure_proof_environment_dir(repo_root: &Path, id: &str) -> Result<PathBuf, String> {
    validate_environment_id(id)?;
    let output = repo_root.join(".sable-out");
    ensure_local_directory(&output)?;
    let environments = output.join("proof-envs");
    ensure_local_directory(&environments)?;
    let environment = proof_environment_dir(repo_root, id);
    ensure_local_directory(&environment)?;
    Ok(environment)
}

fn validate_proof_environment_dir(repo_root: &Path, id: &str) -> Result<(), String> {
    validate_environment_id(id)?;
    validate_local_directory(&repo_root.join(".sable-out"))?;
    validate_local_directory(&repo_root.join(".sable-out/proof-envs"))?;
    validate_local_directory(&proof_environment_dir(repo_root, id))
}

fn validate_local_directory(path: &Path) -> Result<(), String> {
    let metadata = std::fs::symlink_metadata(path).map_err(|error| {
        format!(
            "cannot inspect managed directory {}: {error}",
            path.display()
        )
    })?;
    if metadata.file_type().is_symlink() || !metadata.is_dir() {
        Err(format!(
            "managed proof-environment path {} must be a local directory",
            path.display()
        ))
    } else {
        Ok(())
    }
}

fn ensure_local_directory(path: &Path) -> Result<(), String> {
    match std::fs::symlink_metadata(path) {
        Ok(_) => validate_local_directory(path),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            match std::fs::create_dir(path) {
                Ok(()) => Ok(()),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
                    validate_local_directory(path)
                }
                Err(error) => Err(format!(
                    "cannot create managed directory {}: {error}",
                    path.display()
                )),
            }
        }
        Err(error) => Err(format!(
            "cannot inspect managed directory {}: {error}",
            path.display()
        )),
    }
}

fn capture_proof_files(repo_root: &Path) -> Result<BTreeMap<String, Vec<u8>>, String> {
    let root_metadata = std::fs::symlink_metadata(repo_root).map_err(|error| {
        format!(
            "cannot inspect proof snapshot root {}: {error}",
            repo_root.display()
        )
    })?;
    if root_metadata.file_type().is_symlink() || !root_metadata.is_dir() {
        return Err(format!(
            "proof snapshot root {} must be a local directory",
            repo_root.display()
        ));
    }
    let lean_relative = Path::new("lean");
    let lean_dir = repo_root.join(lean_relative);
    let lean_metadata = std::fs::symlink_metadata(&lean_dir).map_err(|error| {
        format!(
            "cannot inspect proof workspace {}: {error}",
            lean_dir.display()
        )
    })?;
    if lean_metadata.file_type().is_symlink() || !lean_metadata.is_dir() {
        return Err(format!(
            "proof workspace {} must be a repository-local directory",
            lean_dir.display()
        ));
    }

    let mut files = BTreeMap::new();
    for relative in [
        "lean/lean-toolchain",
        "lean/lakefile.toml",
        "lean/lake-manifest.json",
        "lean/Sable.lean",
    ] {
        capture_proof_file(repo_root, Path::new(relative), &mut files)?;
    }
    capture_lean_tree(repo_root, lean_relative, &mut files)?;
    Ok(files)
}

fn capture_lean_tree(
    root: &Path,
    relative: &Path,
    files: &mut BTreeMap<String, Vec<u8>>,
) -> Result<(), String> {
    let directory = root.join(relative);
    let directory_metadata = std::fs::symlink_metadata(&directory).map_err(|error| {
        format!(
            "cannot inspect proof source directory {}: {error}",
            directory.display()
        )
    })?;
    if directory_metadata.file_type().is_symlink() || !directory_metadata.is_dir() {
        return Err(format!(
            "proof source directory {} must be a local directory",
            directory.display()
        ));
    }
    let entries = std::fs::read_dir(&directory).map_err(|error| {
        format!(
            "cannot read proof source directory {}: {error}",
            directory.display()
        )
    })?;
    let mut children = entries
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| format!("cannot read an entry in {}: {error}", directory.display()))?;
    children.sort_by_key(std::fs::DirEntry::file_name);
    for child in children {
        if child.file_name().to_str() == Some(".lake") {
            continue;
        }
        let child_relative = relative.join(child.file_name());
        let path = child.path();
        let metadata = std::fs::symlink_metadata(&path)
            .map_err(|error| format!("cannot inspect proof source {}: {error}", path.display()))?;
        if metadata.file_type().is_symlink() {
            return Err(format!(
                "proof source {} is a symlink; proof snapshots require local regular files",
                path.display()
            ));
        }
        if metadata.is_dir() {
            capture_lean_tree(root, &child_relative, files)?;
        } else if child_relative
            .extension()
            .is_some_and(|extension| extension == "lean")
        {
            capture_proof_file(root, &child_relative, files)?;
        }
    }
    Ok(())
}

fn capture_proof_file(
    root: &Path,
    relative: &Path,
    files: &mut BTreeMap<String, Vec<u8>>,
) -> Result<(), String> {
    let label = relative
        .to_str()
        .ok_or_else(|| format!("proof input path {} is not UTF-8", relative.display()))?
        .replace(std::path::MAIN_SEPARATOR, "/");
    let path = root.join(relative);
    let metadata = std::fs::symlink_metadata(&path)
        .map_err(|error| format!("cannot inspect proof input {}: {error}", path.display()))?;
    if metadata.file_type().is_symlink() || !metadata.is_file() {
        return Err(format!(
            "proof input {} must be a repository-local regular file",
            path.display()
        ));
    }
    let bytes = std::fs::read(&path)
        .map_err(|error| format!("cannot read proof input {}: {error}", path.display()))?;
    files.insert(label, bytes);
    Ok(())
}

fn write_proof_files(root: &Path, files: &BTreeMap<String, Vec<u8>>) -> Result<(), String> {
    for (label, bytes) in files {
        let path = root.join(label);
        let parent = path
            .parent()
            .ok_or_else(|| format!("proof input `{label}` has no parent"))?;
        std::fs::create_dir_all(parent)
            .map_err(|error| format!("cannot create {}: {error}", parent.display()))?;
        OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&path)
            .and_then(|mut file| file.write_all(bytes))
            .map_err(|error| format!("cannot write proof input {}: {error}", path.display()))?;
    }
    Ok(())
}

fn unique_directory(parent: &Path, prefix: &str) -> Result<PathBuf, String> {
    for _ in 0..100 {
        let nonce = NEXT_PROOF_TEMP.fetch_add(1, Ordering::Relaxed);
        let path = parent.join(format!(".{prefix}.{}.{}", std::process::id(), nonce));
        match std::fs::create_dir(&path) {
            Ok(()) => return Ok(path),
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(format!("cannot create {}: {error}", path.display())),
        }
    }
    Err(format!(
        "cannot allocate a unique proof snapshot directory in {}",
        parent.display()
    ))
}

static NEXT_PROOF_TEMP: AtomicU64 = AtomicU64::new(0);

fn remove_unready_built(environment_dir: &Path, built: &Path) -> Result<(), String> {
    if built.parent() != Some(environment_dir)
        || built.file_name().and_then(|name| name.to_str()) != Some("built")
    {
        return Err(format!(
            "refusing to replace out-of-scope proof build {}",
            built.display()
        ));
    }
    let metadata = std::fs::symlink_metadata(built).map_err(|error| {
        format!(
            "cannot inspect incomplete proof build {}: {error}",
            built.display()
        )
    })?;
    if metadata.file_type().is_symlink() || !metadata.is_dir() {
        return Err(format!(
            "incomplete proof build {} is not an owned directory",
            built.display()
        ));
    }
    std::fs::remove_dir_all(built).map_err(|error| {
        format!(
            "cannot replace incomplete proof build {}: {error}",
            built.display()
        )
    })
}

fn require_sable_olean(built: &Path) -> Result<(), String> {
    let olean = built.join("lean/.lake/build/lib/lean/Sable.olean");
    let metadata = std::fs::symlink_metadata(&olean)
        .map_err(|error| format!("proof build is missing {}: {error}", olean.display()))?;
    if metadata.file_type().is_symlink() || !metadata.is_file() {
        Err(format!(
            "proof build output {} is not a regular file",
            olean.display()
        ))
    } else {
        Ok(())
    }
}

fn fingerprint_bytes(mut hash: u64, bytes: &[u8]) -> u64 {
    for &byte in bytes {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }
    hash
}

struct ProofBuildLock(File);

impl ProofBuildLock {
    fn acquire(path: &Path) -> Result<Self, String> {
        if let Ok(metadata) = std::fs::symlink_metadata(path) {
            if metadata.file_type().is_symlink() || !metadata.is_file() {
                return Err(format!(
                    "proof-build lock {} must be a local regular file",
                    path.display()
                ));
            }
        }
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .open(path)
            .map_err(|error| format!("cannot open proof-build lock {}: {error}", path.display()))?;
        // This crate's daemon already requires Unix sockets. `flock` keeps a
        // crashed process from leaving a permanent lock-directory tombstone.
        let result = unsafe { process_flock(file.as_raw_fd(), LOCK_EXCLUSIVE) };
        if result != 0 {
            return Err(format!(
                "cannot lock proof-build lock {}: {}",
                path.display(),
                std::io::Error::last_os_error()
            ));
        }
        Ok(Self(file))
    }
}

impl Drop for ProofBuildLock {
    fn drop(&mut self) {
        let _ = unsafe { process_flock(self.0.as_raw_fd(), LOCK_UNLOCK) };
    }
}

const LOCK_EXCLUSIVE: std::os::raw::c_int = 2;
const LOCK_UNLOCK: std::os::raw::c_int = 8;

unsafe extern "C" {
    #[link_name = "flock"]
    fn process_flock(
        fd: std::os::raw::c_int,
        operation: std::os::raw::c_int,
    ) -> std::os::raw::c_int;
}

/// The full search path is derived from the exact READY build and extended
/// only with this checkout's generated artifact directory.
pub fn lean_search_path(
    repo_root: &Path,
    environment: &ProofEnvironment,
) -> Result<String, String> {
    let built = environment.ensure_built(repo_root)?;
    let out = Command::new("lake")
        .args(["env", "printenv", "LEAN_PATH"])
        .current_dir(built.join("lean"))
        .output()
        .map_err(|err| format!("failed to run `lake env`: {err}"))?;
    if !out.status.success() {
        return Err(format!(
            "`lake env printenv LEAN_PATH` failed:\n{}",
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    environment.validate_built(&built)?;
    let base = String::from_utf8_lossy(&out.stdout).trim().to_string();
    Ok(format!("{base}:{}", modules_dir(repo_root).display()))
}

/// Check a generated file against an immutable proof build. With `olean_out`,
/// additionally compile it into an importable generated-module artifact.
pub fn run_lean(
    repo_root: &Path,
    environment: &ProofEnvironment,
    lean_file: &Path,
    olean_out: Option<&Path>,
    expected_source: &str,
) -> Result<Vec<LeanMessage>, String> {
    let built = environment.ensure_built(repo_root)?;
    let lean_dir = built.join("lean");
    require_generated_source(lean_file, expected_source, "before Lean checking")?;

    let mut cmd = Command::new("lean");
    cmd.arg("--json")
        .env("LEAN_PATH", lean_search_path(repo_root, environment)?)
        .current_dir(&lean_dir);
    if let Some(olean) = olean_out {
        cmd.arg("--root")
            .arg(modules_dir(repo_root))
            .arg("-o")
            .arg(olean);
    }
    let output = cmd
        .arg(lean_file)
        .output()
        .map_err(|err| format!("failed to run `lean`: {err}"))?;
    environment.validate_built(&built)?;
    require_generated_source(lean_file, expected_source, "while Lean was checking")?;

    let stdout = String::from_utf8_lossy(&output.stdout);
    let mut messages = Vec::new();
    for line in stdout.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let Ok(v) = serde_json::from_str::<serde_json::Value>(line) else {
            continue; // non-JSON chatter
        };
        let severity = v["severity"].as_str().unwrap_or("error").to_string();
        let msg_line = v["pos"]["line"].as_u64().unwrap_or(0) as usize;
        let data = match &v["data"] {
            serde_json::Value::String(s) => s.clone(),
            other => other.to_string(),
        };
        messages.push(LeanMessage {
            severity,
            line: msg_line,
            data,
        });
    }

    // A crash with no parseable messages should still surface.
    if !output.status.success() && messages.iter().all(|m| m.severity != "error") {
        return Err(format!(
            "lean exited with {} but produced no error messages:\n{}\n{}",
            output.status,
            stdout,
            String::from_utf8_lossy(&output.stderr),
        ));
    }

    Ok(messages)
}

fn require_generated_source(path: &Path, expected: &str, phase: &str) -> Result<(), String> {
    let actual = std::fs::read_to_string(path).map_err(|error| {
        format!(
            "cannot read generated Lean file {}: {error}",
            path.display()
        )
    })?;
    if actual == expected {
        Ok(())
    } else {
        Err(format!(
            "generated Lean file {} changed {phase}; retry the check",
            path.display()
        ))
    }
}

/// Map lean error messages back to .sable diagnostics.
pub fn diagnose(
    emitted: &Emitted,
    vc: &VcResult,
    messages: &[LeanMessage],
    mods: &crate::modules::ModuleSet,
) -> Vec<Diagnostic> {
    let mut diags = Vec::new();
    for msg in messages {
        if msg.severity != "error" {
            continue;
        }
        let entry = emitted
            .map
            .iter()
            .find(|en| en.first_line <= msg.line && msg.line <= en.last_line);
        match entry.map(|en| &en.target) {
            Some(MapTarget::Clause { span, desc }) => diags.push(Diagnostic {
                name: "proof.clause_syntax".into(),
                title: format!("{desc} fails to elaborate"),
                span: *span,
                label: "this clause is not well-formed proof language".into(),
                notes: vec![("lean".into(), msg.data.clone())],
            }),
            Some(MapTarget::Discharged { name, span, goal }) => diags.push(Diagnostic {
                name: "proof.discharge_failed".into(),
                title: format!("discharge of `{name}` does not prove it"),
                span: *span,
                label: "this tactic script fails".into(),
                notes: vec![
                    ("goal".into(), goal.clone()),
                    ("lean".into(), msg.data.clone()),
                ],
            }),
            Some(MapTarget::Obligation(i)) => {
                let ob: &Obligation = &vc.obligations[*i];
                let mut notes = vec![("goal".into(), ob.goal.clone())];
                if !ob.context.is_empty() {
                    // Each entry carries the line its fact came from, so
                    // the provenance of every hypothesis is traceable —
                    // cross-module facts name their file.
                    let ob_file = mods.locate(ob.span.start).0.to_string();
                    let rendered: Vec<String> = ob
                        .context
                        .iter()
                        .map(|(text, span)| {
                            if span.start == 0 && span.end == 0 {
                                text.clone()
                            } else {
                                let (file, line, _) = mods.locate(span.start);
                                if file == ob_file {
                                    format!("{text}   (line {line})")
                                } else {
                                    let short = file.rsplit('/').next().unwrap_or(file);
                                    format!("{text}   ({short}:{line})")
                                }
                            }
                        })
                        .collect();
                    notes.push(("context".into(), rendered.join("\n")));
                }
                notes.push((
                    "automation".into(),
                    "`sable_auto` could not discharge this obligation \
                     (prove it with a `discharge <obligation> by <tactics>` block)"
                        .into(),
                ));
                notes.push(("lean".into(), msg.data.clone()));
                diags.push(Diagnostic {
                    name: ob.name.clone(),
                    title: format!("unproved obligation `{}`", ob.name),
                    span: ob.span,
                    label: ob.kind_desc.clone(),
                    notes,
                });
            }
            None => diags.push(Diagnostic {
                name: "internal.unmapped_lean_error".into(),
                span: Span::new(0, 0),
                title: "internal error: Lean reported an error outside any obligation".into(),
                label: "this is a bug in the Sable compiler, not in your program".into(),
                notes: vec![("lean".into(), format!("line {}: {}", msg.line, msg.data))],
            }),
        }
    }
    diags
}

/// Map the automation-budget warnings (`sable_grind`'s expensive-success
/// diagnostics) back to obligations. Non-fatal: returned separately from
/// `diagnose` so callers report them without failing the check. A
/// `grind?` "Try this:" suggestion at the same position becomes a
/// ready-to-paste `discharge` note.
pub fn diagnose_warnings(
    emitted: &Emitted,
    vc: &VcResult,
    messages: &[LeanMessage],
) -> Vec<Diagnostic> {
    let mut diags = Vec::new();
    for msg in messages {
        if msg.severity != "warning" || !msg.data.contains("expensive automation") {
            continue;
        }
        let entry = emitted
            .map
            .iter()
            .find(|en| en.first_line <= msg.line && msg.line <= en.last_line);
        let suggestion = messages.iter().find(|m| {
            m.severity == "information"
                && m.data.contains("Try th")
                && entry.is_some_and(|en| en.first_line <= m.line && m.line <= en.last_line)
        });
        let mut notes = vec![("automation".into(), msg.data.clone())];
        if let Some(sug) = suggestion {
            // "Try this:"/"Try these:" list alternatives; the first is
            // grind's own minimization of the successful proof.
            let tactic = sug
                .data
                .lines()
                .nth(1)
                .map(|l| l.trim().trim_start_matches("[apply]").trim().to_string())
                .unwrap_or_default();
            notes.push((
                "suggested".into(),
                format!("discharge <obligation> by {tactic}"),
            ));
        }
        match entry.map(|en| &en.target) {
            Some(MapTarget::Obligation(i)) => {
                let ob: &Obligation = &vc.obligations[*i];
                if let Some((_, sug)) = notes.iter_mut().find(|(k, _)| k == "suggested") {
                    *sug = sug.replace("<obligation>", &ob.name);
                }
                diags.push(Diagnostic {
                    name: ob.name.clone(),
                    title: format!("obligation `{}` leans on expensive automation", ob.name),
                    span: ob.span,
                    label: ob.kind_desc.clone(),
                    notes,
                });
            }
            Some(MapTarget::Discharged { name, span, .. }) => diags.push(Diagnostic {
                name: name.clone(),
                title: format!("discharge of `{name}` leans on expensive automation"),
                span: *span,
                label: "this tactic script reaches the budgeted grind".into(),
                notes,
            }),
            _ => {}
        }
    }
    diags
}

/// Deduplicate: one obligation can produce several lean messages.
pub fn dedup_by_name(diags: Vec<Diagnostic>) -> Vec<Diagnostic> {
    let mut seen = std::collections::HashSet::new();
    diags
        .into_iter()
        .filter(|d| seen.insert((d.name.clone(), d.span.start)))
        .collect()
}
