//! Proof-timing protocol v2.
//!
//! This ignored test records end-to-end verification wall time for the closed
//! positive corpus. It is release instrumentation, not a deterministic gate.
//! The runner validates the declared cache state, immutable proof environment,
//! Git/source identity, batch-only checker mode, and paired cold/warm lineage
//! before it will label a result `baseline`.
//!
//! See `tools/proof_timing/README.md` for the exact preparation and commands.

use sable::{Options, verify_file_batch_structured};
use serde_json::{Map, Value, json};
use std::collections::BTreeSet;
use std::ffi::OsStr;
use std::fs::{self, OpenOptions};
use std::io::Write;
#[cfg(unix)]
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

const SCHEMA: &str = "sable-proof-timing-v2";
const COMPILED_CARGO_PROFILE: &str = env!("SABLE_COMPILED_CARGO_PROFILE");
const COMPILED_CARGO_PROFILE_FAMILY: &str = env!("SABLE_COMPILED_CARGO_PROFILE_FAMILY");
const COMPILED_GIT_REVISION: &str = env!("SABLE_COMPILED_GIT_REVISION");
const COMPILED_GIT_DIRTY: &str = env!("SABLE_COMPILED_GIT_DIRTY");
const COMPILED_GIT_STATUS_FINGERPRINT: &str = env!("SABLE_COMPILED_GIT_STATUS_FINGERPRINT");
const COMPILED_RUSTC_VERSION: &str = env!("SABLE_COMPILED_RUSTC_VERSION");
const COMPILED_CARGO_VERSION: &str = env!("SABLE_COMPILED_CARGO_VERSION");
const COMPILED_PROTOCOL_SOURCE: &[u8] = include_bytes!("proof_timing.rs");
const EXPECTED_MEASURED_SUBJECTS: usize = 126;
const EXPECTED_EXCLUDED_SUBJECTS: usize = 1;
const EXCLUDED_BOUNDARY_SUBJECTS: [(&str, &str, &str); 1] = [(
    "corpus/verifies/defer_assume_demo.sable",
    "escape-hatch demonstration intentionally contains one defer and one assume",
    "da2324ce92ed248af6a0531619c12be570f21c9389e2b2b1df0db25da0d0cf9e",
)];

#[derive(Debug, Clone)]
struct SubjectEntry {
    path: String,
    bytes: u64,
    sha256: String,
    exclusion_reason: Option<&'static str>,
    exclusion_expected_sha256: Option<&'static str>,
}

#[derive(Debug)]
struct SubjectManifest {
    included_paths: Vec<PathBuf>,
    entries: Vec<SubjectEntry>,
    manifest_sha256: String,
}

impl SubjectManifest {
    fn included_count(&self) -> usize {
        self.entries
            .iter()
            .filter(|entry| entry.exclusion_reason.is_none())
            .count()
    }

    fn excluded_count(&self) -> usize {
        self.entries.len() - self.included_count()
    }

    fn to_json(&self) -> Value {
        json!({
            "manifest_sha256": self.manifest_sha256,
            "ordering": "lexicographic repository-relative UTF-8 path",
            "content_framing": "domain + path + measured/excluded tag + exclusion reason + pinned exclusion SHA-256 + content; every component is u64-length-framed",
            "included_count": self.included_count(),
            "excluded_count": self.excluded_count(),
            "entries": self.entries.iter().map(|entry| json!({
                "path": entry.path,
                "bytes": entry.bytes,
                "sha256": entry.sha256,
                "measured": entry.exclusion_reason.is_none(),
                "exclusion_reason": entry.exclusion_reason,
                "exclusion_expected_sha256": entry.exclusion_expected_sha256,
            })).collect::<Vec<_>>(),
        })
    }
}

#[derive(Debug, Clone)]
struct CacheEntry {
    path: String,
    kind: &'static str,
    bytes: Option<u64>,
}

#[derive(Debug, Clone)]
struct CacheDirectoryManifest {
    path: String,
    entries: Vec<CacheEntry>,
    regular_files: usize,
    total_file_bytes: u64,
    manifest_sha256: String,
}

impl CacheDirectoryManifest {
    fn to_json(&self) -> Value {
        json!({
            "path": self.path,
            "manifest_sha256": self.manifest_sha256,
            "entry_count": self.entries.len(),
            "regular_files": self.regular_files,
            "total_file_bytes": self.total_file_bytes,
            "manifest_kind": "metadata-only sorted relative path/type/size; file contents are not read",
            "entries": self.entries.iter().map(|entry| json!({
                "path": entry.path,
                "kind": entry.kind,
                "bytes": entry.bytes,
            })).collect::<Vec<_>>(),
        })
    }
}

#[derive(Debug, Clone)]
struct CacheManifest {
    roots: CacheDirectoryManifest,
    modules: CacheDirectoryManifest,
    manifest_sha256: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ProofBuildFileIdentity {
    path: &'static str,
    bytes: u64,
    modified_unix_ns: u64,
    device: Option<u64>,
    inode: Option<u64>,
    content_sha256: Option<String>,
}

impl ProofBuildFileIdentity {
    fn to_json(&self) -> Value {
        json!({
            "path": self.path,
            "bytes": self.bytes,
            "modified_unix_ns": self.modified_unix_ns,
            "device": self.device,
            "inode": self.inode,
            "content_sha256": self.content_sha256,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ProofBuildIdentity {
    manifest_sha256: String,
    ready: ProofBuildFileIdentity,
    sable_olean: ProofBuildFileIdentity,
}

impl ProofBuildIdentity {
    fn to_json(&self) -> Value {
        json!({
            "manifest_sha256": self.manifest_sha256,
            "manifest_kind": "READY content/size/mtime plus Sable.olean size/mtime; Unix reports also bind device/inode",
            "ready": self.ready.to_json(),
            "sable_olean": self.sable_olean.to_json(),
        })
    }
}

impl CacheManifest {
    fn to_json(&self) -> Value {
        json!({
            "manifest_sha256": self.manifest_sha256,
            "roots": self.roots.to_json(),
            "modules": self.modules.to_json(),
        })
    }
}

#[derive(Debug)]
struct GitState {
    revision: String,
    porcelain: String,
}

impl GitState {
    fn dirty(&self) -> bool {
        !self.porcelain.is_empty()
    }

    fn status_lines(&self) -> Vec<&str> {
        self.porcelain.lines().collect()
    }
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("compiler crate lives below the repository root")
        .canonicalize()
        .expect("repository root is readable")
}

fn relative_utf8(root: &Path, path: &Path) -> Result<String, String> {
    let relative = path.strip_prefix(root).map_err(|error| {
        format!(
            "{} is not below {}: {error}",
            path.display(),
            root.display()
        )
    })?;
    let text = relative
        .to_str()
        .ok_or_else(|| format!("repository path {} is not UTF-8", relative.display()))?;
    Ok(text.replace('\\', "/"))
}

fn subject_manifest(root: &Path) -> Result<SubjectManifest, String> {
    let directory = root.join("corpus/verifies");
    let metadata = fs::symlink_metadata(&directory)
        .map_err(|error| format!("cannot inspect {}: {error}", directory.display()))?;
    if metadata.file_type().is_symlink() || !metadata.is_dir() {
        return Err(format!(
            "proof-timing subject root {} must be a local directory",
            directory.display()
        ));
    }

    let mut candidates = Vec::new();
    for entry in fs::read_dir(&directory)
        .map_err(|error| format!("cannot read {}: {error}", directory.display()))?
    {
        let entry = entry.map_err(|error| {
            format!(
                "cannot read a directory entry in {}: {error}",
                directory.display()
            )
        })?;
        let path = entry.path();
        let metadata = fs::symlink_metadata(&path)
            .map_err(|error| format!("cannot inspect {}: {error}", path.display()))?;
        if metadata.file_type().is_symlink() {
            return Err(format!(
                "proof-timing subject directory contains symlink {}",
                path.display()
            ));
        }
        if path.extension() != Some(OsStr::new("sable")) {
            continue;
        }
        if !metadata.is_file() {
            return Err(format!(
                "proof-timing subject {} is not a regular file",
                path.display()
            ));
        }
        candidates.push((relative_utf8(root, &path)?, path));
    }
    candidates.sort_by(|left, right| left.0.cmp(&right.0));

    let mut exclusions = EXCLUDED_BOUNDARY_SUBJECTS
        .iter()
        .map(|(path, _, _)| *path)
        .collect::<BTreeSet<_>>();
    let mut included_paths = Vec::new();
    let mut entries = Vec::new();
    let mut framed = Vec::new();
    frame(
        &mut framed,
        b"sable-proof-timing-subject-content-manifest-v2",
    );
    for (relative, path) in candidates {
        let content = fs::read(&path)
            .map_err(|error| format!("cannot read subject {}: {error}", path.display()))?;
        let exclusion = EXCLUDED_BOUNDARY_SUBJECTS
            .iter()
            .find(|(excluded, _, _)| *excluded == relative);
        let exclusion_reason = exclusion.map(|(_, reason, _)| *reason);
        let exclusion_expected_sha256 = exclusion.map(|(_, _, sha256)| *sha256);
        let content_sha256 = sha256_hex(&content);
        if let Some(expected) = exclusion_expected_sha256 {
            if content_sha256 != expected {
                return Err(format!(
                    "excluded boundary subject {relative} has SHA-256 {content_sha256}, expected pinned {expected}; review its content and exclusion deliberately"
                ));
            }
        }
        if exclusion_reason.is_some() {
            exclusions.remove(relative.as_str());
        } else {
            included_paths.push(path);
        }
        frame(&mut framed, relative.as_bytes());
        frame(
            &mut framed,
            if exclusion_reason.is_some() {
                b"excluded"
            } else {
                b"measured"
            },
        );
        frame(&mut framed, exclusion_reason.unwrap_or_default().as_bytes());
        frame(
            &mut framed,
            exclusion_expected_sha256.unwrap_or_default().as_bytes(),
        );
        frame(&mut framed, &content);
        entries.push(SubjectEntry {
            path: relative,
            bytes: u64::try_from(content.len())
                .map_err(|_| "one subject is too large to report".to_owned())?,
            sha256: content_sha256,
            exclusion_reason,
            exclusion_expected_sha256,
        });
    }
    if !exclusions.is_empty() {
        return Err(format!(
            "configured proof-timing exclusion(s) are missing: {}",
            exclusions.into_iter().collect::<Vec<_>>().join(", ")
        ));
    }
    let manifest = SubjectManifest {
        included_paths,
        entries,
        manifest_sha256: sha256_hex(&framed),
    };
    if manifest.included_count() != EXPECTED_MEASURED_SUBJECTS
        || manifest.excluded_count() != EXPECTED_EXCLUDED_SUBJECTS
    {
        return Err(format!(
            "proof-timing corpus changed: expected {EXPECTED_MEASURED_SUBJECTS} measured and \
             {EXPECTED_EXCLUDED_SUBJECTS} excluded subject(s), found {} measured and {} excluded; \
             review and update the protocol deliberately",
            manifest.included_count(),
            manifest.excluded_count()
        ));
    }
    Ok(manifest)
}

fn frame(output: &mut Vec<u8>, bytes: &[u8]) {
    let len = u64::try_from(bytes.len()).expect("manifest component length fits u64");
    output.extend_from_slice(&len.to_le_bytes());
    output.extend_from_slice(bytes);
}

fn collect_cache_entries(
    base: &Path,
    directory: &Path,
    entries: &mut Vec<CacheEntry>,
) -> Result<(), String> {
    let children = fs::read_dir(directory).map_err(|error| {
        format!(
            "cannot read cache directory {}: {error}",
            directory.display()
        )
    })?;
    let mut children = children
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| format!("cannot read an entry in {}: {error}", directory.display()))?;
    children.sort_by_key(fs::DirEntry::file_name);
    for child in children {
        let path = child.path();
        let metadata = fs::symlink_metadata(&path)
            .map_err(|error| format!("cannot inspect cache entry {}: {error}", path.display()))?;
        if metadata.file_type().is_symlink() {
            return Err(format!(
                "cache entry {} is a symlink; timing caches must be local",
                path.display()
            ));
        }
        let relative = relative_utf8(base, &path)?;
        if metadata.is_dir() {
            entries.push(CacheEntry {
                path: relative,
                kind: "directory",
                bytes: None,
            });
            collect_cache_entries(base, &path, entries)?;
        } else if metadata.is_file() {
            entries.push(CacheEntry {
                path: relative,
                kind: "file",
                bytes: Some(metadata.len()),
            });
        } else {
            return Err(format!(
                "cache entry {} is neither a regular file nor directory",
                path.display()
            ));
        }
    }
    Ok(())
}

fn cache_directory_manifest(root: &Path, relative: &str) -> Result<CacheDirectoryManifest, String> {
    let directory = root.join(relative);
    let metadata = fs::symlink_metadata(&directory).map_err(|error| {
        format!(
            "cannot inspect cache directory {}: {error}",
            directory.display()
        )
    })?;
    if metadata.file_type().is_symlink() || !metadata.is_dir() {
        return Err(format!(
            "timing cache {} must already exist as a local directory",
            directory.display()
        ));
    }
    let mut entries = Vec::new();
    collect_cache_entries(&directory, &directory, &mut entries)?;
    entries.sort_by(|left, right| left.path.cmp(&right.path));

    let mut framed = Vec::new();
    frame(&mut framed, b"sable-proof-timing-cache-metadata-v2");
    frame(&mut framed, relative.as_bytes());
    for entry in &entries {
        frame(&mut framed, entry.path.as_bytes());
        frame(&mut framed, entry.kind.as_bytes());
        frame(&mut framed, &entry.bytes.unwrap_or(u64::MAX).to_le_bytes());
    }
    let regular_files = entries.iter().filter(|entry| entry.kind == "file").count();
    let total_file_bytes = entries
        .iter()
        .filter_map(|entry| entry.bytes)
        .try_fold(0u64, |total, bytes| total.checked_add(bytes))
        .ok_or_else(|| format!("cache byte total overflows u64 in {}", directory.display()))?;
    Ok(CacheDirectoryManifest {
        path: relative.to_owned(),
        entries,
        regular_files,
        total_file_bytes,
        manifest_sha256: sha256_hex(&framed),
    })
}

fn cache_manifest(root: &Path) -> Result<CacheManifest, String> {
    let roots = cache_directory_manifest(root, ".sable-out/roots")?;
    let modules = cache_directory_manifest(root, ".sable-out/modules")?;
    let mut framed = Vec::new();
    frame(&mut framed, b"sable-proof-timing-cache-pair-v2");
    frame(&mut framed, roots.manifest_sha256.as_bytes());
    frame(&mut framed, modules.manifest_sha256.as_bytes());
    Ok(CacheManifest {
        manifest_sha256: sha256_hex(&framed),
        roots,
        modules,
    })
}

fn command_output_in(
    directory: &Path,
    program: &str,
    arguments: &[&str],
    allow_empty: bool,
) -> Result<String, String> {
    let output = Command::new(program)
        .args(arguments)
        .current_dir(directory)
        .output()
        .map_err(|error| {
            format!(
                "cannot run `{program} {}` in {}: {error}",
                arguments.join(" "),
                directory.display()
            )
        })?;
    if !output.status.success() {
        return Err(format!(
            "`{program} {}` failed in {} (status {}):\n{}{}",
            arguments.join(" "),
            directory.display(),
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    let stdout = String::from_utf8(output.stdout)
        .map_err(|_| format!("`{program}` wrote non-UTF-8 standard output"))?;
    let stderr = String::from_utf8(output.stderr)
        .map_err(|_| format!("`{program}` wrote non-UTF-8 standard error"))?;
    let result = if stdout.trim().is_empty() {
        stderr.trim().to_owned()
    } else {
        stdout.trim().to_owned()
    };
    if result.is_empty() && !allow_empty {
        Err(format!(
            "`{program} {}` produced no output",
            arguments.join(" ")
        ))
    } else {
        Ok(result)
    }
}

fn git_state(root: &Path) -> Result<GitState, String> {
    let revision = command_output_in(root, "git", &["rev-parse", "--verify", "HEAD"], false)?;
    if revision.len() < 40 || !revision.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err(format!("git returned invalid full revision `{revision}`"));
    }
    let output = Command::new("git")
        .args(["status", "--porcelain=v1", "--untracked-files=all"])
        .current_dir(root)
        .output()
        .map_err(|error| format!("cannot inspect Git status in {}: {error}", root.display()))?;
    if !output.status.success() {
        return Err(format!(
            "`git status --porcelain=v1 --untracked-files=all` failed in {} (status {}):\n{}{}",
            root.display(),
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    let stderr = String::from_utf8(output.stderr)
        .map_err(|_| "`git status` wrote non-UTF-8 standard error".to_owned())?;
    if !stderr.trim().is_empty() {
        return Err(format!(
            "`git status` produced unexpected standard error: {}",
            stderr.trim()
        ));
    }
    let porcelain = String::from_utf8(output.stdout)
        .map_err(|_| "`git status` wrote non-UTF-8 standard output".to_owned())?
        .trim_end_matches(|character| matches!(character, '\r' | '\n'))
        .to_owned();
    Ok(GitState {
        revision,
        porcelain,
    })
}

fn require_environment(name: &str, expected: &str) {
    assert_eq!(
        std::env::var(name).as_deref(),
        Ok(expected),
        "proof timing requires {name}={expected}"
    );
}

fn executable_cargo_profile(path: &Path) -> Result<&str, String> {
    let deps = path
        .parent()
        .ok_or_else(|| format!("test executable {} has no parent", path.display()))?;
    if deps.file_name() != Some(OsStr::new("deps")) {
        return Err(format!(
            "test executable {} is not in Cargo's `deps` directory",
            path.display()
        ));
    }
    deps.parent()
        .and_then(Path::file_name)
        .and_then(OsStr::to_str)
        .ok_or_else(|| {
            format!(
                "test executable {} has no UTF-8 Cargo profile directory",
                path.display()
            )
        })
}

fn compiled_git_dirty() -> Result<Option<bool>, String> {
    match COMPILED_GIT_DIRTY {
        "false" => Ok(Some(false)),
        "true" => Ok(Some(true)),
        "unknown" => Ok(None),
        value => Err(format!("invalid compile-time Git dirty marker `{value}`")),
    }
}

fn compiled_source_provenance(
    compiled_git_dirty: Option<bool>,
    compiled_protocol_source_sha256: &str,
) -> Value {
    json!({
        "git_revision": COMPILED_GIT_REVISION,
        "git_dirty": compiled_git_dirty,
        "git_status_fingerprint": COMPILED_GIT_STATUS_FINGERPRINT,
        "protocol_source_sha256": compiled_protocol_source_sha256,
        "rustc_short": COMPILED_RUSTC_VERSION,
        "cargo_short": COMPILED_CARGO_VERSION,
    })
}

fn optional_utf8_environment(name: &str) -> Result<Option<String>, String> {
    match std::env::var(name) {
        Ok(value) => Ok(Some(value)),
        Err(std::env::VarError::NotPresent) => Ok(None),
        Err(std::env::VarError::NotUnicode(_)) => {
            Err(format!("environment variable {name} is not UTF-8"))
        }
    }
}

fn relevant_environment() -> Result<Value, String> {
    let mut values = Map::new();
    for name in [
        "CARGO_INCREMENTAL",
        "CARGO_BUILD_JOBS",
        "CARGO_ENCODED_RUSTFLAGS",
        "CARGO_PROFILE_RELEASE_CODEGEN_UNITS",
        "CARGO_PROFILE_RELEASE_DEBUG",
        "CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS",
        "CARGO_PROFILE_RELEASE_INCREMENTAL",
        "CARGO_PROFILE_RELEASE_LTO",
        "CARGO_PROFILE_RELEASE_OPT_LEVEL",
        "CARGO_PROFILE_RELEASE_PANIC",
        "ELAN_TOOLCHAIN",
        "LEAN_GITHASH",
        "LEAN_IMPORT_WORKERS",
        "LEAN_NUM_THREADS",
        "LEAN_PATH",
        "LEAN_SRC_PATH",
        "LEAN_SYSROOT",
        "RUSTFLAGS",
        "SABLE_GRIND_HEARTBEATS",
        "SABLE_TEST_JOBS",
    ] {
        values.insert(
            name.to_owned(),
            optional_utf8_environment(name)?
                .map(Value::String)
                .unwrap_or(Value::Null),
        );
    }
    Ok(Value::Object(values))
}

fn require_no_daemon(root: &Path, stage: &str) -> Result<(), String> {
    let socket = root.join(".sable-out/daemon.sock");
    match fs::symlink_metadata(&socket) {
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(format!(
            "cannot inspect daemon socket {} {stage}: {error}",
            socket.display()
        )),
        Ok(_) => Err(format!(
            "proof timing requires no daemon socket, but {} exists {stage}",
            socket.display()
        )),
    }
}

fn proof_environment_built_dir(root: &Path, id: &str) -> PathBuf {
    root.join(".sable-out")
        .join("proof-envs")
        .join(id.replace(':', "_"))
        .join("built")
}

#[cfg(unix)]
fn metadata_device_inode(metadata: &fs::Metadata) -> (Option<u64>, Option<u64>) {
    (Some(metadata.dev()), Some(metadata.ino()))
}

#[cfg(not(unix))]
fn metadata_device_inode(_: &fs::Metadata) -> (Option<u64>, Option<u64>) {
    (None, None)
}

fn proof_build_file_identity(
    path: &Path,
    relative: &'static str,
    hash_content: bool,
) -> Result<ProofBuildFileIdentity, String> {
    let metadata = fs::symlink_metadata(path).map_err(|error| {
        format!(
            "cannot inspect proof-build file {}: {error}",
            path.display()
        )
    })?;
    if metadata.file_type().is_symlink() || !metadata.is_file() {
        return Err(format!(
            "proof-build identity path {} is not a regular file",
            path.display()
        ));
    }
    let modified_unix_ns = duration_ns(
        metadata
            .modified()
            .map_err(|error| format!("cannot read mtime for {}: {error}", path.display()))?
            .duration_since(UNIX_EPOCH)
            .map_err(|error| {
                format!("mtime for {} predates Unix epoch: {error}", path.display())
            })?,
    );
    let (device, inode) = metadata_device_inode(&metadata);
    let content_sha256 = if hash_content {
        Some(sha256_hex(&fs::read(path).map_err(|error| {
            format!(
                "cannot read proof-build identity file {}: {error}",
                path.display()
            )
        })?))
    } else {
        None
    };
    Ok(ProofBuildFileIdentity {
        path: relative,
        bytes: metadata.len(),
        modified_unix_ns,
        device,
        inode,
        content_sha256,
    })
}

fn proof_build_identity(root: &Path, id: &str) -> Result<ProofBuildIdentity, String> {
    let built = proof_environment_built_dir(root, id);
    let ready = proof_build_file_identity(&built.join("READY"), "READY", true)?;
    let sable_olean = proof_build_file_identity(
        &built.join("lean/.lake/build/lib/lean/Sable.olean"),
        "lean/.lake/build/lib/lean/Sable.olean",
        false,
    )?;
    let mut framed = Vec::new();
    frame(&mut framed, b"sable-proof-timing-proof-build-identity-v2");
    for entry in [&ready, &sable_olean] {
        frame(&mut framed, entry.path.as_bytes());
        frame(&mut framed, &entry.bytes.to_le_bytes());
        frame(&mut framed, &entry.modified_unix_ns.to_le_bytes());
        for value in [entry.device, entry.inode] {
            frame(
                &mut framed,
                if value.is_some() {
                    &b"present"[..]
                } else {
                    &b"absent"[..]
                },
            );
            frame(&mut framed, &value.unwrap_or_default().to_le_bytes());
        }
        frame(
            &mut framed,
            entry
                .content_sha256
                .as_deref()
                .unwrap_or_default()
                .as_bytes(),
        );
    }
    Ok(ProofBuildIdentity {
        manifest_sha256: sha256_hex(&framed),
        ready,
        sable_olean,
    })
}

fn validate_ready_proof_environment(root: &Path) -> Result<sable::lean::ProofEnvironment, String> {
    let live = sable::lean::ProofEnvironment::capture(root)?;
    let environment = sable::lean::ProofEnvironment::load_published(root, live.id())?;
    let built = proof_environment_built_dir(root, environment.id());
    let ready = built.join("READY");
    match fs::symlink_metadata(&ready) {
        Ok(metadata) if !metadata.file_type().is_symlink() && metadata.is_file() => {}
        Ok(_) => {
            return Err(format!(
                "proof environment readiness marker {} is not a regular file",
                ready.display()
            ));
        }
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            return Err(format!(
                "proof environment {} is not prebuilt; prepare it before the timing run",
                environment.id()
            ));
        }
        Err(error) => {
            return Err(format!(
                "cannot inspect proof environment readiness {}: {error}",
                ready.display()
            ));
        }
    }
    environment.validate_built(&built)?;
    Ok(environment)
}

fn output_path(root: &Path) -> Result<PathBuf, String> {
    let raw = optional_utf8_environment("SABLE_PROOF_TIMING_OUT")?.ok_or_else(|| {
        "set SABLE_PROOF_TIMING_OUT to a new absolute path outside the checkout".to_owned()
    })?;
    let raw = PathBuf::from(raw);
    if !raw.is_absolute() {
        return Err(format!(
            "SABLE_PROOF_TIMING_OUT must be absolute, got {}",
            raw.display()
        ));
    }
    let file_name = raw
        .file_name()
        .ok_or_else(|| format!("output path {} has no file name", raw.display()))?;
    let parent = raw
        .parent()
        .ok_or_else(|| format!("output path {} has no parent", raw.display()))?;
    fs::create_dir_all(parent).map_err(|error| {
        format!(
            "cannot create output directory {}: {error}",
            parent.display()
        )
    })?;
    let parent = parent.canonicalize().map_err(|error| {
        format!(
            "cannot resolve output directory {}: {error}",
            parent.display()
        )
    })?;
    let normalized = parent.join(file_name);
    if normalized.starts_with(root) {
        return Err(format!(
            "proof-timing reports must be written outside the checkout, got {}",
            normalized.display()
        ));
    }
    match fs::symlink_metadata(&normalized) {
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(normalized),
        Err(error) => Err(format!(
            "cannot inspect proof-timing output {}: {error}",
            normalized.display()
        )),
        Ok(_) => Err(format!(
            "proof-timing output {} already exists; reports are never overwritten",
            normalized.display()
        )),
    }
}

fn machine_provenance(root: &Path, label: &str) -> Result<Value, String> {
    let hostname = command_output_in(root, "hostname", &[], false)?;
    let kernel = command_output_in(root, "uname", &["-srv"], false)?;
    let (cpu_model, cpu_model_source) = if std::env::consts::OS == "macos" {
        match command_output_in(root, "sysctl", &["-n", "machdep.cpu.brand_string"], false) {
            Ok(model) => (model, "sysctl machdep.cpu.brand_string"),
            Err(_) => (std::env::consts::ARCH.to_owned(), "architecture fallback"),
        }
    } else if std::env::consts::OS == "linux" {
        match fs::read_to_string("/proc/cpuinfo") {
            Ok(cpuinfo) => cpuinfo
                .lines()
                .find_map(|line| line.strip_prefix("model name\t: "))
                .map_or_else(
                    || (std::env::consts::ARCH.to_owned(), "architecture fallback"),
                    |model| (model.to_owned(), "/proc/cpuinfo model name"),
                ),
            Err(_) => (std::env::consts::ARCH.to_owned(), "architecture fallback"),
        }
    } else {
        (std::env::consts::ARCH.to_owned(), "architecture fallback")
    };
    Ok(json!({
        "label": label,
        "hostname": hostname,
        "os": std::env::consts::OS,
        "kernel": kernel,
        "architecture": std::env::consts::ARCH,
        "cpu_model": cpu_model,
        "cpu_model_source": cpu_model_source,
        "logical_cpus": std::thread::available_parallelism()
            .map(|parallelism| parallelism.get())
            .unwrap_or(1),
    }))
}

fn toolchain_provenance(root: &Path) -> Result<Value, String> {
    Ok(json!({
        "rustc_short": command_output_in(root, "rustc", &["--version"], false)?,
        "rustc": command_output_in(root, "rustc", &["--version", "--verbose"], false)?,
        "cargo_short": command_output_in(root, "cargo", &["--version"], false)?,
        "cargo": command_output_in(root, "cargo", &["--version", "--verbose"], false)?,
        "lake": command_output_in(&root.join("lean"), "lake", &["--version"], false)?,
        "lean": command_output_in(
            &root.join("lean"),
            "lake",
            &["env", "lean", "--version"],
            false,
        )?,
    }))
}

fn required_json_str<'a>(value: &'a Value, pointer: &str) -> Result<&'a str, String> {
    value
        .pointer(pointer)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("cold report lacks string field {pointer}"))
}

#[allow(clippy::too_many_arguments)]
fn validate_cold_parent(
    path: &Path,
    evidence_tier: &str,
    revision: &str,
    subject_manifest_sha256: &str,
    cache_manifest_sha256: &str,
    proof_environment_id: &str,
    proof_build_identity_sha256: &str,
    executable_sha256: &str,
    cargo_lock_sha256: &str,
    protocol_source_sha256: &str,
    machine: &Value,
    toolchain: &Value,
    environment: &Value,
    invocation: &Value,
    compiled_source: &Value,
    profile: &str,
) -> Result<String, String> {
    let bytes = fs::read(path)
        .map_err(|error| format!("cannot read cold parent report {}: {error}", path.display()))?;
    let report: Value = serde_json::from_slice(&bytes).map_err(|error| {
        format!(
            "cannot parse cold parent report {}: {error}",
            path.display()
        )
    })?;
    let mut mismatches = Vec::new();
    let expected_strings = [
        ("/schema", SCHEMA),
        ("/status", "ok"),
        ("/evidence/tier", evidence_tier),
        ("/protocol/cache_mode", "cold-roots"),
        ("/protocol/profile", profile),
        ("/provenance/start_revision", revision),
        ("/provenance/end_revision", revision),
        (
            "/provenance/subject_manifest_start_sha256",
            subject_manifest_sha256,
        ),
        (
            "/provenance/subject_manifest_end_sha256",
            subject_manifest_sha256,
        ),
        (
            "/provenance/proof_environment_id_start",
            proof_environment_id,
        ),
        ("/provenance/proof_environment_id_end", proof_environment_id),
        (
            "/provenance/proof_build_identity_start/manifest_sha256",
            proof_build_identity_sha256,
        ),
        (
            "/provenance/proof_build_identity_end/manifest_sha256",
            proof_build_identity_sha256,
        ),
        ("/provenance/test_executable_sha256", executable_sha256),
        ("/provenance/cargo_lock_sha256", cargo_lock_sha256),
        ("/provenance/protocol_source_sha256", protocol_source_sha256),
        ("/cache/end/manifest_sha256", cache_manifest_sha256),
    ];
    for (pointer, expected) in expected_strings {
        match required_json_str(&report, pointer) {
            Ok(actual) if actual == expected => {}
            Ok(actual) => {
                mismatches.push(format!("{pointer} is `{actual}`, expected `{expected}`"))
            }
            Err(error) => mismatches.push(error),
        }
    }
    for (pointer, expected) in [
        ("/machine", machine),
        ("/toolchain", toolchain),
        ("/environment", environment),
        ("/invocation", invocation),
        ("/provenance/compiled_source", compiled_source),
    ] {
        match report.pointer(pointer) {
            Some(actual) if actual == expected => {}
            Some(_) => mismatches.push(format!("{pointer} differs from this run")),
            None => mismatches.push(format!("cold report lacks {pointer}")),
        }
    }
    if mismatches.is_empty() {
        Ok(sha256_hex(&bytes))
    } else {
        Err(format!(
            "warm-artifacts parent {} does not match the required successful cold-report provenance and metadata:\n{}",
            path.display(),
            mismatches.join("\n")
        ))
    }
}

fn percentile(sorted: &[u64], numerator: usize, denominator: usize) -> u64 {
    assert!(!sorted.is_empty());
    assert!(numerator > 0 && numerator <= denominator);
    let rank = (sorted.len() * numerator).div_ceil(denominator);
    sorted[rank.saturating_sub(1)]
}

fn duration_ns(duration: Duration) -> u64 {
    u64::try_from(duration.as_nanos()).expect("proof timing duration fits u64 nanoseconds")
}

fn unix_ns() -> u64 {
    u64::try_from(
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system time is after the Unix epoch")
            .as_nanos(),
    )
    .expect("current Unix timestamp fits u64 nanoseconds")
}

fn write_new_report(path: &Path, report: &Value) -> Result<(), String> {
    let mut bytes = serde_json::to_vec_pretty(report)
        .map_err(|error| format!("proof-timing report is not serializable: {error}"))?;
    bytes.push(b'\n');
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(|error| format!("cannot create report {}: {error}", path.display()))?;
    file.write_all(&bytes)
        .map_err(|error| format!("cannot write report {}: {error}", path.display()))?;
    file.sync_all()
        .map_err(|error| format!("cannot sync report {}: {error}", path.display()))
}

fn sha256_hex(input: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let digest = sha256(input);
    let mut output = String::with_capacity(digest.len() * 2);
    for byte in digest {
        output.push(char::from(HEX[usize::from(byte >> 4)]));
        output.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    output
}

fn sha256(input: &[u8]) -> [u8; 32] {
    const INITIAL: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];
    const ROUND: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];

    let bit_len = u64::try_from(input.len())
        .expect("SHA-256 input length fits u64")
        .checked_mul(8)
        .expect("SHA-256 bit length fits u64");
    let mut message = Vec::with_capacity(input.len().saturating_add(72));
    message.extend_from_slice(input);
    message.push(0x80);
    while message.len() % 64 != 56 {
        message.push(0);
    }
    message.extend_from_slice(&bit_len.to_be_bytes());

    let mut state = INITIAL;
    for block in message.chunks_exact(64) {
        let mut words = [0u32; 64];
        for (index, chunk) in block.chunks_exact(4).enumerate() {
            words[index] = u32::from_be_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]);
        }
        for index in 16..64 {
            let s0 = words[index - 15].rotate_right(7)
                ^ words[index - 15].rotate_right(18)
                ^ (words[index - 15] >> 3);
            let s1 = words[index - 2].rotate_right(17)
                ^ words[index - 2].rotate_right(19)
                ^ (words[index - 2] >> 10);
            words[index] = words[index - 16]
                .wrapping_add(s0)
                .wrapping_add(words[index - 7])
                .wrapping_add(s1);
        }

        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = state;
        for index in 0..64 {
            let big_s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let choice = (e & f) ^ ((!e) & g);
            let temp1 = h
                .wrapping_add(big_s1)
                .wrapping_add(choice)
                .wrapping_add(ROUND[index])
                .wrapping_add(words[index]);
            let big_s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let majority = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = big_s0.wrapping_add(majority);

            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }
        for (slot, value) in state.iter_mut().zip([a, b, c, d, e, f, g, h].into_iter()) {
            *slot = slot.wrapping_add(value);
        }
    }

    let mut digest = [0u8; 32];
    for (chunk, word) in digest.chunks_exact_mut(4).zip(state) {
        chunk.copy_from_slice(&word.to_be_bytes());
    }
    digest
}

#[test]
fn sha256_matches_published_vectors() {
    assert_eq!(
        sha256_hex(b""),
        "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    );
    assert_eq!(
        sha256_hex(b"abc"),
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    );
    assert_eq!(
        sha256_hex(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"),
        "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
    );
}

#[test]
fn executable_profile_uses_the_exact_cargo_output_directory() {
    assert_eq!(
        executable_cargo_profile(Path::new("target/release/deps/proof_timing-deadbeef"))
            .expect("standard Cargo test path has a profile"),
        "release"
    );
    assert_eq!(
        executable_cargo_profile(Path::new(
            "target/release-without-assertions/deps/proof_timing-deadbeef"
        ))
        .expect("custom Cargo test path has a profile"),
        "release-without-assertions"
    );
    assert!(
        executable_cargo_profile(Path::new("bin/proof_timing-deadbeef")).is_err(),
        "a copied executable without Cargo profile provenance fails closed"
    );
}

#[test]
fn compiled_protocol_source_matches_the_checked_out_harness() {
    let on_disk = fs::read(repo_root().join("compiler/tests/proof_timing.rs"))
        .expect("proof-timing source is readable");
    assert_eq!(sha256_hex(COMPILED_PROTOCOL_SOURCE), sha256_hex(&on_disk));
}

#[test]
fn subject_manifest_pins_the_measured_set_and_boundary_exclusion() {
    let manifest = subject_manifest(&repo_root()).expect("subject manifest is valid");
    assert_eq!(manifest.included_count(), EXPECTED_MEASURED_SUBJECTS);
    assert_eq!(manifest.excluded_count(), EXPECTED_EXCLUDED_SUBJECTS);
    assert!(
        manifest
            .entries
            .windows(2)
            .all(|pair| pair[0].path.as_str() < pair[1].path.as_str()),
        "subject entries are strictly lexicographically ordered"
    );
    let excluded = manifest
        .entries
        .iter()
        .filter(|entry| entry.exclusion_reason.is_some())
        .collect::<Vec<_>>();
    assert_eq!(excluded.len(), 1);
    assert_eq!(excluded[0].path, EXCLUDED_BOUNDARY_SUBJECTS[0].0);
    assert_eq!(
        excluded[0].exclusion_reason,
        Some(EXCLUDED_BOUNDARY_SUBJECTS[0].1)
    );
    assert_eq!(
        excluded[0].exclusion_expected_sha256,
        Some(EXCLUDED_BOUNDARY_SUBJECTS[0].2)
    );
    assert_eq!(excluded[0].sha256, EXCLUDED_BOUNDARY_SUBJECTS[0].2);
    assert!(
        manifest
            .entries
            .iter()
            .all(|entry| entry.sha256.len() == 64),
        "every subject entry carries a SHA-256 hex digest"
    );
}

#[test]
#[ignore = "release instrumentation; wall time is not a deterministic PR gate"]
fn record_verifying_corpus_proof_times() {
    require_environment("CARGO_BUILD_JOBS", "1");
    require_environment("CARGO_INCREMENTAL", "0");
    require_environment("LEAN_IMPORT_WORKERS", "1");
    require_environment("LEAN_NUM_THREADS", "0");
    require_environment("SABLE_TEST_JOBS", "1");

    let root = repo_root();
    let cache_mode = std::env::var("SABLE_PROOF_TIMING_CACHE_MODE")
        .expect("set SABLE_PROOF_TIMING_CACHE_MODE to exactly cold-roots or warm-artifacts");
    assert!(
        matches!(cache_mode.as_str(), "cold-roots" | "warm-artifacts"),
        "unknown proof timing cache mode `{cache_mode}`"
    );
    let machine_label = std::env::var("SABLE_PROOF_TIMING_MACHINE")
        .expect("set SABLE_PROOF_TIMING_MACHINE to a stable machine identity");
    assert!(
        !machine_label.is_empty()
            && machine_label
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'_' | b'-')),
        "SABLE_PROOF_TIMING_MACHINE must use only ASCII letters, digits, `.`, `_`, or `-`"
    );
    let custom = match optional_utf8_environment("SABLE_PROOF_TIMING_ALLOW_CUSTOM")
        .expect("custom-mode environment is valid UTF-8")
    {
        None => false,
        Some(value) if value == "1" => true,
        Some(value) => {
            panic!("SABLE_PROOF_TIMING_ALLOW_CUSTOM must be unset or `1`, got `{value}`")
        }
    };
    let profile = COMPILED_CARGO_PROFILE;
    let grind_heartbeats = optional_utf8_environment("SABLE_GRIND_HEARTBEATS")
        .expect("grind-heartbeat environment is valid UTF-8");
    let ambient_lean_overrides = [
        "ELAN_TOOLCHAIN",
        "LEAN_GITHASH",
        "LEAN_PATH",
        "LEAN_SRC_PATH",
        "LEAN_SYSROOT",
    ]
    .map(|name| {
        (
            name,
            optional_utf8_environment(name)
                .unwrap_or_else(|error| panic!("cannot inspect {name}: {error}")),
        )
    });
    let start_git = git_state(&root).expect("cannot capture starting Git state");
    let compiled_git_dirty = compiled_git_dirty().expect("compile-time Git marker is valid");
    let compiled_protocol_source_sha256 = sha256_hex(COMPILED_PROTOCOL_SOURCE);
    let protocol_source_sha256 = sha256_hex(
        &fs::read(root.join("compiler/tests/proof_timing.rs"))
            .expect("proof-timing protocol source is readable"),
    );
    assert_eq!(
        compiled_protocol_source_sha256, protocol_source_sha256,
        "compiled and on-disk proof-timing protocol sources differ; rebuild the timing executable"
    );
    let compiled_source =
        compiled_source_provenance(compiled_git_dirty, &compiled_protocol_source_sha256);
    let mut evidence_reasons = Vec::new();
    let evidence_tier = if custom {
        evidence_reasons.push("explicit SABLE_PROOF_TIMING_ALLOW_CUSTOM=1 opt-in".to_owned());
        if profile != "release" {
            evidence_reasons.push(format!("non-release Cargo profile `{profile}`"));
        }
        if cfg!(debug_assertions) {
            evidence_reasons.push("Rust debug assertions are enabled".to_owned());
        }
        if start_git.dirty() {
            evidence_reasons.push("dirty starting worktree".to_owned());
        }
        if COMPILED_GIT_REVISION != start_git.revision {
            evidence_reasons.push(format!(
                "compiled Git revision `{}` differs from starting revision `{}`",
                COMPILED_GIT_REVISION, start_git.revision
            ));
        }
        if compiled_git_dirty != Some(false) {
            evidence_reasons.push(format!(
                "compile-time Git dirty state is {}",
                COMPILED_GIT_DIRTY
            ));
        }
        if let Some(value) = &grind_heartbeats {
            evidence_reasons.push(format!("custom SABLE_GRIND_HEARTBEATS={value}"));
        }
        for (name, value) in &ambient_lean_overrides {
            if let Some(value) = value {
                evidence_reasons.push(format!("ambient {name}={value}"));
            }
        }
        "smoke_custom"
    } else {
        assert_eq!(
            profile, "release",
            "baseline proof timing requires the exact Cargo `release` profile; set \
             SABLE_PROOF_TIMING_ALLOW_CUSTOM=1 only for a smoke experiment"
        );
        assert!(
            !cfg!(debug_assertions),
            "baseline proof timing requires Rust debug assertions to be disabled; set \
             SABLE_PROOF_TIMING_ALLOW_CUSTOM=1 only for a smoke experiment"
        );
        assert!(
            !start_git.dirty(),
            "baseline proof timing requires a clean starting worktree; set \
             SABLE_PROOF_TIMING_ALLOW_CUSTOM=1 only for a smoke experiment\n{}",
            start_git.porcelain
        );
        assert_eq!(
            COMPILED_GIT_REVISION, start_git.revision,
            "baseline proof timing requires an executable compiled from the exact starting Git revision"
        );
        assert_eq!(
            compiled_git_dirty,
            Some(false),
            "baseline proof timing requires an executable compiled from a clean worktree"
        );
        assert!(
            grind_heartbeats.is_none(),
            "baseline proof timing requires SABLE_GRIND_HEARTBEATS to be unset; set \
             SABLE_PROOF_TIMING_ALLOW_CUSTOM=1 only for a smoke experiment"
        );
        for (name, value) in &ambient_lean_overrides {
            assert!(
                value.is_none(),
                "baseline proof timing requires {name} to be unset; set \
                 SABLE_PROOF_TIMING_ALLOW_CUSTOM=1 only for a smoke experiment"
            );
        }
        "baseline"
    };

    let output_path = output_path(&root).expect("invalid proof-timing output path");
    let start_subjects = subject_manifest(&root).expect("cannot build starting subject manifest");
    let start_proof_environment = validate_ready_proof_environment(&root)
        .expect("proof-timing proof environment is not ready");
    let proof_environment_id = start_proof_environment.id().to_owned();
    let start_proof_build_identity = proof_build_identity(&root, &proof_environment_id)
        .expect("cannot capture starting proof-build identity");
    require_no_daemon(&root, "before the run").expect("daemon preflight failed");
    let start_cache = cache_manifest(&root).expect("cannot inspect starting timing cache");
    match cache_mode.as_str() {
        "cold-roots" => {
            assert!(
                start_cache.roots.entries.is_empty() && start_cache.modules.entries.is_empty(),
                "cold-roots requires empty .sable-out/roots and .sable-out/modules; found {} and {} entries",
                start_cache.roots.entries.len(),
                start_cache.modules.entries.len()
            );
        }
        "warm-artifacts" => {
            assert!(
                start_cache.roots.regular_files > 0 && start_cache.modules.regular_files > 0,
                "warm-artifacts requires nonempty root and module artifact caches"
            );
        }
        _ => unreachable!(),
    }

    let executable = std::env::current_exe().expect("current test executable path is available");
    let executable_profile = executable_cargo_profile(&executable)
        .expect("cannot authenticate the test executable's Cargo profile directory");
    assert_eq!(
        executable_profile, profile,
        "compile-time and executable-path Cargo profile identities differ"
    );
    let executable_display = executable
        .to_str()
        .expect("current test executable path is UTF-8")
        .to_owned();
    let executable_sha256 = sha256_hex(&fs::read(&executable).unwrap_or_else(|error| {
        panic!(
            "cannot read test executable {}: {error}",
            executable.display()
        )
    }));
    let cargo_lock_sha256 = sha256_hex(
        &fs::read(root.join("compiler/Cargo.lock")).expect("compiler/Cargo.lock is readable"),
    );
    let machine =
        machine_provenance(&root, &machine_label).expect("cannot capture machine provenance");
    let toolchain = toolchain_provenance(&root).expect("cannot capture toolchain provenance");
    let runtime_rustc =
        required_json_str(&toolchain, "/rustc_short").expect("runtime rustc version is present");
    let runtime_cargo =
        required_json_str(&toolchain, "/cargo_short").expect("runtime Cargo version is present");
    if evidence_tier == "baseline" {
        assert_eq!(
            COMPILED_RUSTC_VERSION, runtime_rustc,
            "baseline proof timing requires the build-time and measurement-time rustc versions to match"
        );
        assert_eq!(
            COMPILED_CARGO_VERSION, runtime_cargo,
            "baseline proof timing requires the build-time and measurement-time Cargo versions to match"
        );
    } else {
        if COMPILED_RUSTC_VERSION != runtime_rustc {
            evidence_reasons.push(format!(
                "build-time rustc `{}` differs from measurement-time `{runtime_rustc}`",
                COMPILED_RUSTC_VERSION
            ));
        }
        if COMPILED_CARGO_VERSION != runtime_cargo {
            evidence_reasons.push(format!(
                "build-time Cargo `{}` differs from measurement-time `{runtime_cargo}`",
                COMPILED_CARGO_VERSION
            ));
        }
    }
    let environment = relevant_environment().expect("cannot capture timing environment");
    let invocation = json!({
        "arguments": std::env::args().collect::<Vec<_>>(),
        "current_directory": std::env::current_dir()
            .expect("timing process current directory is available")
            .to_str()
            .expect("timing process current directory is UTF-8")
            .to_owned(),
    });

    let mut cold_parent_path = None;
    let mut cold_parent_sha256 = None;
    if cache_mode == "warm-artifacts" {
        let path = optional_utf8_environment("SABLE_PROOF_TIMING_COLD_REPORT")
            .expect("cold-parent environment is valid UTF-8")
            .map(PathBuf::from)
            .expect("warm-artifacts requires SABLE_PROOF_TIMING_COLD_REPORT");
        assert!(
            path.is_absolute(),
            "SABLE_PROOF_TIMING_COLD_REPORT must be an absolute path"
        );
        let canonical = path.canonicalize().unwrap_or_else(|error| {
            panic!("cannot resolve cold report {}: {error}", path.display())
        });
        assert!(
            !canonical.starts_with(&root),
            "cold parent report must be outside the checkout"
        );
        assert_ne!(
            canonical, output_path,
            "warm report must not overwrite its cold parent"
        );
        let digest = validate_cold_parent(
            &canonical,
            evidence_tier,
            &start_git.revision,
            &start_subjects.manifest_sha256,
            &start_cache.manifest_sha256,
            &proof_environment_id,
            &start_proof_build_identity.manifest_sha256,
            &executable_sha256,
            &cargo_lock_sha256,
            &protocol_source_sha256,
            &machine,
            &toolchain,
            &environment,
            &invocation,
            &compiled_source,
            profile,
        )
        .expect("warm-artifacts lineage check failed");
        cold_parent_path = Some(
            canonical
                .to_str()
                .expect("cold parent report path is UTF-8")
                .to_owned(),
        );
        cold_parent_sha256 = Some(digest);
    } else {
        assert!(
            optional_utf8_environment("SABLE_PROOF_TIMING_COLD_REPORT")
                .expect("cold-parent environment is valid UTF-8")
                .is_none(),
            "cold-roots must not set SABLE_PROOF_TIMING_COLD_REPORT"
        );
    }

    let options = Options::default();
    let mut records = Vec::new();
    let mut failures = Vec::new();
    let mut durations = Vec::new();
    let mut verified_subjects = 0u64;
    let mut total_functions = 0u64;
    let mut total_ordinary_obligations = 0u64;
    let mut total_transition_certificates = 0u64;
    let mut total_argument_schedule_certificates = 0u64;
    let mut total_generated_lean_bytes = 0u64;
    let mut total_warnings = 0u64;
    let mut total_deferred = 0u64;
    let mut total_assumed = 0u64;

    let recorded_start_unix_ns = unix_ns();
    let started_all = Instant::now();
    for path in &start_subjects.included_paths {
        let relative = relative_utf8(&root, path).expect("subject remains below repository root");
        let started = Instant::now();
        let (_, result) = verify_file_batch_structured(path, &options);
        let verification_wall_ns = duration_ns(started.elapsed());
        durations.push(verification_wall_ns);
        match result {
            Ok(verified) => {
                verified_subjects += 1;
                let info = verified.info();
                let warnings = info
                    .warnings
                    .iter()
                    .map(|diagnostic| diagnostic.name.clone())
                    .collect::<Vec<_>>();
                let deferred = info.deferred.clone();
                let assumed = info
                    .assumed
                    .iter()
                    .map(|(name, _)| name.clone())
                    .collect::<Vec<_>>();
                if !warnings.is_empty() || !deferred.is_empty() || !assumed.is_empty() {
                    failures.push(format!(
                        "{relative}: {} warning(s), {} deferred, {} assumed",
                        warnings.len(),
                        deferred.len(),
                        assumed.len()
                    ));
                }
                if verified.proof_fingerprint() != proof_environment_id {
                    failures.push(format!(
                        "{relative}: proof environment {} differs from preflight {}",
                        verified.proof_fingerprint(),
                        proof_environment_id
                    ));
                }
                let total_emitted_theorems = info
                    .obligations
                    .checked_add(info.transition_certificates)
                    .and_then(|count| count.checked_add(info.argument_schedule_certificates))
                    .expect("per-subject theorem count fits usize");
                total_functions += u64::try_from(info.functions).expect("function count fits u64");
                total_ordinary_obligations +=
                    u64::try_from(info.obligations).expect("obligation count fits u64");
                total_transition_certificates += u64::try_from(info.transition_certificates)
                    .expect("transition-certificate count fits u64");
                total_argument_schedule_certificates +=
                    u64::try_from(info.argument_schedule_certificates)
                        .expect("argument-schedule-certificate count fits u64");
                total_generated_lean_bytes +=
                    u64::try_from(info.generated_lean_bytes).expect("generated Lean size fits u64");
                total_warnings += u64::try_from(warnings.len()).expect("warning count fits u64");
                total_deferred += u64::try_from(deferred.len()).expect("defer count fits u64");
                total_assumed += u64::try_from(assumed.len()).expect("assume count fits u64");
                records.push(json!({
                    "path": relative,
                    "status": "verified",
                    "verification_wall_ns": verification_wall_ns,
                    "artifact_name": verified.artifact_name(),
                    "proof_environment_id": verified.proof_fingerprint(),
                    "functions": info.functions,
                    "ordinary_obligations": info.obligations,
                    "transition_certificates": info.transition_certificates,
                    "argument_schedule_certificates": info.argument_schedule_certificates,
                    "total_emitted_theorems": total_emitted_theorems,
                    "generated_lean_bytes": info.generated_lean_bytes,
                    "unsafe_regions": info.unsafe_regions,
                    "extern_contracts": info.externs,
                    "machine_profiles": info.machine_profiles,
                    "machine_intrinsics": info.machine_intrinsics,
                    "warnings": warnings,
                    "deferred": deferred,
                    "assumed": assumed,
                }));
            }
            Err(diagnostics) => {
                let names = diagnostics
                    .iter()
                    .map(|diagnostic| diagnostic.name.clone())
                    .collect::<Vec<_>>();
                failures.push(format!("{relative}: {}", names.join(", ")));
                records.push(json!({
                    "path": relative,
                    "status": "failed",
                    "verification_wall_ns": verification_wall_ns,
                    "diagnostics": names,
                }));
            }
        }
    }
    let verification_wall_total_ns = duration_ns(started_all.elapsed());
    let recorded_end_unix_ns = unix_ns();
    durations.sort_unstable();

    let end_subjects = subject_manifest(&root).expect("cannot build ending subject manifest");
    let end_proof_environment =
        validate_ready_proof_environment(&root).expect("ending proof environment is not ready");
    let end_proof_build_identity = proof_build_identity(&root, end_proof_environment.id())
        .expect("cannot capture ending proof-build identity");
    let end_cache = cache_manifest(&root).expect("cannot inspect ending timing cache");
    if let Err(error) = require_no_daemon(&root, "after the run") {
        failures.push(error);
    }
    let end_git = git_state(&root).expect("cannot capture ending Git state");

    if end_git.revision != start_git.revision {
        failures.push(format!(
            "Git revision changed during run: {} -> {}",
            start_git.revision, end_git.revision
        ));
    }
    if evidence_tier == "baseline" && end_git.revision != COMPILED_GIT_REVISION {
        failures.push(format!(
            "baseline ending Git revision {} differs from compiled revision {}",
            end_git.revision, COMPILED_GIT_REVISION
        ));
    }
    if evidence_tier == "baseline" && end_git.dirty() {
        failures.push(format!(
            "baseline worktree became dirty during run:\n{}",
            end_git.porcelain
        ));
    }
    if end_subjects.manifest_sha256 != start_subjects.manifest_sha256 {
        failures.push(format!(
            "subject content manifest changed during run: {} -> {}",
            start_subjects.manifest_sha256, end_subjects.manifest_sha256
        ));
    }
    if end_proof_environment.id() != proof_environment_id {
        failures.push(format!(
            "proof environment changed during run: {} -> {}",
            proof_environment_id,
            end_proof_environment.id()
        ));
    }
    if end_proof_build_identity != start_proof_build_identity {
        failures.push(format!(
            "proof build changed during run: {} -> {}",
            start_proof_build_identity.manifest_sha256, end_proof_build_identity.manifest_sha256
        ));
    }
    match cache_mode.as_str() {
        "cold-roots" => {
            if end_cache.roots.regular_files == 0 || end_cache.modules.regular_files == 0 {
                failures.push(
                    "cold-roots run did not populate both root and module artifact caches".into(),
                );
            }
        }
        "warm-artifacts" => {
            if end_cache.manifest_sha256 != start_cache.manifest_sha256 {
                failures.push(format!(
                    "warm-artifacts cache changed during run: {} -> {}",
                    start_cache.manifest_sha256, end_cache.manifest_sha256
                ));
            }
        }
        _ => unreachable!(),
    }

    let sum_subject_ns = durations
        .iter()
        .copied()
        .try_fold(0u64, |total, duration| total.checked_add(duration))
        .expect("sum of subject wall times fits u64 nanoseconds");
    let status = if failures.is_empty() { "ok" } else { "failed" };
    let reported_tier = if failures.is_empty() {
        evidence_tier
    } else {
        "invalid"
    };
    let report = json!({
        "schema": SCHEMA,
        "status": status,
        "evidence": {
            "tier": reported_tier,
            "attempted_tier": evidence_tier,
            "reasons": evidence_reasons,
            "claim": if !failures.is_empty() {
                "failed run; no baseline or smoke evidence claim"
            } else if evidence_tier == "baseline" {
                "comparable release baseline under protocol v2; wall time is observational, not a gate"
            } else {
                "custom smoke only; not a comparable release baseline"
            },
        },
        "recorded": {
            "started_unix_ns": recorded_start_unix_ns,
            "ended_unix_ns": recorded_end_unix_ns,
        },
        "provenance": {
            "start_revision": start_git.revision,
            "end_revision": end_git.revision,
            "start_git_dirty": start_git.dirty(),
            "end_git_dirty": end_git.dirty(),
            "start_git_status": start_git.status_lines(),
            "end_git_status": end_git.status_lines(),
            "subject_manifest_start_sha256": start_subjects.manifest_sha256,
            "subject_manifest_end_sha256": end_subjects.manifest_sha256,
            "proof_environment_id_start": proof_environment_id,
            "proof_environment_id_end": end_proof_environment.id(),
            "proof_build_identity_start": start_proof_build_identity.to_json(),
            "proof_build_identity_end": end_proof_build_identity.to_json(),
            "test_executable": executable_display,
            "test_executable_sha256": executable_sha256,
            "cargo_lock_sha256": cargo_lock_sha256,
            "protocol_source_sha256": protocol_source_sha256,
            "compiled_protocol_source_sha256": compiled_protocol_source_sha256,
            "compiled_source": compiled_source,
        },
        "machine": machine,
        "toolchain": toolchain,
        "environment": environment,
        "invocation": invocation,
        "protocol": {
            "version": 2,
            "profile": profile,
            "profile_family": COMPILED_CARGO_PROFILE_FAMILY,
            "profile_identity": "exact Cargo output profile directory captured from OUT_DIR at compile time and cross-checked against the running test executable path",
            "debug_assertions": cfg!(debug_assertions),
            "cache_mode": cache_mode,
            "checker": "batch Lean only (daemon bypassed; serialized root and missing-import processes)",
            "metric": "end-to-end verification API wall time, including front end, VC generation, Lean emission/check, and artifact publication",
            "clock": "std::time::Instant monotonic elapsed nanoseconds",
            "subject_order": "lexicographic repository-relative path",
            "subject_concurrency": 1,
            "subject_serialization": "one lexicographic Rust loop; no subject worker pool",
            "external_lean_process_concurrency": 1,
            "lean_task_manager": "disabled by required LEAN_NUM_THREADS=0 inherited by direct run_lean",
            "lean_import_workers": "exactly one by required LEAN_IMPORT_WORKERS=1 inherited by direct run_lean",
            "orchestration_conventions": "SABLE_TEST_JOBS=1 pins the supported outer verification pool; the serial timing loop does not consume it",
            "expected_measured_subjects": EXPECTED_MEASURED_SUBJECTS,
            "expected_excluded_subjects": EXPECTED_EXCLUDED_SUBJECTS,
            "escape_hatch_policy": "every measured subject must have zero warnings, defers, and assumes",
            "cache_manifest_policy": "metadata-only; avoids deliberately paging artifact contents into memory before measurement",
            "warm_lineage_limit": "authenticates selected cold-report bytes and equivalent path/type/size cache state, not temporal adjacency, unique physical lineage, or cache-content identity beyond normal content-addressed artifact validation",
        },
        "cache": {
            "cold_parent_report": cold_parent_path,
            "cold_parent_report_sha256": cold_parent_sha256,
            "start": start_cache.to_json(),
            "end": end_cache.to_json(),
        },
        "subject_manifest": start_subjects.to_json(),
        "summary": {
            "subjects": records.len(),
            "verified_subjects": verified_subjects,
            "failed_subjects": records.len() as u64 - verified_subjects,
            "failure_records": failures.len(),
            "verification_wall_total_ns": verification_wall_total_ns,
            "verification_wall_subject_sum_ns": sum_subject_ns,
            "verification_wall_subject_median_ns": percentile(&durations, 50, 100),
            "verification_wall_subject_p95_ns": percentile(&durations, 95, 100),
            "verification_wall_subject_max_ns": durations.last().copied().unwrap_or(0),
            "functions": total_functions,
            "ordinary_obligations": total_ordinary_obligations,
            "transition_certificates": total_transition_certificates,
            "argument_schedule_certificates": total_argument_schedule_certificates,
            "total_emitted_theorems": total_ordinary_obligations
                + total_transition_certificates
                + total_argument_schedule_certificates,
            "generated_lean_bytes": total_generated_lean_bytes,
            "warnings": total_warnings,
            "deferred": total_deferred,
            "assumed": total_assumed,
        },
        "failures": failures,
        "subjects": records,
    });
    write_new_report(&output_path, &report).expect("cannot write proof-timing report");
    println!(
        "proof timing v2: {} subjects, {} ns verification wall, median {} ns, p95 {} ns, max {} ns -> {}",
        durations.len(),
        verification_wall_total_ns,
        percentile(&durations, 50, 100),
        percentile(&durations, 95, 100),
        durations.last().copied().unwrap_or(0),
        output_path.display()
    );
    assert!(
        failures.is_empty(),
        "proof-timing report written to {}:\n{}",
        output_path.display(),
        failures.join("\n")
    );
}
