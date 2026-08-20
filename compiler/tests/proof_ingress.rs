use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

use sable::{Options, ProofAssurance, check_file_structured};

const UNAUDITED_PROOF_STATUS: &str = "status: Lean accepted; proof dependencies unaudited";

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("compiler crate lives under the repository root")
        .to_path_buf()
}

struct TempSource(PathBuf);

impl Drop for TempSource {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

struct TempModuleTree(PathBuf);

impl Drop for TempModuleTree {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn temp_source(label: &str, source: &str) -> TempSource {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("test clock follows the Unix epoch")
        .as_nanos();
    let path = std::env::temp_dir().join(format!(
        "sable-proof-ingress-{label}-{}-{nanos}-{}.sable",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed),
    ));
    fs::write(&path, source).expect("write proof-ingress witness");
    TempSource(path)
}

fn temp_module_tree(label: &str, files: &[(&str, &str)]) -> TempModuleTree {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("test clock follows the Unix epoch")
        .as_nanos();
    let directory = std::env::temp_dir().join(format!(
        "sable-proof-ingress-{label}-{}-{nanos}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed),
    ));
    fs::create_dir(&directory).expect("create proof-ingress module directory");
    for (name, source) in files {
        fs::write(directory.join(name), source).expect("write proof-ingress module witness");
    }
    TempModuleTree(directory)
}

fn assert_no_daemon(repo: &PathBuf) {
    let daemon_socket = repo.join(".sable-out/daemon.sock");
    match fs::symlink_metadata(&daemon_socket) {
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => panic!("cannot inspect {}: {error}", daemon_socket.display()),
        Ok(_) => panic!(
            "{} exists; proof-ingress tests require bounded batch Lean",
            daemon_socket.display()
        ),
    }
}

fn check_path(path: &PathBuf, module_path: Option<&PathBuf>) -> Output {
    let repo = repo_root();
    assert_no_daemon(&repo);

    let mut command = Command::new(env!("CARGO_BIN_EXE_sable"));
    command
        .current_dir(repo)
        .env("LEAN_NUM_THREADS", "0")
        .env("LEAN_IMPORT_WORKERS", "1")
        .arg("check");
    if let Some(module_path) = module_path {
        command.arg("-M").arg(module_path);
    }
    command
        .arg(path)
        .output()
        .expect("run Sable proof-ingress witness")
}

fn check_source(label: &str, source: &str) -> Output {
    let source = temp_source(label, source);
    check_path(&source.0, None)
}

fn artifact_stem(source: &Path) -> String {
    let stem: String = source
        .file_stem()
        .expect("proof-ingress source has a file stem")
        .to_string_lossy()
        .chars()
        .map(|character| {
            if character.is_ascii_alphanumeric() {
                character
            } else {
                '_'
            }
        })
        .collect();
    if stem
        .chars()
        .next()
        .is_some_and(|character| character.is_ascii_digit())
    {
        format!("m{stem}")
    } else {
        stem
    }
}

fn final_artifacts_for(source: &Path) -> BTreeSet<PathBuf> {
    let directory = repo_root().join(".sable-out/modules");
    let prefix = format!("{}_", artifact_stem(source));
    let entries = match fs::read_dir(&directory) {
        Ok(entries) => entries,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return BTreeSet::new(),
        Err(error) => panic!("cannot inspect {}: {error}", directory.display()),
    };
    entries
        .map(|entry| entry.expect("read generated artifact entry").path())
        .filter(|path| {
            let Some(name) = path.file_name().and_then(|name| name.to_str()) else {
                return false;
            };
            name.starts_with(&prefix) && (name.ends_with(".ok") || name.ends_with(".olean"))
        })
        .collect()
}

fn assert_no_new_final_artifacts(source: &Path, before: &BTreeSet<PathBuf>, context: &str) {
    let after = final_artifacts_for(source);
    assert_eq!(
        &after, before,
        "{context} published a final `.ok` or `.olean`: {after:#?}"
    );
}

fn assert_failed_closed(output: Output, context: &str) {
    let stdout = String::from_utf8(output.stdout).expect("Sable stdout is UTF-8");
    let stderr = String::from_utf8(output.stderr).expect("Sable stderr is UTF-8");
    assert!(
        !output.status.success(),
        "{context} unexpectedly passed:\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("Lean emitted an unrecognized `warning` diagnostic"),
        "{context} did not surface the stable warning gate:\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("declaration uses `sorry`"),
        "{context} did not retain Lean's `sorry` evidence:\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(!stdout.contains("status:"));
    assert!(!stdout.contains("fully verified"));
    assert!(!stderr.contains("fully verified"));
}

#[test]
fn emit_only_reports_generated_only_assurance() {
    let source = temp_source(
        "emit-only",
        r#"
/// post result = 0
fn subject() -> u64 {
    return 0;
}
"#,
    );
    let options = Options {
        emit_lean_only: true,
        ..Options::default()
    };
    let (_, result) = check_file_structured(&source.0, &options);
    let info = result.expect("emit-only source should pass the front end");
    assert_eq!(info.proof_assurance, ProofAssurance::GeneratedOnly);
    assert_eq!(
        info.proof_assurance.status_line(false, false),
        "status: Lean generated only; proof not checked"
    );
}

#[test]
fn clean_source_reports_the_exact_provisional_status() {
    let source = temp_source(
        "clean-policy-stamp",
        r#"
/// post result = 0
fn subject() -> u64 {
    return 0;
}
"#,
    );
    let before = final_artifacts_for(&source.0);
    let output = check_path(&source.0, None);
    let stdout = String::from_utf8(output.stdout).expect("Sable stdout is UTF-8");
    let stderr = String::from_utf8(output.stderr).expect("Sable stderr is UTF-8");
    assert!(
        output.status.success(),
        "clean source did not pass Lean:\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let statuses: Vec<&str> = stdout
        .lines()
        .filter(|line| line.starts_with("status:"))
        .collect();
    assert_eq!(statuses, [UNAUDITED_PROOF_STATUS]);
    assert!(!stdout.contains("fully verified"));
    assert!(!stderr.contains("fully verified"));
    let published = final_artifacts_for(&source.0)
        .difference(&before)
        .cloned()
        .collect::<Vec<_>>();
    assert_eq!(published.len(), 1, "{published:#?}");
    assert_eq!(
        published[0].extension().and_then(|value| value.to_str()),
        Some("ok")
    );
    assert_eq!(
        fs::read(&published[0]).expect("read root verification stamp"),
        b"sable-verification-policy:reject-unrecognized-lean-warnings-v2\n"
    );
}

#[test]
fn root_sorry_fails_closed_before_artifact_stamping() {
    let source = temp_source(
        "root-sorry-no-final-artifact",
        r#"
/// post result = 1
fn subject() -> u64 {
    return 0;
}

/// discharge subject.post.result_1 by
///   sorry
"#,
    );
    let before = final_artifacts_for(&source.0);
    assert_failed_closed(check_path(&source.0, None), "root `sorry` witness");
    assert_no_new_final_artifacts(&source.0, &before, "root `sorry` witness");
}

#[test]
fn root_admit_fails_closed_before_artifact_stamping() {
    let source = temp_source(
        "root-admit-no-final-artifact",
        r#"
/// post result = 1
fn subject() -> u64 {
    return 0;
}

/// discharge subject.post.result_1 by
///   admit
"#,
    );
    let before = final_artifacts_for(&source.0);
    assert_failed_closed(check_path(&source.0, None), "root `admit` witness");
    assert_no_new_final_artifacts(&source.0, &before, "root `admit` witness");
}

#[test]
fn direct_sorry_ax_fails_closed_before_artifact_stamping() {
    assert_failed_closed(
        check_source(
            "direct-sorry-ax",
            r#"
/// theorem fabricated : False := sorryAx False true

/// post result = 1
fn subject() -> u64 {
    return 0;
}

/// discharge subject.post.result_1 by
///   exact False.elim fabricated
"#,
        ),
        "direct `sorryAx` witness",
    );
}

#[test]
fn imported_sorry_fails_closed_on_fresh_and_repeated_checks() {
    let tree = temp_module_tree("imported-sorry", &[]);
    let dependency_module = tree
        .0
        .file_name()
        .expect("temporary module tree has a name")
        .to_string_lossy()
        .chars()
        .map(|character| {
            if character.is_ascii_alphanumeric() {
                character
            } else {
                '_'
            }
        })
        .collect::<String>();
    let dependency = tree.0.join(format!("{dependency_module}.sable"));
    fs::write(
        &dependency,
        r#"
/// post result = 1
pub fn poisoned() -> u64 {
    return 0;
}

/// discharge poisoned.post.result_1 by
///   sorry
"#,
    )
    .expect("write imported `sorry` dependency");
    let root = tree.0.join("root.sable");
    fs::write(
        &root,
        format!(
            r#"
use {dependency_module};

fn root() {{
}}
"#,
        ),
    )
    .expect("write imported `sorry` root");
    let before = final_artifacts_for(&dependency);
    for attempt in ["fresh", "repeated"] {
        assert_failed_closed(
            check_path(&root, Some(&tree.0)),
            &format!("{attempt} imported `sorry` witness"),
        );
        assert_no_new_final_artifacts(
            &dependency,
            &before,
            &format!("{attempt} imported `sorry` witness"),
        );
    }
}

#[test]
fn unreported_axiom_remains_accepted_only_at_the_provisional_boundary() {
    let output = check_source(
        "injected-axiom",
        r#"
/// theorem harmless : True := by exact True.intro
/// axiom fabricated : False

/// post result = 1
fn subject() -> u64 {
    return 0;
}

/// discharge subject.post.result_1 by
///   exact False.elim fabricated
"#,
    );
    let stdout = String::from_utf8(output.stdout).expect("Sable stdout is UTF-8");
    let stderr = String::from_utf8(output.stderr).expect("Sable stderr is UTF-8");
    assert!(
        output.status.success(),
        "the next-tranche axiom witness changed behavior unexpectedly:\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(!stdout.contains("fully verified"));
    assert!(!stderr.contains("fully verified"));
    let statuses: Vec<&str> = stdout
        .lines()
        .filter(|line| line.starts_with("status:"))
        .collect();
    assert_eq!(statuses, [UNAUDITED_PROOF_STATUS]);
}

#[test]
fn option_suppressed_sorry_ax_remains_only_provisional_until_envelope_audit() {
    let output = check_source(
        "suppressed-sorry-ax",
        r#"
/// theorem harmless : True := by exact True.intro
/// set_option warn.sorry false in theorem fabricated : False := sorryAx False false

/// post result = 1
fn subject() -> u64 {
    return 0;
}

/// discharge subject.post.result_1 by
///   exact False.elim fabricated
"#,
    );
    let stdout = String::from_utf8(output.stdout).expect("Sable stdout is UTF-8");
    let stderr = String::from_utf8(output.stderr).expect("Sable stderr is UTF-8");
    assert!(
        output.status.success(),
        "the warning-suppressed next-tranche witness changed behavior unexpectedly:\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(!stdout.contains("fully verified"));
    assert!(!stderr.contains("fully verified"));
    let statuses: Vec<&str> = stdout
        .lines()
        .filter(|line| line.starts_with("status:"))
        .collect();
    assert_eq!(statuses, [UNAUDITED_PROOF_STATUS]);
}
