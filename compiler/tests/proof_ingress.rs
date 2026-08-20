use std::fs;
use std::path::PathBuf;
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

fn temp_source(label: &str, source: &str) -> TempSource {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let path = std::env::temp_dir().join(format!(
        "sable-proof-ingress-{label}-{}-{}.sable",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed),
    ));
    fs::write(&path, source).expect("write proof-ingress witness");
    TempSource(path)
}

fn check_source(label: &str, source: &str) -> Output {
    let repo = repo_root();
    let daemon_socket = repo.join(".sable-out/daemon.sock");
    match fs::symlink_metadata(&daemon_socket) {
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => panic!("cannot inspect {}: {error}", daemon_socket.display()),
        Ok(_) => panic!(
            "{} exists; proof-ingress tests require bounded batch Lean",
            daemon_socket.display()
        ),
    }

    let source = temp_source(label, source);

    Command::new(env!("CARGO_BIN_EXE_sable"))
        .current_dir(repo)
        .env("LEAN_NUM_THREADS", "0")
        .env("LEAN_IMPORT_WORKERS", "1")
        .arg("check")
        .arg(&source.0)
        .output()
        .expect("run Sable proof-ingress witness")
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
    let output = check_source(
        "clean",
        r#"
/// post result = 0
fn subject() -> u64 {
    return 0;
}
"#,
    );
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
}

#[test]
fn known_false_proofs_never_receive_the_strongest_status() {
    let witnesses = [
        (
            "sorry",
            r#"
/// post result = 1
fn subject() -> u64 {
    return 0;
}

/// discharge subject.post.result_1 by
///   sorry
"#,
        ),
        (
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
        ),
    ];

    for (label, source) in witnesses {
        let output = check_source(label, source);
        let stdout = String::from_utf8(output.stdout).expect("Sable stdout is UTF-8");
        let stderr = String::from_utf8(output.stderr).expect("Sable stderr is UTF-8");
        assert!(
            output.status.success(),
            "current ingress witness should remain usable only behind the provisional status; \
             a future rejecting tranche must update this regression to require its exact diagnostic:\n\
             stdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(
            !stdout.contains("fully verified") && !stderr.contains("fully verified"),
            "{label} received the forbidden strongest status:\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        let statuses: Vec<&str> = stdout
            .lines()
            .filter(|line| line.starts_with("status:"))
            .collect();
        assert_eq!(
            statuses,
            [UNAUDITED_PROOF_STATUS],
            "accepted {label} witness did not report the exact provisional boundary"
        );
    }
}
