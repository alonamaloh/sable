use std::path::{Path, PathBuf};
use std::process::Command;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("compiler crate lives under the repository root")
        .to_path_buf()
}

#[test]
fn doctor_reports_the_pinned_toolchain_and_checkout() {
    let pin = std::fs::read_to_string(repo_root().join("lean/lean-toolchain"))
        .expect("read the repository's Lean pin");
    let pin = pin.trim();
    let output = Command::new(env!("CARGO_BIN_EXE_sable"))
        .arg("doctor")
        .current_dir(repo_root())
        .output()
        .expect("run sable doctor");

    assert!(
        output.status.success(),
        "doctor failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).expect("doctor output is UTF-8");
    assert!(
        stdout.contains(pin),
        "doctor output omitted exact Lean pin `{pin}`:\n{stdout}"
    );
    for required in [
        "Sable doctor",
        "ok      checkout",
        "ok      Cargo",
        "ok      Lake",
        "ok      Lean",
        "hosted runtime",
        "ready: verification",
    ] {
        assert!(
            stdout.contains(required),
            "doctor output omitted `{required}`:\n{stdout}"
        );
    }
}

#[test]
fn doctor_rejects_a_file_argument() {
    let output = Command::new(env!("CARGO_BIN_EXE_sable"))
        .args(["doctor", "program.sable"])
        .current_dir(repo_root())
        .output()
        .expect("run sable doctor with a file");
    assert_eq!(output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&output.stderr).contains("takes no file"));
}

#[test]
fn doctor_rejects_an_unused_module_path() {
    let output = Command::new(env!("CARGO_BIN_EXE_sable"))
        .args(["doctor", "-M", "/definitely/not/a/module/path"])
        .current_dir(repo_root())
        .output()
        .expect("run sable doctor with a module path");
    assert_eq!(output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&output.stderr).contains("`-M` is not valid"));
}
