use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("compiler crate lives under the repository root")
        .to_path_buf()
}

fn temp_dir(label: &str) -> PathBuf {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let path = std::env::temp_dir().join(format!(
        "sable-llvm-{label}-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&path).expect("create isolated LLVM test directory");
    path
}

fn build_command() -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_sable"));
    command
        .current_dir(repo_root())
        .env("SABLE_LEAN_JOBS", "1")
        .env("SABLE_TEST_JOBS", "1");
    command
}

#[test]
fn verified_scalar_ir_is_pipe_clean_and_runs_when_clang_exists() {
    let source = repo_root().join("corpus/llvm-diff/scalar_calls.sable");
    let output = build_command()
        .args(["build", "--emit-llvm", "--entry", "scalar_entry", "-o", "-"])
        .arg(&source)
        .output()
        .expect("run the Sable LLVM build command");

    assert!(
        output.status.success(),
        "LLVM build failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let ir = String::from_utf8(output.stdout).expect("LLVM IR is UTF-8");
    let report = String::from_utf8(output.stderr).expect("verification report is UTF-8");
    assert!(ir.starts_with("; Sable textual LLVM IR v0\n"));
    assert!(ir.contains("; Sable artifact: scalar_calls_"));
    assert!(ir.contains("; Sable proof environment: proof-env-v2-fnv64:"));
    assert!(ir.contains("define i32 @main()"));
    assert!(!ir.contains("verified:"), "stdout must remain pipe-clean");
    assert!(report.contains("verified:"));
    assert!(report.contains("status: fully verified"));

    let Some(clang) = find_clang() else {
        assert_ne!(
            std::env::var("SABLE_REQUIRE_CLANG").as_deref(),
            Ok("1"),
            "SABLE_REQUIRE_CLANG=1 but no clang executable was found"
        );
        return;
    };
    let temp = temp_dir("run");
    let ir_path = temp.join("scalar.ll");
    fs::write(&ir_path, ir).expect("write emitted IR fixture");
    for optimization in ["-O0", "-O2"] {
        let executable = temp.join(format!("scalar-{}", &optimization[1..]));
        let compile = Command::new(&clang)
            .args([optimization, "-x", "ir"])
            .arg(&ir_path)
            .arg("-o")
            .arg(&executable)
            .output()
            .expect("run clang over emitted LLVM IR");
        assert!(
            compile.status.success(),
            "clang {optimization} rejected emitted IR:\n{}",
            String::from_utf8_lossy(&compile.stderr)
        );
        let status = Command::new(&executable)
            .status()
            .expect("run the compiled scalar entry");
        assert_eq!(status.code(), Some(42), "wrong {optimization} result");
    }
    fs::remove_dir_all(&temp).expect("remove isolated LLVM test directory");
}

#[test]
fn failed_verification_preserves_an_existing_output() {
    let temp = temp_dir("atomic");
    let destination = temp.join("program.ll");
    fs::write(&destination, b"existing-output\n").expect("seed existing output");
    let source = repo_root().join("corpus/must-fail/assert_unprovable.sable");

    let output = build_command()
        .args(["build", "--emit-llvm", "--entry", "bad", "-o"])
        .arg(&destination)
        .arg(&source)
        .output()
        .expect("run a deliberately failing verified build");
    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("bad.assert.x_10"),
        "unexpected failure:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        fs::read(&destination).expect("read preserved output"),
        b"existing-output\n"
    );
    fs::remove_dir_all(&temp).expect("remove isolated LLVM test directory");
}

#[test]
fn assumed_obligation_is_not_silently_erased() {
    let temp = temp_dir("assumed");
    let destination = temp.join("program.ll");
    fs::write(&destination, b"existing-output\n").expect("seed existing output");
    let source = repo_root().join("corpus/llvm-diff/assumed_escape.sable");

    let output = build_command()
        .args(["build", "--emit-llvm", "--entry", "assumed_entry", "-o"])
        .arg(&destination)
        .arg(&source)
        .output()
        .expect("run a build containing an audited proof escape");
    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("LLVM lowering does not accept assumed obligations"),
        "unexpected failure:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        fs::read(&destination).expect("read preserved output"),
        b"existing-output\n"
    );
    fs::remove_dir_all(&temp).expect("remove isolated LLVM test directory");
}

fn find_clang() -> Option<PathBuf> {
    if let Some(path) = std::env::var_os("SABLE_CLANG") {
        let path = PathBuf::from(path);
        return command_works(&path).then_some(path);
    }
    let homebrew = Path::new("/opt/homebrew/opt/llvm/bin/clang");
    if command_works(homebrew) {
        return Some(homebrew.to_path_buf());
    }
    let path = PathBuf::from("clang");
    command_works(&path).then_some(path)
}

fn command_works(path: &Path) -> bool {
    Command::new(path)
        .arg("--version")
        .output()
        .is_ok_and(|output| output.status.success())
}
