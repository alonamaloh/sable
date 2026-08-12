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

    assert_clang_exit("scalar", &ir, 42);
}

#[test]
fn verified_control_flow_and_short_circuit_run_at_o0_and_o2() {
    let source = repo_root().join("corpus/llvm-diff/control_flow.sable");
    let output = build_command()
        .args([
            "build",
            "--emit-llvm",
            "--entry",
            "control_entry",
            "-o",
            "-",
        ])
        .arg(&source)
        .output()
        .expect("run the Sable control-flow LLVM build command");
    assert!(
        output.status.success(),
        "LLVM CFG build failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let ir = String::from_utf8(output.stdout).expect("LLVM IR is UTF-8");
    assert!(ir.contains("while.head"));
    assert!(ir.contains("phi i1 [ 0,"));
    assert!(ir.contains("phi i1 [ 1,"));
    assert!(ir.contains("icmp ugt i32"));

    let control = ir
        .find("define internal i32 @__sable_v0_f_13_control_entry")
        .map(|start| &ir[start..])
        .expect("control entry is emitted");
    let rhs_block = control
        .find(".sc.rhs:\n")
        .expect("short-circuit RHS has its own block");
    let rhs_call = control[rhs_block..]
        .find("call i1 @__sable_v0_f_15_unreachable_rhs")
        .expect("the syntactic RHS call is inside the conditional RHS block");
    let rhs_merge = control[rhs_block..]
        .find(".sc.end:\n")
        .expect("short-circuit RHS rejoins at a merge block");
    assert!(rhs_call < rhs_merge);
    assert_clang_exit("control", &ir, 42);
}

#[test]
fn verified_checked_arithmetic_and_euclidean_conversions_run_at_o0_and_o2() {
    let source = repo_root().join("corpus/llvm-diff/arithmetic.sable");
    let output = build_command()
        .args([
            "build",
            "--emit-llvm",
            "--entry",
            "arithmetic_entry",
            "-o",
            "-",
        ])
        .arg(&source)
        .output()
        .expect("run the Sable arithmetic LLVM build command");
    assert!(
        output.status.success(),
        "LLVM arithmetic build failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let ir = String::from_utf8(output.stdout).expect("LLVM IR is UTF-8");
    assert!(ir.contains("@llvm.sadd.with.overflow.i8"));
    assert!(ir.contains("@llvm.usub.with.overflow.i8"));
    assert!(ir.contains("@llvm.smul.with.overflow.i16"));
    assert!(ir.contains("@__sable_rt_trap_v1"));
    assert!(ir.contains("@__sable_rt_fail_v1"));
    assert!(ir.contains("sdiv i32"));
    assert!(ir.contains("srem i32"));
    assert!(ir.contains("sext i16"));
    assert!(ir.contains("trunc i128"));
    for forbidden in [" nsw ", " nuw ", " exact ", " inbounds ", "llvm.assume"] {
        assert!(!ir.contains(forbidden), "forbidden LLVM token: {forbidden}");
    }
    assert_clang_exit("arithmetic", &ir, 42);
}

#[test]
fn versioned_trap_hook_observes_raw_payloads_and_cannot_suppress_failure() {
    let source = repo_root().join("corpus/llvm-diff/trap_abi.sable");
    let output = build_command()
        .args(["build", "--emit-llvm", "-o", "-"])
        .arg(&source)
        .output()
        .expect("run the Sable trap-ABI LLVM build command");
    assert!(
        output.status.success(),
        "LLVM trap-ABI build failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let ir = String::from_utf8(output.stdout).expect("LLVM IR is UTF-8");
    let report = String::from_utf8(output.stderr).expect("verification report is UTF-8");
    assert!(report.contains("status: fully verified"));
    assert!(!ir.contains("define i32 @main("));

    // Whole-module mode emits these functions without a process entry.  The
    // test-only main calls them with values that violate their Sable-level
    // preconditions.  That makes otherwise unreachable backend guards
    // executable without weakening verification or admitting an assumption.
    let ir = format!(
        "{ir}\n\
         define i32 @main(i32 %argc, ptr %argv) {{\n\
         entry:\n\
           switch i32 %argc, label %unexpected [\n\
             i32 2, label %add_overflow\n\
             i32 3, label %division_by_zero\n\
             i32 4, label %signed_division_overflow\n\
             i32 5, label %narrow_range\n\
           ]\n\
         add_overflow:\n\
           %add_result = call i8 @__sable_v0_f_9_add_guard__p_i8_i8__r_i8(i8 127, i8 1)\n\
           ret i32 0\n\
         division_by_zero:\n\
           %zero_result = call i32 @__sable_v0_f_9_div_guard__p_i32_i32__r_i32(i32 7, i32 0)\n\
           ret i32 0\n\
         signed_division_overflow:\n\
           %div_result = call i32 @__sable_v0_f_9_div_guard__p_i32_i32__r_i32(i32 -2147483648, i32 -1)\n\
           ret i32 0\n\
         narrow_range:\n\
           %narrow_result = call i8 @__sable_v0_f_12_narrow_guard__p_i32__r_i8(i32 300)\n\
           ret i32 0\n\
         unexpected:\n\
           ret i32 99\n\
         }}\n"
    );

    let cases = [
        TrapCase {
            label: "add overflow",
            arguments: &["add"],
            kind: 1,
            type_info: 328_965, // i8 | (i8 << 8) | (i8 << 16)
            lhs_bits: 127,
            rhs_bits: 1,
        },
        TrapCase {
            label: "division by zero",
            arguments: &["division", "zero"],
            kind: 5,
            type_info: 460_551, // i32 | (i32 << 8) | (i32 << 16)
            lhs_bits: 7,
            rhs_bits: 0,
        },
        TrapCase {
            label: "signed division overflow",
            arguments: &["signed", "division", "overflow"],
            kind: 6,
            type_info: 460_551,
            // Signed values are exposed as zero-extended source-width bits.
            lhs_bits: 2_147_483_648,
            rhs_bits: 4_294_967_295,
        },
        TrapCase {
            label: "narrow range",
            arguments: &["narrow", "range", "outside", "target"],
            kind: 7,
            type_info: 1_797, // destination i8 | (source i32 << 8)
            lhs_bits: 300,
            rhs_bits: 0,
        },
    ];
    assert_clang_traps("trap-abi", &ir, &cases);
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

struct TrapCase {
    label: &'static str,
    arguments: &'static [&'static str],
    kind: u32,
    type_info: u32,
    lhs_bits: u64,
    rhs_bits: u64,
}

fn assert_clang_traps(label: &str, ir: &str, cases: &[TrapCase]) {
    let Some(clang) = find_clang() else {
        assert_ne!(
            std::env::var("SABLE_REQUIRE_CLANG").as_deref(),
            Ok("1"),
            "SABLE_REQUIRE_CLANG=1 but no clang executable was found"
        );
        return;
    };
    let temp = temp_dir(label);
    let ir_path = temp.join(format!("{label}.ll"));
    let hook_path = temp.join("trap-hook.c");
    fs::write(&ir_path, ir).expect("write emitted trap IR fixture");
    fs::write(
        &hook_path,
        br#"#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>

void __sable_rt_trap_v1(
    int32_t kind,
    int32_t type_info,
    uint64_t lhs_bits,
    uint64_t rhs_bits
) {
    fprintf(
        stderr,
        "SABLE_TRAP_V1 kind=%" PRId32 " type_info=%" PRIu32
        " lhs=%" PRIu64 " rhs=%" PRIu64 "\n",
        kind,
        (uint32_t)type_info,
        lhs_bits,
        rhs_bits
    );
    fflush(stderr);
}
"#,
    )
    .expect("write strong trap hook");

    for optimization in ["-O0", "-O2"] {
        let executable = temp.join(format!("{label}-{}", &optimization[1..]));
        let compile = Command::new(&clang)
            .args([optimization, "-x", "ir"])
            .arg(&ir_path)
            .args(["-x", "c"])
            .arg(&hook_path)
            .arg("-o")
            .arg(&executable)
            .output()
            .expect("run clang over emitted trap IR and replacement hook");
        assert!(
            compile.status.success(),
            "clang {optimization} rejected trap-ABI fixture:\n{}",
            String::from_utf8_lossy(&compile.stderr)
        );

        for case in cases {
            let output = Command::new(&executable)
                .args(case.arguments)
                .output()
                .expect("run a compiled LLVM trap case");
            assert!(
                !output.status.success(),
                "{} {optimization} returned after the replacement hook; llvm.trap must terminate",
                case.label
            );
            let stderr = String::from_utf8_lossy(&output.stderr);
            let expected = format!(
                "SABLE_TRAP_V1 kind={} type_info={} lhs={} rhs={}",
                case.kind, case.type_info, case.lhs_bits, case.rhs_bits
            );
            assert!(
                stderr.contains(&expected),
                "wrong {} {optimization} trap payload (status {}):\n{stderr}",
                case.label,
                output.status
            );
        }
    }
    fs::remove_dir_all(&temp).expect("remove isolated LLVM trap test directory");
}

fn assert_clang_exit(label: &str, ir: &str, expected: i32) {
    let Some(clang) = find_clang() else {
        assert_ne!(
            std::env::var("SABLE_REQUIRE_CLANG").as_deref(),
            Ok("1"),
            "SABLE_REQUIRE_CLANG=1 but no clang executable was found"
        );
        return;
    };
    let temp = temp_dir(label);
    let ir_path = temp.join(format!("{label}.ll"));
    fs::write(&ir_path, ir).expect("write emitted IR fixture");
    for optimization in ["-O0", "-O2"] {
        let executable = temp.join(format!("{label}-{}", &optimization[1..]));
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
            .expect("run the compiled LLVM entry");
        assert_eq!(
            status.code(),
            Some(expected),
            "wrong {label} {optimization} result"
        );
    }
    fs::remove_dir_all(&temp).expect("remove isolated LLVM test directory");
}

fn command_works(path: &Path) -> bool {
    Command::new(path)
        .arg("--version")
        .output()
        .is_ok_and(|output| output.status.success())
}
