//! Bounded end-to-end differential for the verified LLVM scalar backend.
//!
//! Each subject is verified once, then the exact `VerifiedProgram` capability
//! is consumed by both the tree-walking interpreter and LLVM lowering. Native
//! O0/O2 process outcomes must agree with the interpreter; no expected result
//! is duplicated in this harness.

use sable::interp::RtVal;
use sable::llvm::{EmitOptions, emit_verified};
use sable::{Options, verify_file_structured};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread;

// Verification remains intentionally recursive over proof/control structure.
// Rust's test harness runs each test on a smaller spawned-thread stack than the
// CLI's main thread, which is insufficient for the largest differential cases.
// Give this bounded end-to-end worker the same explicit budget as the corpus
// harness so the test observes compiler behavior rather than harness stack size.
const LLVM_DIFF_WORKER_STACK: usize = 16 * 1024 * 1024;

struct Case {
    label: &'static str,
    source: &'static str,
    entry: &'static str,
}

const CASES: &[Case] = &[
    Case {
        label: "scalar",
        source: "scalar_calls.sable",
        entry: "scalar_entry",
    },
    Case {
        label: "control",
        source: "control_flow.sable",
        entry: "control_entry",
    },
    Case {
        label: "arithmetic",
        source: "arithmetic.sable",
        entry: "arithmetic_entry",
    },
    Case {
        label: "option-bool",
        source: "option_bool.sable",
        entry: "option_entry",
    },
    Case {
        label: "option-bool-params",
        source: "option_param.sable",
        entry: "option_param_entry",
    },
    Case {
        label: "pod-record",
        source: "pod_record.sable",
        entry: "pod_record_entry",
    },
    Case {
        label: "bool-arrays",
        source: "bool_arrays.sable",
        entry: "bool_arrays_entry",
    },
    Case {
        label: "affine-options",
        source: "affine_options.sable",
        entry: "affine_options_entry",
    },
    Case {
        label: "u32-arrays",
        source: "u32_arrays.sable",
        entry: "u32_arrays_entry",
    },
    Case {
        label: "bool-array-borrows",
        source: "bool_array_borrows.sable",
        entry: "bool_array_borrows_entry",
    },
    Case {
        label: "bool-owner-slots",
        source: "slots_bool.sable",
        entry: "slots_bool_entry",
    },
    Case {
        label: "bignum-native",
        source: "../verifies/bignum_native.sable",
        entry: "bignum_native_entry",
    },
    Case {
        label: "bignum-add-native",
        source: "../verifies/bignum_add_native.sable",
        entry: "bignum_add_native_entry",
    },
    Case {
        label: "bignum-sub-mul-native",
        source: "../verifies/bignum_sub_mul_native.sable",
        entry: "bignum_sub_mul_native_entry",
    },
    Case {
        label: "bignum-div-native",
        source: "../verifies/bignum_div_native.sable",
        entry: "bignum_div_native_entry",
    },
    Case {
        label: "integer-native",
        source: "../verifies/integer_native.sable",
        entry: "integer_native_entry",
    },
];

fn repo_root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("compiler crate lives under the repository root")
}

#[test]
fn verified_llvm_matches_the_interpreter_at_o0_and_o2() {
    let result = thread::Builder::new()
        .name("sable-llvm-differential".into())
        .stack_size(LLVM_DIFF_WORKER_STACK)
        .spawn(run_verified_llvm_differential)
        .expect("spawn LLVM differential worker")
        .join();
    if let Err(payload) = result {
        std::panic::resume_unwind(payload);
    }
}

fn run_verified_llvm_differential() {
    let Some(clang) = find_clang() else {
        assert_ne!(
            std::env::var("SABLE_REQUIRE_CLANG").as_deref(),
            Ok("1"),
            "SABLE_REQUIRE_CLANG=1 but no clang executable was found"
        );
        eprintln!("skipping verified LLVM differential: no clang executable found");
        return;
    };

    let temp = temp_dir("diff");
    let hosted_runtime = repo_root().join("runtime/hosted/sable_rt_v1.c");
    let counted_runtime = temp.join("counted_owned_storage_runtime.c");
    fs::write(
        &counted_runtime,
        r#"
#include <stdint.h>
#include <stdlib.h>

static uint64_t live_allocations = 0;
static uint64_t total_allocations = 0;
static uint64_t total_frees = 0;

static void require_balanced_storage(void) {
    if (live_allocations != 0 || total_allocations != 2 || total_frees != 2) {
        _Exit(253);
    }
}

__attribute__((constructor))
static void install_balance_check(void) {
    if (atexit(require_balanced_storage) != 0) {
        _Exit(251);
    }
}

void *__sable_rt_array_alloc_v1(uint64_t bytes) {
    if (bytes > SIZE_MAX) {
        return NULL;
    }
    void *storage = malloc((size_t)bytes);
    if (storage != NULL) {
        live_allocations += 1;
        total_allocations += 1;
    }
    return storage;
}

void __sable_rt_array_free_v1(void *storage) {
    if (storage == NULL) {
        return;
    }
    if (live_allocations == 0) {
        _Exit(252);
    }
    live_allocations -= 1;
    total_frees += 1;
    free(storage);
}
"#,
    )
    .expect("write counted owned-storage differential runtime");
    for case in CASES {
        let source = repo_root().join("corpus/llvm-diff").join(case.source);
        eprintln!("llvm-diff {}: verify", case.label);
        let (mods, verified) = verify_file_structured(&source, &Options::default());
        let verified = verified.unwrap_or_else(|diagnostics| {
            panic!(
                "{} failed verification:\n{}",
                source.display(),
                diagnostics
                    .iter()
                    .map(|diagnostic| mods.render(diagnostic))
                    .collect::<Vec<_>>()
                    .join("\n")
            )
        });

        eprintln!("llvm-diff {}: interpret", case.label);
        let interpreted = sable::interp::run_verified_fn(&verified, &mods, case.entry)
            .unwrap_or_else(|trap| panic!("{} interpreter trapped: {trap}", case.label));
        let expected_status = bounded_process_status(case, interpreted);

        eprintln!("llvm-diff {}: emit", case.label);
        let ir = emit_verified(
            &verified,
            &EmitOptions {
                entry: Some(case.entry.to_owned()),
            },
        )
        .unwrap_or_else(|diagnostics| {
            panic!(
                "{} failed LLVM lowering:\n{}",
                case.label,
                diagnostics
                    .iter()
                    .map(|diagnostic| mods.render(diagnostic))
                    .collect::<Vec<_>>()
                    .join("\n")
            )
        });

        let ir_path = temp.join(format!("{}.ll", case.label));
        fs::write(&ir_path, ir).expect("write emitted differential IR");
        let runtime = if case.label == "bool-owner-slots" {
            &counted_runtime
        } else {
            &hosted_runtime
        };
        for optimization in ["-O0", "-O2"] {
            eprintln!("llvm-diff {}: clang {optimization}", case.label);
            let executable = temp.join(format!("{}-{}", case.label, &optimization[1..]));
            let compile = Command::new(&clang)
                .args([optimization, "-x", "ir"])
                .arg(&ir_path)
                .args(["-x", "c"])
                .arg(runtime)
                .arg("-o")
                .arg(&executable)
                .output()
                .expect("run clang over differential IR");
            assert!(
                compile.status.success(),
                "clang {optimization} rejected {}:\n{}",
                case.label,
                String::from_utf8_lossy(&compile.stderr)
            );

            let native = Command::new(&executable)
                .output()
                .expect("run native differential executable");
            assert_eq!(
                native.status.code(),
                Some(expected_status),
                "{} diverged at {optimization}: interpreter returned {expected_status}, native status was {}\nstdout:\n{}\nstderr:\n{}",
                case.label,
                native.status,
                String::from_utf8_lossy(&native.stdout),
                String::from_utf8_lossy(&native.stderr)
            );
            println!(
                "ok (llvm-diff): {} {optimization} = {expected_status}",
                case.label
            );
        }
    }
    fs::remove_dir_all(&temp).expect("remove isolated LLVM differential directory");
}

fn bounded_process_status(case: &Case, value: RtVal) -> i32 {
    let RtVal::Int(value) = value else {
        panic!(
            "{} returned a non-integer interpreter value; the v0 process bridge requires i32",
            case.label
        );
    };
    let value = i32::try_from(value)
        .unwrap_or_else(|_| panic!("{} returned {value}, outside the i32 entry ABI", case.label));

    // Unix process status preserves only 8 bits. Refuse to silently compare a
    // truncated result: this deliberately bounded corpus uses exact statuses.
    assert!(
        (0..=255).contains(&value),
        "{} returned {value}; LLVM differential process statuses must be in 0..=255",
        case.label
    );
    value
}

fn temp_dir(label: &str) -> PathBuf {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let path = std::env::temp_dir().join(format!(
        "sable-llvm-{label}-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&path).expect("create isolated LLVM differential directory");
    path
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
