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
             i32 6, label %sub_overflow\n\
             i32 7, label %mul_overflow\n\
             i32 8, label %neg_overflow\n\
             i32 9, label %option_none\n\
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
         sub_overflow:\n\
           %sub_result = call i8 @__sable_v0_f_9_sub_guard__p_u8_u8__r_u8(i8 0, i8 1)\n\
           ret i32 0\n\
         mul_overflow:\n\
           %mul_result = call i16 @__sable_v0_f_9_mul_guard__p_i16_i16__r_i16(i16 32767, i16 2)\n\
           ret i32 0\n\
         neg_overflow:\n\
           %neg_result = call i64 @__sable_v0_f_9_neg_guard__p_i64__r_i64(i64 -9223372036854775808)\n\
           ret i32 0\n\
         option_none:\n\
           %option_result = call i1 @__sable_v0_f_18_option_value_guard__p_b__r_b(i1 0)\n\
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
            label: "subtract overflow",
            arguments: &["subtract", "overflow", "from", "unsigned", "byte"],
            kind: 2,
            type_info: 65_793, // u8 | (u8 << 8) | (u8 << 16)
            lhs_bits: 0,
            rhs_bits: 1,
        },
        TrapCase {
            label: "multiply overflow",
            arguments: &[
                "multiply", "overflow", "signed", "sixteen", "bit", "integer",
            ],
            kind: 3,
            type_info: 394_758, // i16 | (i16 << 8) | (i16 << 16)
            lhs_bits: 32_767,
            rhs_bits: 2,
        },
        TrapCase {
            label: "negation overflow",
            arguments: &[
                "negation", "overflow", "signed", "sixty", "four", "bit", "integer",
            ],
            kind: 4,
            type_info: 2_056, // i64 | (i64 << 8), with no rhs type
            lhs_bits: 9_223_372_036_854_775_808,
            rhs_bits: 0,
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
        TrapCase {
            label: "option value of none",
            arguments: &[
                "option", "value", "of", "none", "must", "trap", "kind", "eight",
            ],
            kind: 8,
            type_info: 0,
            lhs_bits: 0,
            rhs_bits: 0,
        },
    ];
    assert_clang_traps("trap-abi", &ir, &cases);
}

#[test]
fn boolean_arrays_use_versioned_host_hooks_and_pin_lifetime_and_traps() {
    let source = repo_root().join("corpus/llvm-diff/bool_arrays.sable");
    let output = build_command()
        .args(["build", "--emit-llvm", "-o", "-"])
        .arg(&source)
        .output()
        .expect("run the Sable Boolean-array LLVM build command");
    assert!(
        output.status.success(),
        "LLVM Boolean-array build failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let ir = String::from_utf8(output.stdout).expect("LLVM IR is UTF-8");
    let report = String::from_utf8(output.stderr).expect("verification report is UTF-8");
    assert!(report.contains("status: fully verified"));
    assert!(!ir.contains("define i32 @main("));
    assert!(ir.contains("@__sable_rt_array_alloc_v1"));
    assert!(ir.contains("@__sable_rt_array_free_v1"));

    // Whole-module mode leaves the Sable functions internal. Injecting the
    // test-only main into the same LLVM module lets it violate their verified
    // preconditions without publishing an array ABI. The strong C hooks then
    // expose allocation/free traffic and deliberately fail the 13-byte case.
    let ir = format!(
        "{ir}\n\
         define i32 @main(i32 %argc, ptr %argv) {{\n\
         entry:\n\
           switch i32 %argc, label %unexpected [\n\
             i32 1, label %normal\n\
             i32 2, label %oom\n\
             i32 3, label %load_oob\n\
             i32 4, label %store_oob\n\
           ]\n\
         normal:\n\
           %normal_result = call i32 @__sable_v0_f_17_bool_arrays_entry__p___r_i32()\n\
           ret i32 %normal_result\n\
         oom:\n\
           %oom_result = call i64 @__sable_v0_f_22_bool_array_alloc_guard__p_u64__r_u64(i64 13)\n\
           ret i32 0\n\
         load_oob:\n\
           %load_result = call i1 @__sable_v0_f_21_bool_array_load_guard__p_u64__r_b(i64 7)\n\
           ret i32 0\n\
         store_oob:\n\
           %store_result = call i1 @__sable_v0_f_22_bool_array_store_guard__p_u64__r_b(i64 9)\n\
           ret i32 0\n\
         unexpected:\n\
           ret i32 99\n\
         }}\n"
    );

    assert_clang_array_runtime("bool-arrays", &ir);
}

#[test]
fn affine_options_use_atomic_take_and_conditional_native_cleanup() {
    let source = repo_root().join("corpus/llvm-diff/affine_options.sable");
    let output = build_command()
        .args(["build", "--emit-llvm", "-o", "-"])
        .arg(&source)
        .output()
        .expect("run the Sable affine-option LLVM build command");
    assert!(
        output.status.success(),
        "LLVM affine-option build failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let ir = String::from_utf8(output.stdout).expect("LLVM IR is UTF-8");
    let report = String::from_utf8(output.stderr).expect("verification report is UTF-8");
    assert!(report.contains("status: fully verified"));
    assert!(!ir.contains("define i32 @main("));
    assert!(ir.contains("%sable.option.array.bool = type { i8, %sable.array.bool }"));
    assert!(ir.contains("@__sable_rt_array_alloc_v1"));
    assert!(ir.contains("@__sable_rt_array_free_v1"));
    assert!(ir.contains("@__sable_rt_trap_v1"));

    // Discover internal symbols from their source-name component. This keeps
    // the test independent of the private signature-code spelling while the
    // injected main still calls the scalar-only helpers in the same module.
    let entry = internal_function_symbol(&ir, "affine_options_entry");
    let present = internal_function_symbol(&ir, "affine_option_present_drop");
    let take = internal_function_symbol(&ir, "affine_option_take_drop");
    let none = internal_function_symbol(&ir, "affine_option_none_drop");
    let zero = internal_function_symbol(&ir, "affine_option_zero_drop");
    let reverse = internal_function_symbol(&ir, "affine_option_reverse_cleanup");
    let branch = internal_function_symbol(&ir, "affine_option_branch_cleanup");
    let loop_cleanup = internal_function_symbol(&ir, "affine_option_loop_cleanup");
    let unsafe_cleanup = internal_function_symbol(&ir, "affine_option_unsafe_cleanup");
    let early_return = internal_function_symbol(&ir, "affine_option_early_return");
    let take_none = internal_function_symbol(&ir, "affine_option_take_none_guard");
    let alloc_guard = internal_function_symbol(&ir, "affine_option_alloc_guard");

    let ir = format!(
        "{ir}\n\
         define i32 @main(i32 %argc, ptr %argv) {{\n\
         entry:\n\
           switch i32 %argc, label %unexpected [\n\
             i32 1, label %all\n\
             i32 2, label %present\n\
             i32 3, label %take\n\
             i32 4, label %none\n\
             i32 5, label %zero\n\
             i32 6, label %reverse\n\
             i32 7, label %branch_true\n\
             i32 8, label %branch_false\n\
             i32 9, label %loop_cleanup\n\
             i32 10, label %unsafe_cleanup\n\
             i32 11, label %early_return\n\
             i32 12, label %take_none\n\
             i32 13, label %oom\n\
           ]\n\
         all:\n\
           %all_result = call i32 @{entry}()\n\
           ret i32 %all_result\n\
         present:\n\
           %present_result = call i1 @{present}()\n\
           %present_status = select i1 %present_result, i32 42, i32 1\n\
           ret i32 %present_status\n\
         take:\n\
           %take_result = call i1 @{take}()\n\
           %take_status = select i1 %take_result, i32 42, i32 1\n\
           ret i32 %take_status\n\
         none:\n\
           %none_result = call i1 @{none}()\n\
           %none_status = select i1 %none_result, i32 42, i32 1\n\
           ret i32 %none_status\n\
         zero:\n\
           %zero_result = call i1 @{zero}()\n\
           %zero_status = select i1 %zero_result, i32 42, i32 1\n\
           ret i32 %zero_status\n\
         reverse:\n\
           %reverse_result = call i1 @{reverse}()\n\
           %reverse_status = select i1 %reverse_result, i32 42, i32 1\n\
           ret i32 %reverse_status\n\
         branch_true:\n\
           %branch_true_result = call i1 @{branch}(i1 1)\n\
           %branch_true_status = select i1 %branch_true_result, i32 42, i32 1\n\
           ret i32 %branch_true_status\n\
         branch_false:\n\
           %branch_false_result = call i1 @{branch}(i1 0)\n\
           %branch_false_status = select i1 %branch_false_result, i32 42, i32 1\n\
           ret i32 %branch_false_status\n\
         loop_cleanup:\n\
           %loop_result = call i1 @{loop_cleanup}()\n\
           %loop_status = select i1 %loop_result, i32 42, i32 1\n\
           ret i32 %loop_status\n\
         unsafe_cleanup:\n\
           %unsafe_result = call i1 @{unsafe_cleanup}()\n\
           %unsafe_status = select i1 %unsafe_result, i32 42, i32 1\n\
           ret i32 %unsafe_status\n\
         early_return:\n\
           %early_result = call i1 @{early_return}()\n\
           %early_status = select i1 %early_result, i32 42, i32 1\n\
           ret i32 %early_status\n\
         take_none:\n\
           %take_none_result = call i1 @{take_none}()\n\
           ret i32 0\n\
         oom:\n\
           %oom_result = call i1 @{alloc_guard}(i64 13)\n\
           ret i32 0\n\
         unexpected:\n\
           ret i32 99\n\
         }}\n"
    );

    assert_clang_affine_option_runtime("affine-options", &ir);
}

#[test]
fn borrowed_boolean_arrays_pass_a_descriptor_and_never_own_it() {
    let source = repo_root().join("corpus/llvm-diff/bool_array_borrows.sable");
    let output = build_command()
        .args(["build", "--emit-llvm", "-o", "-"])
        .arg(&source)
        .output()
        .expect("run the Sable borrowed-Boolean-array LLVM build command");
    assert!(
        output.status.success(),
        "LLVM borrowed-Boolean-array build failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let ir = String::from_utf8(output.stdout).expect("LLVM IR is UTF-8");
    let report = String::from_utf8(output.stderr).expect("verification report is UTF-8");
    assert!(report.contains("status: fully verified"));
    assert!(!ir.contains("define i32 @main("));
    // An owner and a borrow share one descriptor; the borrow adds no type.
    assert!(ir.contains("%sable.array.bool = type { ptr, i64 }"));
    assert!(!ir.contains(" inbounds "));

    let entry = internal_function_symbol(&ir, "bool_array_borrows_entry");
    let shared = internal_function_symbol(&ir, "bool_shared_count");
    let unique = internal_function_symbol(&ir, "bool_set");
    let load_guard = internal_function_symbol(&ir, "bool_borrow_load_guard");
    let store_guard = internal_function_symbol(&ir, "bool_borrow_store_guard");
    // Mangling is mutability-sensitive even though the IR type is not, so the
    // two borrow forms are two entry points. The component spelling is
    // internal and versionable, like the named type.
    assert!(shared.contains("__p_abs__"), "shared borrow code: {shared}");
    assert!(
        unique.contains("__p_abm_u64__"),
        "unique borrow code: {unique}"
    );
    assert!(ir.contains(&format!("call i64 @{shared}(%sable.array.bool ")));
    assert!(ir.contains(&format!("call i1 @{unique}(%sable.array.bool ")));

    // No function that only borrows may reach the free hook: an owner frees,
    // and every borrowed descriptor is a copy of one the caller still owns.
    for borrowing in [
        "bool_shared_count",
        "bool_set",
        "bool_clear",
        "bool_count_if",
        "bool_set_first_two",
        "read_through_borrow",
        "write_through_borrow",
    ] {
        let symbol = internal_function_symbol(&ir, borrowing);
        let body = internal_function_body(&ir, &symbol);
        assert!(
            !body.contains("__sable_rt_array_free_v1"),
            "`{borrowing}` borrows its array but reaches the free hook"
        );
    }

    // The injected main calls only scalar-signature helpers, so it neither
    // publishes nor reconstructs the internal borrowed-array convention.
    let ir = format!(
        "{ir}\n\
         define i32 @main(i32 %argc, ptr %argv) {{\n\
         entry:\n\
           switch i32 %argc, label %unexpected [\n\
             i32 1, label %normal\n\
             i32 2, label %load_oob\n\
             i32 3, label %store_oob\n\
           ]\n\
         normal:\n\
           %normal_result = call i32 @{entry}()\n\
           ret i32 %normal_result\n\
         load_oob:\n\
           %load_result = call i1 @{load_guard}(i64 7)\n\
           ret i32 0\n\
         store_oob:\n\
           %store_result = call i1 @{store_guard}(i64 9)\n\
           ret i32 0\n\
         unexpected:\n\
           ret i32 99\n\
         }}\n"
    );

    assert_clang_bool_array_borrow_runtime("bool-array-borrows", &ir);
}

#[test]
fn u32_arrays_use_byte_hooks_unaligned_access_and_nonowning_internal_borrows() {
    let source = repo_root().join("corpus/llvm-diff/u32_arrays.sable");
    let output = build_command()
        .args(["build", "--emit-llvm", "-o", "-"])
        .arg(&source)
        .output()
        .expect("run the Sable u32-array LLVM build command");
    assert!(
        output.status.success(),
        "LLVM u32-array build failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let ir = String::from_utf8(output.stdout).expect("LLVM IR is UTF-8");
    let report = String::from_utf8(output.stderr).expect("verification report is UTF-8");
    assert!(report.contains("status: fully verified"));
    assert!(!ir.contains("define i32 @main("));
    assert!(ir.contains("%sable.array.u32 = type { ptr, i64 }"));
    assert!(ir.contains("@__sable_rt_array_alloc_v1"));
    assert!(ir.contains("@__sable_rt_array_free_v1"));
    assert!(ir.contains("@__sable_rt_trap_v1"));
    assert!(
        ir.lines()
            .any(|line| line.contains("load i32, ptr") && line.contains(", align 1")),
        "the v1 byte-allocation hook does not promise u32 alignment"
    );
    assert!(
        ir.lines().any(|line| {
            line.contains("store i32 ") && line.contains(", ptr ") && line.contains(", align 1")
        }),
        "u32 element stores must use explicit align 1"
    );
    assert!(!ir.contains(" inbounds "));

    // Borrow calls stay internal and non-owning. Discover every symbol from
    // the private mangle rather than pinning an array signature as an ABI.
    let entry = internal_function_symbol(&ir, "u32_arrays_entry");
    let shared = internal_function_symbol(&ir, "u32_shared_sum");
    let mutate = internal_function_symbol(&ir, "u32_mutate");
    let zero = internal_function_symbol(&ir, "u32_array_zero");
    let branch = internal_function_symbol(&ir, "u32_array_branch_cleanup");
    let loop_cleanup = internal_function_symbol(&ir, "u32_array_loop_cleanup");
    let early_return = internal_function_symbol(&ir, "u32_array_early_return");
    let alloc_guard = internal_function_symbol(&ir, "u32_array_alloc_guard");
    let load_guard = internal_function_symbol(&ir, "u32_array_load_guard");
    let store_guard = internal_function_symbol(&ir, "u32_array_store_guard");
    assert!(ir.contains(&format!("call i64 @{shared}(")));
    assert!(ir.contains(&format!("call i1 @{mutate}(")));

    // The injected main calls only scalar-signature helpers. It does not
    // publish or reconstruct the internal borrowed-array convention.
    let ir = format!(
        "{ir}\n\
         define i32 @main(i32 %argc, ptr %argv) {{\n\
         entry:\n\
           switch i32 %argc, label %unexpected [\n\
             i32 1, label %all\n\
             i32 2, label %zero\n\
             i32 3, label %branch_true\n\
             i32 4, label %branch_false\n\
             i32 5, label %loop_cleanup\n\
             i32 6, label %early_return\n\
             i32 7, label %oom\n\
             i32 8, label %over_cap\n\
             i32 9, label %load_oob\n\
             i32 10, label %store_oob\n\
           ]\n\
         all:\n\
           %all_result = call i32 @{entry}()\n\
           ret i32 %all_result\n\
         zero:\n\
           %zero_result = call i1 @{zero}()\n\
           %zero_status = select i1 %zero_result, i32 42, i32 1\n\
           ret i32 %zero_status\n\
         branch_true:\n\
           %branch_true_result = call i1 @{branch}(i1 1)\n\
           %branch_true_status = select i1 %branch_true_result, i32 42, i32 1\n\
           ret i32 %branch_true_status\n\
         branch_false:\n\
           %branch_false_result = call i1 @{branch}(i1 0)\n\
           %branch_false_status = select i1 %branch_false_result, i32 42, i32 1\n\
           ret i32 %branch_false_status\n\
         loop_cleanup:\n\
           %loop_result = call i1 @{loop_cleanup}()\n\
           %loop_status = select i1 %loop_result, i32 42, i32 1\n\
           ret i32 %loop_status\n\
         early_return:\n\
           %early_result = call i1 @{early_return}()\n\
           %early_status = select i1 %early_result, i32 42, i32 1\n\
           ret i32 %early_status\n\
         oom:\n\
           %oom_result = call i64 @{alloc_guard}(i64 13)\n\
           ret i32 0\n\
         over_cap:\n\
           %over_cap_result = call i64 @{alloc_guard}(i64 50000001)\n\
           ret i32 0\n\
         load_oob:\n\
           %load_result = call i32 @{load_guard}(i64 7)\n\
           ret i32 0\n\
         store_oob:\n\
           %store_result = call i32 @{store_guard}(i64 9)\n\
           ret i32 0\n\
         unexpected:\n\
           ret i32 99\n\
         }}\n"
    );

    assert_clang_u32_array_runtime("u32-arrays", &ir);
}

#[test]
fn integer_native_balances_nested_array_ownership_at_o0_and_o2() {
    let source = repo_root().join("corpus/verifies/integer_native.sable");
    let output = build_command()
        .args([
            "build",
            "--emit-llvm",
            "--entry",
            "integer_native_entry",
            "-o",
            "-",
        ])
        .arg(&source)
        .output()
        .expect("run the Sable Integer LLVM build command");
    assert!(
        output.status.success(),
        "LLVM Integer build failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let ir = String::from_utf8(output.stdout).expect("LLVM IR is UTF-8");
    let report = String::from_utf8(output.stderr).expect("verification report is UTF-8");
    assert!(report.contains("status: fully verified"));
    assert!(ir.contains("define i32 @main()"));
    assert!(ir.contains("@__sable_rt_array_alloc_v1"));
    assert!(ir.contains("@__sable_rt_array_free_v1"));

    assert_clang_integer_lifetime("integer-native-lifetime", &ir);
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

fn assert_clang_array_runtime(label: &str, ir: &str) {
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
    let hook_path = temp.join("array-hooks.c");
    fs::write(&ir_path, ir).expect("write emitted Boolean-array IR fixture");
    fs::write(
        &hook_path,
        br#"#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

void *__sable_rt_array_alloc_v1(uint64_t bytes) {
    fprintf(stderr, "SABLE_ARRAY_ALLOC_V1 bytes=%" PRIu64 "\n", bytes);
    fflush(stderr);
    if (bytes == 13 || bytes > SIZE_MAX) {
        return NULL;
    }
    return malloc((size_t)bytes);
}

void __sable_rt_array_free_v1(void *storage) {
    fprintf(stderr, "SABLE_ARRAY_FREE_V1\n");
    fflush(stderr);
    free(storage);
}

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
    .expect("write strong Boolean-array runtime hooks");

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
            .expect("run clang over emitted Boolean-array IR and replacement hooks");
        assert!(
            compile.status.success(),
            "clang {optimization} rejected Boolean-array fixture:\n{}",
            String::from_utf8_lossy(&compile.stderr)
        );

        let normal = Command::new(&executable)
            .output()
            .expect("run the compiled normal Boolean-array case");
        assert_eq!(
            normal.status.code(),
            Some(42),
            "normal Boolean-array case diverged at {optimization}:\n{}",
            String::from_utf8_lossy(&normal.stderr)
        );
        let normal_stderr = String::from_utf8_lossy(&normal.stderr);
        assert_eq!(normal_stderr.matches("SABLE_ARRAY_ALLOC_V1").count(), 7);
        assert_eq!(normal_stderr.matches("SABLE_ARRAY_FREE_V1").count(), 7);
        assert!(normal_stderr.contains("SABLE_ARRAY_ALLOC_V1 bytes=4"));
        assert!(normal_stderr.contains("SABLE_ARRAY_ALLOC_V1 bytes=3"));
        assert!(normal_stderr.contains("SABLE_ARRAY_ALLOC_V1 bytes=5"));
        assert_eq!(
            normal_stderr
                .matches("SABLE_ARRAY_ALLOC_V1 bytes=6")
                .count(),
            2
        );
        assert!(normal_stderr.contains("SABLE_ARRAY_ALLOC_V1 bytes=7"));
        assert!(normal_stderr.contains("SABLE_ARRAY_ALLOC_V1 bytes=8"));
        assert!(
            !normal_stderr.contains("bytes=0"),
            "zero-length arrays must use the allocation-free representation"
        );

        for (arguments, expected_trap, expected_allocation) in [
            (
                &["oom"][..],
                "SABLE_TRAP_V1 kind=9 type_info=0 lhs=13 rhs=0",
                "SABLE_ARRAY_ALLOC_V1 bytes=13",
            ),
            (
                &["load", "oob"][..],
                "SABLE_TRAP_V1 kind=10 type_info=0 lhs=7 rhs=2",
                "SABLE_ARRAY_ALLOC_V1 bytes=2",
            ),
            (
                &["store", "oob", "case"][..],
                "SABLE_TRAP_V1 kind=10 type_info=0 lhs=9 rhs=2",
                "SABLE_ARRAY_ALLOC_V1 bytes=2",
            ),
        ] {
            let trapped = Command::new(&executable)
                .args(arguments)
                .output()
                .expect("run a compiled Boolean-array trap case");
            assert!(
                !trapped.status.success(),
                "Boolean-array trap hook returned at {optimization}; llvm.trap must terminate"
            );
            let stderr = String::from_utf8_lossy(&trapped.stderr);
            assert!(
                stderr.contains(expected_trap),
                "wrong Boolean-array trap at {optimization} (status {}):\n{stderr}",
                trapped.status
            );
            assert_eq!(stderr.matches("SABLE_ARRAY_ALLOC_V1").count(), 1);
            assert!(stderr.contains(expected_allocation));
            assert_eq!(
                stderr.matches("SABLE_ARRAY_FREE_V1").count(),
                0,
                "trap edges do not unwind owned arrays"
            );
        }
    }
    fs::remove_dir_all(&temp).expect("remove isolated LLVM Boolean-array test directory");
}

fn assert_clang_affine_option_runtime(label: &str, ir: &str) {
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
    let hook_path = temp.join("affine-option-hooks.c");
    fs::write(&ir_path, ir).expect("write emitted affine-option IR fixture");
    fs::write(
        &hook_path,
        br#"#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

typedef struct {
    void *storage;
    uint64_t bytes;
} SableAllocation;

static SableAllocation live_allocations[64];
static size_t live_count = 0;

void *__sable_rt_array_alloc_v1(uint64_t bytes) {
    fprintf(stderr, "SABLE_ARRAY_ALLOC_V1 bytes=%" PRIu64 "\n", bytes);
    fflush(stderr);
    if (bytes == 13 || bytes > SIZE_MAX) {
        return NULL;
    }
    void *storage = malloc((size_t)bytes);
    if (storage != NULL) {
        if (live_count == 64) {
            abort();
        }
        live_allocations[live_count].storage = storage;
        live_allocations[live_count].bytes = bytes;
        live_count += 1;
    }
    return storage;
}

void __sable_rt_array_free_v1(void *storage) {
    uint64_t bytes = UINT64_MAX;
    for (size_t i = 0; i < live_count; i += 1) {
        if (live_allocations[i].storage == storage) {
            bytes = live_allocations[i].bytes;
            live_count -= 1;
            live_allocations[i] = live_allocations[live_count];
            break;
        }
    }
    fprintf(stderr, "SABLE_ARRAY_FREE_V1 bytes=%" PRIu64 "\n", bytes);
    fflush(stderr);
    free(storage);
}

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
    .expect("write strong affine-option runtime hooks");

    let cases: &[(&str, usize, &[&str])] = &[
        (
            "all",
            1,
            &[
                "SABLE_ARRAY_ALLOC_V1 bytes=1",
                "SABLE_ARRAY_FREE_V1 bytes=1",
                "SABLE_ARRAY_ALLOC_V1 bytes=2",
                "SABLE_ARRAY_FREE_V1 bytes=2",
                "SABLE_ARRAY_ALLOC_V1 bytes=8",
                "SABLE_ARRAY_ALLOC_V1 bytes=9",
                "SABLE_ARRAY_FREE_V1 bytes=9",
                "SABLE_ARRAY_FREE_V1 bytes=8",
                "SABLE_ARRAY_ALLOC_V1 bytes=3",
                "SABLE_ARRAY_ALLOC_V1 bytes=11",
                "SABLE_ARRAY_FREE_V1 bytes=11",
                "SABLE_ARRAY_FREE_V1 bytes=3",
                "SABLE_ARRAY_ALLOC_V1 bytes=4",
                "SABLE_ARRAY_ALLOC_V1 bytes=12",
                "SABLE_ARRAY_FREE_V1 bytes=12",
                "SABLE_ARRAY_FREE_V1 bytes=4",
                "SABLE_ARRAY_ALLOC_V1 bytes=5",
                "SABLE_ARRAY_ALLOC_V1 bytes=11",
                "SABLE_ARRAY_FREE_V1 bytes=11",
                "SABLE_ARRAY_FREE_V1 bytes=5",
                "SABLE_ARRAY_ALLOC_V1 bytes=5",
                "SABLE_ARRAY_ALLOC_V1 bytes=11",
                "SABLE_ARRAY_FREE_V1 bytes=11",
                "SABLE_ARRAY_FREE_V1 bytes=5",
                "SABLE_ARRAY_ALLOC_V1 bytes=6",
                "SABLE_ARRAY_ALLOC_V1 bytes=10",
                "SABLE_ARRAY_FREE_V1 bytes=10",
                "SABLE_ARRAY_FREE_V1 bytes=6",
                "SABLE_ARRAY_ALLOC_V1 bytes=7",
                "SABLE_ARRAY_FREE_V1 bytes=7",
            ],
        ),
        (
            "present option drops its payload",
            2,
            &[
                "SABLE_ARRAY_ALLOC_V1 bytes=1",
                "SABLE_ARRAY_FREE_V1 bytes=1",
            ],
        ),
        (
            "taken source is empty and destination drops",
            3,
            &[
                "SABLE_ARRAY_ALLOC_V1 bytes=2",
                "SABLE_ARRAY_FREE_V1 bytes=2",
            ],
        ),
        ("none option has no payload", 4, &[]),
        ("zero payload is allocation-free", 5, &[]),
        (
            "reverse declaration cleanup",
            6,
            &[
                "SABLE_ARRAY_ALLOC_V1 bytes=8",
                "SABLE_ARRAY_ALLOC_V1 bytes=9",
                "SABLE_ARRAY_FREE_V1 bytes=9",
                "SABLE_ARRAY_FREE_V1 bytes=8",
            ],
        ),
        (
            "true branch cleanup",
            7,
            &[
                "SABLE_ARRAY_ALLOC_V1 bytes=3",
                "SABLE_ARRAY_ALLOC_V1 bytes=11",
                "SABLE_ARRAY_FREE_V1 bytes=11",
                "SABLE_ARRAY_FREE_V1 bytes=3",
            ],
        ),
        (
            "false branch cleanup",
            8,
            &[
                "SABLE_ARRAY_ALLOC_V1 bytes=4",
                "SABLE_ARRAY_ALLOC_V1 bytes=12",
                "SABLE_ARRAY_FREE_V1 bytes=12",
                "SABLE_ARRAY_FREE_V1 bytes=4",
            ],
        ),
        (
            "loop iteration cleanup",
            9,
            &[
                "SABLE_ARRAY_ALLOC_V1 bytes=5",
                "SABLE_ARRAY_ALLOC_V1 bytes=11",
                "SABLE_ARRAY_FREE_V1 bytes=11",
                "SABLE_ARRAY_FREE_V1 bytes=5",
                "SABLE_ARRAY_ALLOC_V1 bytes=5",
                "SABLE_ARRAY_ALLOC_V1 bytes=11",
                "SABLE_ARRAY_FREE_V1 bytes=11",
                "SABLE_ARRAY_FREE_V1 bytes=5",
            ],
        ),
        (
            "unsafe open-scope cleanup",
            10,
            &[
                "SABLE_ARRAY_ALLOC_V1 bytes=6",
                "SABLE_ARRAY_ALLOC_V1 bytes=10",
                "SABLE_ARRAY_FREE_V1 bytes=10",
                "SABLE_ARRAY_FREE_V1 bytes=6",
            ],
        ),
        (
            "early return cleanup",
            11,
            &[
                "SABLE_ARRAY_ALLOC_V1 bytes=7",
                "SABLE_ARRAY_FREE_V1 bytes=7",
            ],
        ),
    ];

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
            .expect("run clang over emitted affine-option IR and replacement hooks");
        assert!(
            compile.status.success(),
            "clang {optimization} rejected affine-option fixture:\n{}",
            String::from_utf8_lossy(&compile.stderr)
        );

        for (case, argc, expected_events) in cases {
            let output = Command::new(&executable)
                .args((1..*argc).map(|_| "case"))
                .output()
                .expect("run a compiled affine-option lifetime case");
            assert_eq!(
                output.status.code(),
                Some(42),
                "{case} diverged at {optimization}:\n{}",
                String::from_utf8_lossy(&output.stderr)
            );
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert_eq!(
                stderr.lines().collect::<Vec<_>>(),
                expected_events.to_vec(),
                "wrong {case} hook order at {optimization}"
            );
        }

        let absent = Command::new(&executable)
            .args((1..12).map(|_| "take-none"))
            .output()
            .expect("run an absent affine-option take");
        assert!(
            !absent.status.success(),
            "absent take returned after its trap hook at {optimization}"
        );
        let absent_stderr = String::from_utf8_lossy(&absent.stderr);
        assert!(absent_stderr.contains("SABLE_TRAP_V1 kind=8 type_info=0 lhs=0 rhs=0"));
        assert_eq!(absent_stderr.matches("SABLE_ARRAY_ALLOC_V1").count(), 0);
        assert_eq!(absent_stderr.matches("SABLE_ARRAY_FREE_V1").count(), 0);

        let oom = Command::new(&executable)
            .args((1..13).map(|_| "oom"))
            .output()
            .expect("run a forced affine-option allocation failure");
        assert!(
            !oom.status.success(),
            "affine-option OOM returned after its trap hook at {optimization}"
        );
        let oom_stderr = String::from_utf8_lossy(&oom.stderr);
        assert!(oom_stderr.contains("SABLE_ARRAY_ALLOC_V1 bytes=13"));
        assert!(oom_stderr.contains("SABLE_TRAP_V1 kind=9 type_info=0 lhs=13 rhs=0"));
        assert_eq!(oom_stderr.matches("SABLE_ARRAY_ALLOC_V1").count(), 1);
        assert_eq!(oom_stderr.matches("SABLE_ARRAY_FREE_V1").count(), 0);
        let allocation = oom_stderr
            .find("SABLE_ARRAY_ALLOC_V1 bytes=13")
            .expect("forced OOM calls the allocation hook");
        let trap = oom_stderr
            .find("SABLE_TRAP_V1 kind=9")
            .expect("forced OOM reports trap kind 9");
        assert!(
            allocation < trap,
            "the failed allocation precedes its OOM trap"
        );
    }
    fs::remove_dir_all(&temp).expect("remove isolated LLVM affine-option test directory");
}

/// Run the borrowed-Boolean-array fixture against strong hooks that track
/// every live allocation, so a free the emitter should not have emitted —
/// a callee freeing storage it only borrowed — aborts instead of passing.
fn assert_clang_bool_array_borrow_runtime(label: &str, ir: &str) {
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
    let hook_path = temp.join("bool-array-borrow-hooks.c");
    fs::write(&ir_path, ir).expect("write emitted borrowed-Boolean-array IR fixture");
    fs::write(
        &hook_path,
        br#"#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static void *live_allocations[64];
static size_t live_count = 0;

void *__sable_rt_array_alloc_v1(uint64_t bytes) {
    fprintf(stderr, "SABLE_ARRAY_ALLOC_V1 bytes=%" PRIu64 "\n", bytes);
    fflush(stderr);
    if (bytes > SIZE_MAX) {
        return NULL;
    }
    void *storage = malloc((size_t)bytes);
    if (storage == NULL || live_count == 64) {
        abort();
    }
    live_allocations[live_count] = storage;
    live_count += 1;
    return storage;
}

void __sable_rt_array_free_v1(void *storage) {
    fprintf(stderr, "SABLE_ARRAY_FREE_V1\n");
    fflush(stderr);
    for (size_t i = 0; i < live_count; i += 1) {
        if (live_allocations[i] == storage) {
            live_count -= 1;
            live_allocations[i] = live_allocations[live_count];
            free(storage);
            return;
        }
    }
    // Either a double free or storage this scope only borrowed.
    abort();
}

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
    .expect("write strong borrowed-Boolean-array runtime hooks");

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
            .expect("run clang over emitted borrowed-Boolean-array IR");
        assert!(
            compile.status.success(),
            "clang {optimization} rejected the borrowed-Boolean-array fixture:\n{}",
            String::from_utf8_lossy(&compile.stderr)
        );

        let normal = Command::new(&executable)
            .output()
            .expect("run the compiled normal borrowed-Boolean-array case");
        assert_eq!(
            normal.status.code(),
            Some(42),
            "borrowed-Boolean-array case diverged at {optimization}:\n{}",
            String::from_utf8_lossy(&normal.stderr)
        );
        let stderr = String::from_utf8_lossy(&normal.stderr);
        // The entry owns two nonempty arrays and lends them repeatedly; the
        // empty one keeps the allocation-free representation.
        assert_eq!(stderr.matches("SABLE_ARRAY_ALLOC_V1").count(), 2);
        assert_eq!(stderr.matches("SABLE_ARRAY_FREE_V1").count(), 2);
        assert!(stderr.contains("SABLE_ARRAY_ALLOC_V1 bytes=4"));
        assert!(stderr.contains("SABLE_ARRAY_ALLOC_V1 bytes=3"));
        assert!(
            !stderr.contains("bytes=0"),
            "a zero-length array uses the allocation-free representation"
        );

        for (arguments, expected_trap) in [
            (
                &["load-oob"][..],
                "SABLE_TRAP_V1 kind=10 type_info=0 lhs=7 rhs=2",
            ),
            (
                &["store-oob", "case"][..],
                "SABLE_TRAP_V1 kind=10 type_info=0 lhs=9 rhs=2",
            ),
        ] {
            let trapped = Command::new(&executable)
                .args(arguments)
                .output()
                .expect("run a compiled borrowed-Boolean-array trap case");
            assert!(
                !trapped.status.success(),
                "the trap hook returned at {optimization}; llvm.trap must terminate"
            );
            let stderr = String::from_utf8_lossy(&trapped.stderr);
            assert!(
                stderr.contains(expected_trap),
                "wrong bounds trap through a borrow at {optimization} (status {}):\n{stderr}",
                trapped.status
            );
            assert_eq!(
                stderr.matches("SABLE_ARRAY_FREE_V1").count(),
                0,
                "trap edges do not unwind owned arrays"
            );
        }
    }
    fs::remove_dir_all(&temp).expect("remove isolated borrowed-Boolean-array test directory");
}

fn assert_clang_u32_array_runtime(label: &str, ir: &str) {
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
    let hook_path = temp.join("u32-array-hooks.c");
    fs::write(&ir_path, ir).expect("write emitted u32-array IR fixture");
    fs::write(
        &hook_path,
        br#"#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
    void *storage;
    uint64_t bytes;
} SableAllocation;

static SableAllocation live_allocations[64];
static size_t live_count = 0;

void *__sable_rt_array_alloc_v1(uint64_t bytes) {
    fprintf(stderr, "SABLE_ARRAY_ALLOC_V1 bytes=%" PRIu64 "\n", bytes);
    fflush(stderr);
    if (bytes == 52 || bytes > SIZE_MAX - 1) {
        return NULL;
    }
    unsigned char *base = malloc((size_t)bytes + 1);
    if (base == NULL) {
        return NULL;
    }
    // Deliberately return a byte-aligned address. N0 must not strengthen the
    // v1 hook into a native-u32-alignment promise.
    void *storage = base + 1;
    if (live_count == 64) {
        abort();
    }
    live_allocations[live_count].storage = storage;
    live_allocations[live_count].bytes = bytes;
    live_count += 1;
    memset(storage, 0, (size_t)bytes);
    return storage;
}

void __sable_rt_array_free_v1(void *storage) {
    uint64_t bytes = UINT64_MAX;
    for (size_t i = 0; i < live_count; i += 1) {
        if (live_allocations[i].storage == storage) {
            bytes = live_allocations[i].bytes;
            live_count -= 1;
            live_allocations[i] = live_allocations[live_count];
            break;
        }
    }
    fprintf(stderr, "SABLE_ARRAY_FREE_V1 bytes=%" PRIu64 "\n", bytes);
    fflush(stderr);
    if (bytes == UINT64_MAX) {
        abort();
    }
    free((unsigned char *)storage - 1);
}

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
    .expect("write strong u32-array runtime hooks");

    let cases: &[(&str, usize, &[&str])] = &[
        (
            "all",
            1,
            &[
                "SABLE_ARRAY_ALLOC_V1 bytes=16",
                "SABLE_ARRAY_ALLOC_V1 bytes=12",
                "SABLE_ARRAY_ALLOC_V1 bytes=20",
                "SABLE_ARRAY_ALLOC_V1 bytes=28",
                "SABLE_ARRAY_FREE_V1 bytes=28",
                "SABLE_ARRAY_FREE_V1 bytes=20",
                "SABLE_ARRAY_ALLOC_V1 bytes=24",
                "SABLE_ARRAY_ALLOC_V1 bytes=32",
                "SABLE_ARRAY_FREE_V1 bytes=32",
                "SABLE_ARRAY_FREE_V1 bytes=24",
                "SABLE_ARRAY_ALLOC_V1 bytes=36",
                "SABLE_ARRAY_FREE_V1 bytes=36",
                "SABLE_ARRAY_ALLOC_V1 bytes=36",
                "SABLE_ARRAY_FREE_V1 bytes=36",
                "SABLE_ARRAY_ALLOC_V1 bytes=40",
                "SABLE_ARRAY_FREE_V1 bytes=40",
                "SABLE_ARRAY_FREE_V1 bytes=12",
                "SABLE_ARRAY_FREE_V1 bytes=16",
            ],
        ),
        ("zero-length bypass", 2, &[]),
        (
            "true branch reverse cleanup",
            3,
            &[
                "SABLE_ARRAY_ALLOC_V1 bytes=20",
                "SABLE_ARRAY_ALLOC_V1 bytes=28",
                "SABLE_ARRAY_FREE_V1 bytes=28",
                "SABLE_ARRAY_FREE_V1 bytes=20",
            ],
        ),
        (
            "false branch reverse cleanup",
            4,
            &[
                "SABLE_ARRAY_ALLOC_V1 bytes=24",
                "SABLE_ARRAY_ALLOC_V1 bytes=32",
                "SABLE_ARRAY_FREE_V1 bytes=32",
                "SABLE_ARRAY_FREE_V1 bytes=24",
            ],
        ),
        (
            "loop iteration cleanup",
            5,
            &[
                "SABLE_ARRAY_ALLOC_V1 bytes=36",
                "SABLE_ARRAY_FREE_V1 bytes=36",
                "SABLE_ARRAY_ALLOC_V1 bytes=36",
                "SABLE_ARRAY_FREE_V1 bytes=36",
            ],
        ),
        (
            "early return cleanup",
            6,
            &[
                "SABLE_ARRAY_ALLOC_V1 bytes=40",
                "SABLE_ARRAY_FREE_V1 bytes=40",
            ],
        ),
    ];

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
            .expect("run clang over emitted u32-array IR and replacement hooks");
        assert!(
            compile.status.success(),
            "clang {optimization} rejected u32-array fixture:\n{}",
            String::from_utf8_lossy(&compile.stderr)
        );

        for (case, argc, expected_events) in cases {
            let output = Command::new(&executable)
                .args((1..*argc).map(|_| "case"))
                .output()
                .expect("run a compiled u32-array lifetime case");
            assert_eq!(
                output.status.code(),
                Some(42),
                "{case} diverged at {optimization}:\n{}",
                String::from_utf8_lossy(&output.stderr)
            );
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert_eq!(
                stderr.lines().collect::<Vec<_>>(),
                expected_events.to_vec(),
                "wrong {case} hook order at {optimization}"
            );
        }

        for (argc, expected_trap, expected_allocation) in [
            (
                7,
                "SABLE_TRAP_V1 kind=9 type_info=0 lhs=13 rhs=0",
                Some("SABLE_ARRAY_ALLOC_V1 bytes=52"),
            ),
            (
                8,
                "SABLE_TRAP_V1 kind=9 type_info=0 lhs=50000001 rhs=0",
                None,
            ),
            (
                9,
                "SABLE_TRAP_V1 kind=10 type_info=0 lhs=7 rhs=2",
                Some("SABLE_ARRAY_ALLOC_V1 bytes=8"),
            ),
            (
                10,
                "SABLE_TRAP_V1 kind=10 type_info=0 lhs=9 rhs=2",
                Some("SABLE_ARRAY_ALLOC_V1 bytes=8"),
            ),
        ] {
            let trapped = Command::new(&executable)
                .args((1..argc).map(|_| "trap"))
                .output()
                .expect("run a compiled u32-array trap case");
            assert!(
                !trapped.status.success(),
                "u32-array trap hook returned at {optimization}; llvm.trap must terminate"
            );
            let stderr = String::from_utf8_lossy(&trapped.stderr);
            assert!(
                stderr.contains(expected_trap),
                "wrong u32-array trap at {optimization} (status {}):\n{stderr}",
                trapped.status
            );
            assert_eq!(
                stderr.matches("SABLE_ARRAY_FREE_V1").count(),
                0,
                "trap edges do not unwind owned u32 arrays"
            );
            match expected_allocation {
                Some(allocation) => {
                    assert_eq!(stderr.matches("SABLE_ARRAY_ALLOC_V1").count(), 1);
                    assert!(stderr.contains(allocation));
                    let allocation = stderr
                        .find(allocation)
                        .expect("expected allocation event is present");
                    let trap = stderr
                        .find("SABLE_TRAP_V1")
                        .expect("expected trap event is present");
                    assert!(allocation < trap, "allocation precedes its trap");
                }
                None => assert_eq!(
                    stderr.matches("SABLE_ARRAY_ALLOC_V1").count(),
                    0,
                    "profile-cap rejection precedes the allocation hook"
                ),
            }
        }
    }
    fs::remove_dir_all(&temp).expect("remove isolated LLVM u32-array test directory");
}

fn assert_clang_integer_lifetime(label: &str, ir: &str) {
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
    let hook_path = temp.join("integer-lifetime-hooks.c");
    fs::write(&ir_path, ir).expect("write emitted Integer IR fixture");
    fs::write(
        &hook_path,
        br#"#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
    void *storage;
    unsigned char *base;
    uint64_t bytes;
} SableAllocation;

static SableAllocation live_allocations[4096];
static size_t live_count = 0;
static int exit_check_registered = 0;

static void check_balanced_at_exit(void) {
    if (live_count != 0) {
        fprintf(stderr, "SABLE_ARRAY_LIFETIME_V1 live=%zu\n", live_count);
        fflush(stderr);
        abort();
    }
    fprintf(stderr, "SABLE_ARRAY_LIFETIME_V1 live=0\n");
    fflush(stderr);
}

void *__sable_rt_array_alloc_v1(uint64_t bytes) {
    if (!exit_check_registered) {
        if (atexit(check_balanced_at_exit) != 0) {
            abort();
        }
        exit_check_registered = 1;
    }
    if (bytes > SIZE_MAX - 1 || live_count == 4096) {
        return NULL;
    }
    unsigned char *base = malloc((size_t)bytes + 1);
    if (base == NULL) {
        return NULL;
    }

    // Return a deliberately unaligned address so nested Nat cleanup cannot
    // accidentally rely on stronger alignment than the byte-hook ABI gives.
    void *storage = base + 1;
    live_allocations[live_count].storage = storage;
    live_allocations[live_count].base = base;
    live_allocations[live_count].bytes = bytes;
    live_count += 1;
    memset(storage, 0, (size_t)bytes);
    return storage;
}

void __sable_rt_array_free_v1(void *storage) {
    for (size_t i = 0; i < live_count; i += 1) {
        if (live_allocations[i].storage == storage) {
            unsigned char *base = live_allocations[i].base;
            uint64_t bytes = live_allocations[i].bytes;
            live_count -= 1;
            live_allocations[i] = live_allocations[live_count];
            memset(storage, 0xa5, (size_t)bytes);
            free(base);
            return;
        }
    }

    // A second free is unknown after the first removal, so both invalid and
    // duplicate frees fail through the same strict ownership check.
    fprintf(stderr, "SABLE_ARRAY_LIFETIME_V1 unknown-free=%p\n", storage);
    fflush(stderr);
    abort();
}
"#,
    )
    .expect("write strong Integer lifetime hooks");

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
            .expect("run clang over emitted Integer IR and lifetime hooks");
        assert!(
            compile.status.success(),
            "clang {optimization} rejected Integer lifetime fixture:\n{}",
            String::from_utf8_lossy(&compile.stderr)
        );

        let output = Command::new(&executable)
            .output()
            .expect("run the compiled Integer lifetime case");
        assert_eq!(
            output.status.code(),
            Some(42),
            "Integer lifetime case diverged at {optimization}:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(
            String::from_utf8_lossy(&output.stderr)
                .lines()
                .any(|line| line == "SABLE_ARRAY_LIFETIME_V1 live=0"),
            "Integer ownership did not reach a balanced exit at {optimization}:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    fs::remove_dir_all(&temp).expect("remove isolated LLVM Integer test directory");
}

fn internal_function_symbol(ir: &str, source_name: &str) -> String {
    let marker = format!("_{source_name}__p_");
    let definition = ir
        .lines()
        .find(|line| line.starts_with("define internal ") && line.contains(&marker))
        .unwrap_or_else(|| panic!("missing emitted definition for `{source_name}`"));
    let after_at = definition
        .split_once('@')
        .map(|(_, suffix)| suffix)
        .expect("internal definition has a symbol");
    after_at
        .split_once('(')
        .map(|(symbol, _)| symbol.to_owned())
        .expect("internal definition has a parameter list")
}

/// The emitted lines of one internal definition, from `define` to its `}`.
fn internal_function_body(ir: &str, symbol: &str) -> String {
    let opening = format!("@{symbol}(");
    let mut lines = ir
        .lines()
        .skip_while(|line| !(line.starts_with("define internal ") && line.contains(&opening)));
    let mut body = String::new();
    for line in lines.by_ref() {
        body.push_str(line);
        body.push('\n');
        if line == "}" {
            return body;
        }
    }
    panic!("missing emitted body for `{symbol}`")
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
