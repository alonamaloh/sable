use std::process::{Command, Output};

fn explain(spelling: &str) -> Output {
    Command::new(env!("CARGO_BIN_EXE_sable"))
        .args(["explain-type", spelling])
        .output()
        .expect("run sable explain-type")
}

#[test]
fn reports_parser_positions_and_all_four_evidence_profiles() {
    let output = explain("option<[bool]>");
    assert!(
        output.status.success(),
        "explain-type failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stderr.is_empty());
    let report = String::from_utf8(output.stdout).expect("report is UTF-8");
    for expected in [
        "type: option<[bool]>",
        "normalized: option<[bool]>",
        "parser type positions — 6/16 lowerings accepted",
        "parser lowering is not full parse→consts→mono→check language admission",
        "parser-accepted: param, return, local, record field, class field, option payload",
        "type.borrow_param_unsupported",
        "verified core (checker + VC generation)",
        "vc.affine_option_position",
        "executable core (interpreter + monitor)",
        "interp.affine_option_position_unsupported",
        "formal-machine core (SVM)",
        "svm.affine_option_unsupported",
        "native core (LLVM)",
        "backend.affine_option_unsupported",
    ] {
        assert!(
            report.contains(expected),
            "explain-type report omitted `{expected}`:\n{report}"
        );
    }
    assert!(!report.contains("source positions"), "{report}");
}

#[test]
fn invalid_spelling_is_a_spanned_named_cli_error() {
    let output = explain("option<[bool]>>");
    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    let error = String::from_utf8(output.stderr).expect("diagnostic is UTF-8");
    for expected in [
        "expected end of type, found `>`",
        "--> <type>:1:15",
        "diagnostic: parse.expected",
    ] {
        assert!(
            error.contains(expected),
            "invalid-type diagnostic omitted `{expected}`:\n{error}"
        );
    }
}

#[test]
fn standalone_nominal_names_fail_without_inventing_module_context() {
    let output = explain("ProjectClass");
    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    let error = String::from_utf8(output.stderr).expect("diagnostic is UTF-8");
    assert!(error.contains("unknown type `ProjectClass`"));
    assert!(error.contains("diagnostic: parse.unknown_type"));
}
